/*
 * BenchmarkAdder.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.List;
import org.jacop.fz.Fz2jacop;

/**
 * Adds a new MiniZinc benchmark to the JaCoP benchmark suite. Compiles {@code .mzn} to {@code .fzn}
 * using MiniZinc with the JaCoP solver backend, solves with JaCoP to produce the golden output,
 * categorizes by execution time, generates constraint metadata, and updates {@code list.txt}.
 *
 * <p>Prerequisites: MiniZinc must be installed and JaCoP registered as a solver (see the {@code
 * run-minizinc-jacop} skill in {@code .cursor/skills/run-minizinc-jacop/SKILL.md}).
 *
 * <p>Usage: {@code java org.jacop.BenchmarkAdder model.mzn [data1.dzn data2.dzn ...]}
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class BenchmarkAdder {

  private static final Path FZ_ROOT = Path.of("src/test/fz");

  private static final long TIMEOUT_MS = 3_600_000;
  private static final long MAX_FZN_SIZE_BYTES = 1_250_000;

  record TimeBucket(String dirName, long maxMillis) {}

  static final List<TimeBucket> BUCKETS =
      List.of(
          new TimeBucket("upTo5sec", 5_000),
          new TimeBucket("upTo30sec", 30_000),
          new TimeBucket("upTo1min", 60_000),
          new TimeBucket("upTo5min", 300_000),
          new TimeBucket("upTo10min", 600_000),
          new TimeBucket("upTo1hour", 3_600_000));

  /**
   * Adds one or more benchmark instances from a MiniZinc model.
   *
   * @param mznFile path to the .mzn model
   * @param dznFiles optional data files; each produces a separate benchmark instance
   */
  public void addBenchmark(Path mznFile, List<Path> dznFiles) throws Exception {
    String modelName = stripExtension(mznFile.getFileName().toString());

    if (dznFiles.isEmpty()) {
      Path fznFile = compileMzn(mznFile, null);
      addSingleInstance(fznFile, modelName, modelName, mznFile, null);
    } else {
      for (Path dzn : dznFiles) {
        String dznName = stripExtension(dzn.getFileName().toString());
        Path fznFile = compileMzn(mznFile, dzn);
        addSingleInstance(fznFile, modelName, dznName, mznFile, dzn);
      }
    }
  }

  private void addSingleInstance(
      Path fznFile, String problemName, String instanceName, Path mznFile, Path dznFile)
      throws Exception {

    long fznSize = Files.size(fznFile);
    if (fznSize > MAX_FZN_SIZE_BYTES) {
      System.err.println(
          "Skipping benchmark "
              + fznFile
              + " because .fzn size "
              + fznSize
              + " bytes exceeds limit "
              + MAX_FZN_SIZE_BYTES
              + " bytes.");
      Files.deleteIfExists(fznFile);
      return;
    }

    System.out.println("Solving " + fznFile + " ...");
    long startMs = System.currentTimeMillis();

    ByteArrayOutputStream baos = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    String output;
    try {
      System.setOut(new PrintStream(baos, true, StandardCharsets.UTF_8));
      Fz2jacop fz2jacop = new Fz2jacop();
      fz2jacop.callMain(new String[] {"-t", String.valueOf(TIMEOUT_MS), fznFile.toString()});
    } finally {
      System.setOut(originalOut);
      output = baos.toString(StandardCharsets.UTF_8);
    }

    long elapsedMs = System.currentTimeMillis() - startMs;
    System.out.println("Solved in " + elapsedMs + " ms");

    if (output.contains("=====TIME-OUT=====") || output.contains("=====UNKNOWN=====")) {
      System.err.println("WARNING: Problem timed out or is unknown. Placing in above1hour.");
    }

    String category = categorize(elapsedMs);
    System.out.println("Categorized as: " + category);

    Path targetDir = FZ_ROOT.resolve(category).resolve(problemName);
    Files.createDirectories(targetDir);

    Path targetFzn = targetDir.resolve(instanceName + ".fzn");
    Files.copy(fznFile, targetFzn, StandardCopyOption.REPLACE_EXISTING);

    Path targetOut = targetDir.resolve(instanceName + ".out");
    Files.writeString(targetOut, output, StandardCharsets.UTF_8);

    if (dznFile != null) {
      Path dznFolder = targetDir.resolve("dznFolder");
      Files.createDirectories(dznFolder);
      Files.copy(
          mznFile, dznFolder.resolve(mznFile.getFileName()), StandardCopyOption.REPLACE_EXISTING);
      Files.copy(
          dznFile, dznFolder.resolve(dznFile.getFileName()), StandardCopyOption.REPLACE_EXISTING);
    } else if (mznFile != null) {
      Path dznFolder = targetDir.resolve("dznFolder");
      Files.createDirectories(dznFolder);
      Files.copy(
          mznFile, dznFolder.resolve(mznFile.getFileName()), StandardCopyOption.REPLACE_EXISTING);
    }

    BenchmarkMetadataGenerator generator = new BenchmarkMetadataGenerator();
    generator.generateForFznFile(targetFzn);

    regenerateList(FZ_ROOT.resolve(category));

    Files.deleteIfExists(fznFile);

    System.out.println("Added benchmark: " + category + "/" + problemName + "/" + instanceName);
  }

  String categorize(long elapsedMs) {
    for (TimeBucket bucket : BUCKETS) {
      if (elapsedMs <= bucket.maxMillis) {
        return bucket.dirName;
      }
    }
    return "above1hour";
  }

  private Path compileMzn(Path mznFile, Path dznFile) throws Exception {
    String minizinc = findMinizinc();
    List<String> cmd = new ArrayList<>();
    cmd.add(minizinc);
    cmd.add("--compile");
    cmd.add("--solver");
    cmd.add("org.jacop");
    cmd.add(mznFile.toString());
    if (dznFile != null) {
      cmd.add("-d");
      cmd.add(dznFile.toString());
    }

    System.out.println("Compiling: " + String.join(" ", cmd));
    ProcessBuilder pb = new ProcessBuilder(cmd);
    pb.inheritIO();
    Process process = pb.start();
    int exitCode = process.waitFor();
    if (exitCode != 0) {
      throw new RuntimeException("MiniZinc compilation failed with exit code " + exitCode);
    }

    String baseName =
        dznFile != null
            ? stripExtension(dznFile.getFileName().toString())
            : stripExtension(mznFile.getFileName().toString());
    Path expectedFzn = mznFile.getParent().resolve(baseName + ".fzn");
    if (!Files.exists(expectedFzn)) {
      expectedFzn = Path.of(baseName + ".fzn");
    }
    if (!Files.exists(expectedFzn)) {
      throw new RuntimeException("Expected .fzn file not found after compilation: " + expectedFzn);
    }
    return expectedFzn;
  }

  static void regenerateList(Path categoryDir) throws IOException {
    List<String> entries = new ArrayList<>();
    try (DirectoryStream<Path> problemDirs = Files.newDirectoryStream(categoryDir)) {
      for (Path problemDir : problemDirs) {
        if (!Files.isDirectory(problemDir)) {
          continue;
        }
        try (DirectoryStream<Path> fznFiles = Files.newDirectoryStream(problemDir, "*.fzn")) {
          for (Path fzn : fznFiles) {
            String name = fzn.getFileName().toString();
            String baseName = name.substring(0, name.length() - 4);
            Path outFile = problemDir.resolve(baseName + ".out");
            if (!Files.exists(outFile)) {
              continue;
            }
            String entry = problemDir.getFileName() + "/" + baseName;
            entries.add(entry);
          }
        }
      }
    }
    entries.sort(String::compareTo);
    Path listFile = categoryDir.resolve("list.txt");
    Files.writeString(listFile, String.join("\n", entries) + "\n", StandardCharsets.UTF_8);
  }

  private static String findMinizinc() {
    String[] candidates = {
      "C:\\Program Files\\MiniZinc\\minizinc.exe",
      "C:\\Program Files (x86)\\MiniZinc\\minizinc.exe",
      "/usr/bin/minizinc",
      "/usr/local/bin/minizinc"
    };
    for (String candidate : candidates) {
      if (Files.exists(Path.of(candidate))) {
        return candidate;
      }
    }
    return "minizinc";
  }

  private static String stripExtension(String filename) {
    int dot = filename.lastIndexOf('.');
    return dot > 0 ? filename.substring(0, dot) : filename;
  }

  /**
   * Adds a new MiniZinc benchmark.
   *
   * @param args first argument is the .mzn file, remaining arguments are optional .dzn files
   */
  public static void main(String[] args) throws Exception {
    if (args.length < 1) {
      System.err.println("Usage: BenchmarkAdder <model.mzn> [data1.dzn data2.dzn ...]");
      System.exit(1);
    }
    Path mznFile = Path.of(args[0]);
    List<Path> dznFiles = new ArrayList<>();
    for (int i = 1; i < args.length; i++) {
      dznFiles.add(Path.of(args[i]));
    }
    new BenchmarkAdder().addBenchmark(mznFile, dznFiles);
  }
}
