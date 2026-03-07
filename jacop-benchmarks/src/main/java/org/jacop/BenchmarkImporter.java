/*
 * BenchmarkImporter.java
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
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import org.jacop.fz.Fz2jacop;

/**
 * Batch-imports MiniZinc benchmarks from an external repository into the JaCoP benchmark suite.
 *
 * <p>For each problem directory, it compiles {@code .mzn} files to {@code .fzn} using MiniZinc,
 * solves with JaCoP, verifies determinism across 7 runs, and installs qualifying instances into the
 * appropriate time category ({@code upTo5sec} or {@code upTo30sec}).
 *
 * <p>Rules:
 *
 * <ul>
 *   <li>Instances are processed smallest-first (by {@code .dzn} or {@code .mzn} file size).
 *   <li>At most 5 instances per problem directory per time category.
 *   <li>Instances taking more than 60 seconds on the first run are immediately discarded.
 *   <li>Only instances solving in under 40 seconds are retained.
 *   <li>Each retained instance must produce identical output across 7 runs.
 *   <li>Original directory names from the source repository are preserved.
 * </ul>
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class BenchmarkImporter {

  static final Path FZ_ROOT = Path.of("src/test/fz");
  static final long HARD_TIMEOUT_MS = 60_000;
  static final long UPTO5SEC_MAX_MS = 5_000;
  static final long INCLUSION_MAX_MS = 40_000;
  static final int DETERMINISM_RUNS = 7;
  static final int MAX_INSTANCES_PER_PROBLEM = 5;
  static final int CONSECUTIVE_FAIL_THRESHOLD = 5;
  static final long MAX_FZN_SIZE_BYTES = 1_250_000;

  private Path sourceDir;
  private Path workDir;
  private BenchmarkMetadataGenerator metadataGenerator;

  private int totalAdded = 0;
  private int totalSkippedTimeout = 0;
  private int totalSkippedSlow = 0;
  private int totalSkippedNonDeterministic = 0;
  private int totalSkippedDuplicate = 0;
  private int totalSkippedCompileFail = 0;
  private int totalSkippedCapped = 0;
  private int totalSkippedNoOutput = 0;
  private int totalSkippedTooLarge = 0;

  private Map<String, Map<String, Integer>> problemCategoryCounts = new HashMap<>();
  private Set<String> existingInstancePaths = new HashSet<>();

  /** Creates an uninitialized importer. Call {@link #init(Path)} before use. */
  public BenchmarkImporter() {}

  /**
   * Initializes the importer for benchmarks in the given source directory.
   *
   * @param source path to the external minizinc-benchmarks repository root
   */
  public void init(Path source) throws IOException {
    this.sourceDir = source;
    this.workDir = Path.of("target/import-work");
    Files.createDirectories(workDir);
    this.metadataGenerator = new BenchmarkMetadataGenerator();
    loadExistingBenchmarks();
  }

  /** Imports all eligible benchmarks from the source directory. */
  public void importAll() throws Exception {
    List<Path> problemDirs;
    try (var stream = Files.newDirectoryStream(sourceDir)) {
      problemDirs = new ArrayList<>();
      for (Path p : stream) {
        if (Files.isDirectory(p)) {
          problemDirs.add(p);
        }
      }
    }
    problemDirs.sort(Comparator.comparing(p -> p.getFileName().toString()));

    System.out.println(
        "=== BenchmarkImporter: scanning "
            + problemDirs.size()
            + " problem directories in "
            + sourceDir
            + " ===");

    for (Path problemDir : problemDirs) {
      try {
        importProblemDirectory(problemDir);
      } catch (Exception e) {
        System.err.println("ERROR processing " + problemDir.getFileName() + ": " + e.getMessage());
      }
    }

    System.out.println("\n=== IMPORT COMPLETE ===");
    System.out.println("Added:                    " + totalAdded);
    System.out.println("Skipped (compile fail):   " + totalSkippedCompileFail);
    System.out.println("Skipped (too large fzn):  " + totalSkippedTooLarge);
    System.out.println("Skipped (timeout >60s):   " + totalSkippedTimeout);
    System.out.println("Skipped (slow 40-60s):    " + totalSkippedSlow);
    System.out.println("Skipped (no output):      " + totalSkippedNoOutput);
    System.out.println("Skipped (non-determ.):    " + totalSkippedNonDeterministic);
    System.out.println("Skipped (duplicate):      " + totalSkippedDuplicate);
    System.out.println("Skipped (cap reached):    " + totalSkippedCapped);

    regenerateListFiles();
  }

  private void importProblemDirectory(Path problemDir) throws Exception {
    String problemName = problemDir.getFileName().toString();
    System.out.println("\n--- Processing: " + problemName + " ---");

    List<Path> mznFiles = listFiles(problemDir, "*.mzn");
    List<Path> dznFiles = listFiles(problemDir, "*.dzn");

    if (mznFiles.isEmpty()) {
      System.out.println("  No .mzn files found, skipping.");
      return;
    }

    List<InstanceCandidate> candidates = enumerateInstances(mznFiles, dznFiles);
    System.out.println("  Found " + candidates.size() + " instance candidates");

    int addedForProblem = 0;
    int consecutiveHardFails = 0;
    for (InstanceCandidate candidate : candidates) {
      if (bothCategoriesCapped(problemName)) {
        System.out.println("  Both categories capped for " + problemName + ", moving on.");
        break;
      }
      if (consecutiveHardFails >= CONSECUTIVE_FAIL_THRESHOLD) {
        System.out.println(
            "  "
                + CONSECUTIVE_FAIL_THRESHOLD
                + " consecutive timeouts/failures, skipping remaining instances.");
        break;
      }
      try {
        InstanceResult result = processInstance(candidate, problemName);
        switch (result) {
          case ADDED -> {
            addedForProblem++;
            consecutiveHardFails = 0;
          }
          case TIMEOUT, SLOW, NO_OUTPUT, COMPILE_FAIL -> consecutiveHardFails++;
          case DUPLICATE, CAPPED, NON_DETERMINISTIC, TOO_LARGE -> {
            // benign skips: don't count as consecutive hard failures
          }
          default -> throw new IllegalStateException("Unexpected result: " + result);
        }
      } catch (Exception e) {
        System.err.println(
            "  Error on instance " + candidate.instanceName() + ": " + e.getMessage());
        consecutiveHardFails++;
      }
    }
    System.out.println("  Added " + addedForProblem + " instances from " + problemName);
  }

  enum InstanceResult {
    ADDED,
    COMPILE_FAIL,
    TIMEOUT,
    SLOW,
    NO_OUTPUT,
    CAPPED,
    DUPLICATE,
    NON_DETERMINISTIC,
    TOO_LARGE
  }

  private InstanceResult processInstance(InstanceCandidate candidate, String problemName)
      throws Exception {

    Path fznFile = compileInstance(candidate);
    if (fznFile == null) {
      totalSkippedCompileFail++;
      return InstanceResult.COMPILE_FAIL;
    }

    long fznSize = Files.size(fznFile);
    if (fznSize > MAX_FZN_SIZE_BYTES) {
      System.out.println(
          "    " + candidate.instanceName() + ": .fzn too large (" + fznSize + " bytes), skipping");
      totalSkippedTooLarge++;
      return InstanceResult.TOO_LARGE;
    }

    try {
      SolveResult firstRun = solve(fznFile);

      if (firstRun.timedOut || firstRun.elapsedMs > HARD_TIMEOUT_MS) {
        System.out.println(
            "    " + candidate.instanceName() + ": TIMEOUT (" + firstRun.elapsedMs + " ms)");
        totalSkippedTimeout++;
        return InstanceResult.TIMEOUT;
      }

      if (firstRun.elapsedMs > INCLUSION_MAX_MS) {
        System.out.println(
            "    " + candidate.instanceName() + ": too slow (" + firstRun.elapsedMs + " ms)");
        totalSkippedSlow++;
        return InstanceResult.SLOW;
      }

      String output = filterOutput(firstRun.output);
      if (!output.contains("----------")) {
        System.out.println("    " + candidate.instanceName() + ": no solution found");
        totalSkippedNoOutput++;
        return InstanceResult.NO_OUTPUT;
      }

      String category = categorize(firstRun.elapsedMs);

      if (isCategoryCapped(problemName, category)) {
        totalSkippedCapped++;
        return InstanceResult.CAPPED;
      }

      if (isDuplicate(problemName, candidate.instanceName(), category)) {
        System.out.println("    " + candidate.instanceName() + ": duplicate, skipping");
        totalSkippedDuplicate++;
        return InstanceResult.DUPLICATE;
      }

      if (!checkDeterminism(fznFile, output)) {
        System.out.println("    " + candidate.instanceName() + ": NON-DETERMINISTIC");
        totalSkippedNonDeterministic++;
        return InstanceResult.NON_DETERMINISTIC;
      }

      install(candidate, fznFile, category, output, problemName);
      incrementCount(problemName, category);
      totalAdded++;
      System.out.println(
          "    ADDED: "
              + category
              + "/"
              + problemName
              + "/"
              + candidate.instanceName()
              + " ("
              + firstRun.elapsedMs
              + " ms)");
      return InstanceResult.ADDED;
    } finally {
      Files.deleteIfExists(fznFile);
    }
  }

  private Path compileInstance(InstanceCandidate candidate) {
    try {
      String minizinc = findMinizinc();
      Path outputFzn = workDir.resolve(candidate.instanceName() + ".fzn");
      Files.deleteIfExists(outputFzn);

      List<String> cmd = new ArrayList<>();
      cmd.add(minizinc);
      cmd.add("--compile");
      cmd.add("--solver");
      cmd.add("org.jacop");
      cmd.add(candidate.mznFile().toString());
      if (candidate.dznFile() != null) {
        cmd.add("-d");
        cmd.add(candidate.dznFile().toString());
      }
      cmd.add("--fzn");
      cmd.add(outputFzn.toString());

      ProcessBuilder pb = new ProcessBuilder(cmd);
      pb.redirectErrorStream(true);
      Process process = pb.start();
      new String(process.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
      boolean finished = process.waitFor(120, TimeUnit.SECONDS);
      if (!finished) {
        process.destroyForcibly();
        System.out.println("    " + candidate.instanceName() + ": compilation timed out");
        return null;
      }
      if (process.exitValue() != 0) {
        System.out.println(
            "    "
                + candidate.instanceName()
                + ": compilation failed (exit "
                + process.exitValue()
                + ")");
        return null;
      }
      if (!Files.exists(outputFzn)) {
        System.out.println("    " + candidate.instanceName() + ": no .fzn produced");
        return null;
      }
      return outputFzn;
    } catch (Exception _) {
      System.out.println("    " + candidate.instanceName() + ": compilation error");
      return null;
    }
  }

  private SolveResult solve(Path fznFile) {
    long startMs = System.currentTimeMillis();
    ByteArrayOutputStream baos = new ByteArrayOutputStream();
    PrintStream originalOut = System.out;
    PrintStream originalErr = System.err;
    String output;
    boolean timedOut = false;
    try {
      System.setOut(new PrintStream(baos, true, StandardCharsets.UTF_8));
      System.setErr(new PrintStream(new ByteArrayOutputStream()));
      Fz2jacop fz2jacop = new Fz2jacop();
      fz2jacop.callMain(new String[] {"-t", String.valueOf(HARD_TIMEOUT_MS), fznFile.toString()});
    } catch (Throwable _) {
      timedOut = true;
    } finally {
      System.setOut(originalOut);
      System.setErr(originalErr);
      output = baos.toString(StandardCharsets.UTF_8);
    }
    long elapsedMs = System.currentTimeMillis() - startMs;

    if (output.contains("=====TIME-OUT=====") || output.contains("=====UNKNOWN=====")) {
      timedOut = true;
    }

    return new SolveResult(output, elapsedMs, timedOut);
  }

  private boolean checkDeterminism(Path fznFile, String expectedOutput) {
    for (int i = 2; i <= DETERMINISM_RUNS; i++) {
      SolveResult run = solve(fznFile);
      String runOutput = filterOutput(run.output);
      if (!runOutput.equals(expectedOutput)) {
        return false;
      }
    }
    return true;
  }

  private void install(
      InstanceCandidate candidate, Path fznFile, String category, String output, String problemName)
      throws IOException {

    Path targetDir = FZ_ROOT.resolve(category).resolve(problemName);
    Files.createDirectories(targetDir);

    Path targetFzn = targetDir.resolve(candidate.instanceName() + ".fzn");
    Files.copy(fznFile, targetFzn, StandardCopyOption.REPLACE_EXISTING);

    Path targetOut = targetDir.resolve(candidate.instanceName() + ".out");
    Files.writeString(targetOut, output, StandardCharsets.UTF_8);

    if (candidate.mznFile() != null) {
      Files.copy(
          candidate.mznFile(),
          targetDir.resolve(candidate.mznFile().getFileName()),
          StandardCopyOption.REPLACE_EXISTING);
    }
    if (candidate.dznFile() != null) {
      Files.copy(
          candidate.dznFile(),
          targetDir.resolve(candidate.dznFile().getFileName()),
          StandardCopyOption.REPLACE_EXISTING);
    }

    metadataGenerator.generateForFznFile(targetFzn);

    existingInstancePaths.add(category + "/" + problemName + "/" + candidate.instanceName());
  }

  private void regenerateListFiles() throws IOException {
    for (String category : new String[] {"upTo5sec", "upTo30sec"}) {
      Path categoryDir = FZ_ROOT.resolve(category);
      if (Files.isDirectory(categoryDir)) {
        BenchmarkAdder.regenerateList(categoryDir);
        System.out.println("Regenerated " + category + "/list.txt");
      }
    }
  }

  private List<InstanceCandidate> enumerateInstances(List<Path> mznFiles, List<Path> dznFiles) {
    List<InstanceCandidate> candidates = new ArrayList<>();

    if (dznFiles.isEmpty()) {
      mznFiles.sort(Comparator.comparingLong(this::fileSize));
      for (Path mzn : mznFiles) {
        String name = stripExtension(mzn.getFileName().toString());
        candidates.add(new InstanceCandidate(mzn, null, name));
      }
    } else {
      dznFiles.sort(Comparator.comparingLong(this::fileSize));
      for (Path dzn : dznFiles) {
        for (Path mzn : mznFiles) {
          String name = stripExtension(dzn.getFileName().toString());
          candidates.add(new InstanceCandidate(mzn, dzn, name));
        }
      }
    }
    return candidates;
  }

  static String filterOutput(String rawOutput) {
    StringBuilder sb = new StringBuilder();
    for (String line : rawOutput.split("\n")) {
      if (line.startsWith("Warning:") || line.startsWith("% ") || line.startsWith("%%")) {
        continue;
      }
      sb.append(line).append("\n");
    }
    String result = sb.toString();
    while (result.endsWith("\n\n")) {
      result = result.substring(0, result.length() - 1);
    }
    return result;
  }

  private String categorize(long elapsedMs) {
    if (elapsedMs <= UPTO5SEC_MAX_MS) {
      return "upTo5sec";
    }
    return "upTo30sec";
  }

  private boolean isDuplicate(String problemName, String instanceName, String category) {
    return existingInstancePaths.contains(category + "/" + problemName + "/" + instanceName);
  }

  private boolean isCategoryCapped(String problemName, String category) {
    return getCategoryCount(problemName, category) >= MAX_INSTANCES_PER_PROBLEM;
  }

  private boolean bothCategoriesCapped(String problemName) {
    return isCategoryCapped(problemName, "upTo5sec") && isCategoryCapped(problemName, "upTo30sec");
  }

  private int getCategoryCount(String problemName, String category) {
    return problemCategoryCounts.getOrDefault(problemName, Map.of()).getOrDefault(category, 0);
  }

  private void incrementCount(String problemName, String category) {
    problemCategoryCounts
        .computeIfAbsent(problemName, k -> new HashMap<>())
        .merge(category, 1, Integer::sum);
  }

  private void loadExistingBenchmarks() throws IOException {
    for (String category : new String[] {"upTo5sec", "upTo30sec"}) {
      Path categoryDir = FZ_ROOT.resolve(category);
      if (!Files.isDirectory(categoryDir)) {
        continue;
      }
      try (DirectoryStream<Path> problemDirs = Files.newDirectoryStream(categoryDir)) {
        for (Path problemDir : problemDirs) {
          if (!Files.isDirectory(problemDir)) {
            continue;
          }
          String problemName = problemDir.getFileName().toString();
          try (DirectoryStream<Path> fznFiles = Files.newDirectoryStream(problemDir, "*.fzn")) {
            int count = 0;
            for (Path fzn : fznFiles) {
              String instanceName = stripExtension(fzn.getFileName().toString());
              existingInstancePaths.add(category + "/" + problemName + "/" + instanceName);
              count++;
            }
            if (count > 0) {
              problemCategoryCounts
                  .computeIfAbsent(problemName, k -> new HashMap<>())
                  .put(category, count);
            }
          }
        }
      }
    }
    System.out.println(
        "Loaded " + existingInstancePaths.size() + " existing benchmark instance paths.");
  }

  private long fileSize(Path p) {
    try {
      return Files.size(p);
    } catch (IOException _) {
      return Long.MAX_VALUE;
    }
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

  private static List<Path> listFiles(Path dir, String glob) throws IOException {
    List<Path> result = new ArrayList<>();
    try (DirectoryStream<Path> stream = Files.newDirectoryStream(dir, glob)) {
      for (Path p : stream) {
        if (Files.isRegularFile(p)) {
          result.add(p);
        }
      }
    }
    return result;
  }

  record InstanceCandidate(Path mznFile, Path dznFile, String instanceName) {}

  record SolveResult(String output, long elapsedMs, boolean timedOut) {}

  /**
   * Command-line entry point.
   *
   * @param args first argument is the path to the minizinc-benchmarks directory
   */
  public static void main(String[] args) throws Exception {
    if (args.length < 1) {
      System.err.println("Usage: BenchmarkImporter <path-to-minizinc-benchmarks>");
      System.exit(1);
    }
    BenchmarkImporter importer = new BenchmarkImporter();
    importer.init(Path.of(args[0]));
    importer.importAll();
  }
}
