/*
 * SolverRun.java
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

package org.jacop.decomposition;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;

/**
 * Runs {@code Fz2jacop} on a FlatZinc file in a separate JVM and collects the solutions it prints.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class SolverRun {

  /** Outcome of a run. */
  enum Status {
    /** The search finished: every solution was printed (none for an unsatisfiable model). */
    COMPLETE,
    /** The time or solution limit stopped the search. */
    INCOMPLETE,
    /** The solver failed. */
    ERROR
  }

  /** Solution texts kept in memory for diagnostics and cross-checks. */
  static final int STORED_SOLUTIONS = 10_000;

  Status status = Status.ERROR;
  long solutions;
  long nodes = -1;
  long millis;
  String error = "";

  /** Distinct solutions (text) with their multiplicity, the first STORED_SOLUTIONS of them. */
  final Map<String, Integer> distinct = new LinkedHashMap<>();

  private final Set<Long> hashes = new HashSet<>();

  /** Hash of each solution in the order in which they were printed. */
  final List<Long> order = new ArrayList<>();

  private long distinctDigest;

  /** Last solution printed, used to read the objective of an optimisation run. */
  String lastSolution = "";

  long distinctCount() {
    return hashes.size();
  }

  /** Whether a solution with this text was printed. */
  boolean contains(String solution) {
    return hashes.contains(hash(solution));
  }

  /** Order-independent digest of the set of distinct solutions. */
  String digest() {
    return Long.toHexString(distinctDigest);
  }

  static SolverRun run(
      Path fzn, List<String> options, boolean all, int solutionLimit, int timeoutMillis) {
    List<String> cmd = new ArrayList<>();
    cmd.add(Path.of(System.getProperty("java.home"), "bin", "java").toString());
    cmd.add("-Xss64m");
    cmd.add("-Xmx" + System.getProperty("decomp.xmx", "4g"));
    cmd.add("-cp");
    cmd.add(System.getProperty("decomp.classpath", System.getProperty("java.class.path")));
    cmd.add("org.jacop.fz.Fz2jacop");
    cmd.addAll(options);
    cmd.add("--default-search");
    cmd.add("input");
    cmd.add("-s");
    if (all) {
      cmd.add("-a");
    }
    if (solutionLimit > 0) {
      cmd.add("-n");
      cmd.add(Integer.toString(solutionLimit));
    }
    cmd.add("-t");
    cmd.add(Integer.toString(timeoutMillis));
    cmd.add(fzn.toString());

    SolverRun result = new SolverRun();
    long start = System.nanoTime();
    try {
      Path stderr = Files.createTempFile("decomp", ".err");
      ProcessBuilder pb = new ProcessBuilder(cmd).redirectError(stderr.toFile());
      pb.environment().remove("JAVA_TOOL_OPTIONS");
      Process p = pb.start();
      Thread reader =
          Thread.ofVirtual()
              .start(
                  () -> {
                    try (BufferedReader r =
                        new BufferedReader(
                            new InputStreamReader(p.getInputStream(), StandardCharsets.UTF_8))) {
                      result.read(r);
                    } catch (IOException | RuntimeException | Error e) {
                      result.status = Status.ERROR;
                      result.error = "reading the output: " + e;
                    }
                  });
      if (!p.waitFor(timeoutMillis + 30_000L, TimeUnit.MILLISECONDS)) {
        p.destroyForcibly();
        p.waitFor();
        reader.join();
        result.status = Status.INCOMPLETE;
        result.error = "killed after the time limit";
      } else {
        reader.join();
        String err = Files.readString(stderr);
        if (p.exitValue() != 0 || err.contains("Exception") || err.contains("Error")) {
          if (result.status != Status.INCOMPLETE) {
            result.status = Status.ERROR;
          }
          result.error = (result.error + " exit=" + p.exitValue() + " " + firstLines(err)).strip();
        }
      }
      Files.deleteIfExists(stderr);
    } catch (IOException e) {
      result.status = Status.ERROR;
      result.error = e.toString();
    } catch (InterruptedException e) {
      Thread.currentThread().interrupt();
      result.status = Status.ERROR;
      result.error = e.toString();
    }
    result.millis = (System.nanoTime() - start) / 1_000_000;
    return result;
  }

  private static String firstLines(String text) {
    String[] lines = text.strip().split("\n");
    StringBuilder b = new StringBuilder();
    for (int i = 0; i < Math.min(lines.length, 4); i++) {
      b.append(lines[i].strip()).append(" | ");
    }
    return b.toString().replace('\t', ' ');
  }

  private void read(BufferedReader r) throws IOException {
    Status seen = Status.INCOMPLETE;
    StringBuilder current = new StringBuilder();
    String line;
    while ((line = r.readLine()) != null) {
      String t = line.strip();
      if (t.startsWith("%%%mzn-stat: nodes=")) {
        nodes = Long.parseLong(t.substring("%%%mzn-stat: nodes=".length()).strip());
      }
      if (t.isEmpty() || t.startsWith("%")) {
        continue;
      }
      switch (t) {
        case "----------" -> {
          addSolution(current.toString());
          current.setLength(0);
        }
        case "==========", "=====UNSATISFIABLE=====" -> seen = Status.COMPLETE;
        case "=====UNKNOWN=====", "=====UNSATorUNBOUNDED=====", "=====UNBOUNDED=====" -> {
          // keep INCOMPLETE
        }
        case "=====ERROR=====" -> {
          seen = Status.ERROR;
          error = "=====ERROR=====";
        }
        default -> current.append(t).append('\n');
      }
    }
    status = seen;
  }

  private void addSolution(String text) {
    solutions++;
    lastSolution = text;
    long h = hash(text);
    order.add(h);
    if (hashes.add(h)) {
      distinctDigest += h;
      if (distinct.size() < STORED_SOLUTIONS) {
        distinct.put(text, 1);
      }
    } else {
      distinct.computeIfPresent(text, (k, v) -> v + 1);
    }
  }

  static long hash(String text) {
    try {
      byte[] h = MessageDigest.getInstance("SHA-256").digest(text.getBytes(StandardCharsets.UTF_8));
      long v = 0;
      for (int i = 0; i < 8; i++) {
        v = (v << 8) | (h[i] & 0xff);
      }
      return v;
    } catch (NoSuchAlgorithmException e) {
      throw new IllegalStateException(e);
    }
  }

  /** Value printed for a variable in a solution ({@code name = value;}), or null. */
  static String value(String solution, String name) {
    for (String line : solution.split("\n")) {
      int eq = line.indexOf('=');
      if (eq > 0 && line.substring(0, eq).strip().equals(name)) {
        String v = line.substring(eq + 1).strip();
        return v.endsWith(";") ? v.substring(0, v.length() - 1).strip() : v;
      }
    }
    return null;
  }
}
