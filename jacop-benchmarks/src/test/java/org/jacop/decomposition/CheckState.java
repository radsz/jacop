/*
 * CheckState.java
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

import java.io.BufferedWriter;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * The record of earlier runs, one tab-separated line per result, so that a stopped check resumes
 * with the next problem or constraint that has not been checked. Lines are only appended; a later
 * line for the same key replaces an earlier one.
 *
 * <ul>
 *   <li>{@code B problem hash kind objective status solutions distinct digest nodes millis date} is
 *       the reference run of the problem with JaCoP's own constraints.
 *   <li>{@code C problem hash constraint occurrences verdict status solutions distinct digest nodes
 *       millis date note} is the check of one constraint, every occurrence decomposed.
 *   <li>{@code N problem hash reason date} marks a problem with nothing to check.
 * </ul>
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class CheckState {

  static final String HEADER =
      "# Decomposition check state, see DecompositionCheck. Columns are tab-separated.\n"
          + "# B problem hash kind objective status solutions distinct digest nodes millis date\n"
          + "# C problem hash constraint occurrences verdict status solutions distinct digest"
          + " nodes millis date note\n"
          + "# N problem hash reason date\n";

  private final Path file;
  final Map<String, String[]> baselines = new HashMap<>();
  final Map<String, String[]> checks = new HashMap<>();
  final Map<String, String[]> nothing = new HashMap<>();

  CheckState(Path file) throws IOException {
    this.file = file;
    if (Files.exists(file)) {
      List<String> lines = Files.readAllLines(file, StandardCharsets.UTF_8);
      for (String line : lines) {
        if (line.isBlank() || line.startsWith("#")) {
          continue;
        }
        String[] f = line.split("\t", -1);
        switch (f[0]) {
          case "B" -> baselines.put(f[1] + "\t" + f[2], f);
          case "C" -> checks.put(f[1] + "\t" + f[2] + "\t" + f[3], f);
          case "N" -> nothing.put(f[1] + "\t" + f[2], f);
          default -> throw new IllegalStateException("bad line in " + file + ": " + line);
        }
      }
    } else {
      Files.createDirectories(file.toAbsolutePath().getParent());
      Files.writeString(file, HEADER, StandardCharsets.UTF_8);
    }
  }

  String[] baseline(String problem, String hash) {
    return baselines.get(problem + "\t" + hash);
  }

  String[] check(String problem, String hash, String constraint) {
    return checks.get(problem + "\t" + hash + "\t" + constraint);
  }

  boolean nothingToCheck(String problem, String hash) {
    return nothing.containsKey(problem + "\t" + hash);
  }

  synchronized void append(String... fields) {
    for (int i = 0; i < fields.length; i++) {
      fields[i] = fields[i] == null ? "" : fields[i].replace('\t', ' ').replace('\n', ' ');
    }
    switch (fields[0]) {
      case "B" -> baselines.put(fields[1] + "\t" + fields[2], fields);
      case "C" -> checks.put(fields[1] + "\t" + fields[2] + "\t" + fields[3], fields);
      case "N" -> nothing.put(fields[1] + "\t" + fields[2], fields);
      default -> throw new IllegalArgumentException(fields[0]);
    }
    try (BufferedWriter w =
        Files.newBufferedWriter(
            file, StandardCharsets.UTF_8, StandardOpenOption.CREATE, StandardOpenOption.APPEND)) {
      w.write(String.join("\t", fields));
      w.write('\n');
    } catch (IOException e) {
      throw new IllegalStateException("cannot write " + file, e);
    }
  }
}
