/*
 * MinizincByConstraintTest.java
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

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.fail;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;
import org.jacop.floats.core.FloatDomain;
import org.jacop.fz.Fz2jacop;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.TestFactory;

/**
 * Constraint-family-based test runner for MiniZinc/FlatZinc benchmarks. Selects benchmarks by the
 * JaCoP constraint families they exercise, using per-benchmark {@code metadata.json} files.
 *
 * <p>System properties:
 *
 * <ul>
 *   <li>{@code constraintFilter} -- comma-separated constraint family names (e.g., {@code
 *       alldifferent,cumulative}). Required.
 *   <li>{@code timeFilter} -- maximum time category to include. Defaults to {@code upTo30sec}.
 *       Cumulative: {@code upTo30sec} includes both upTo5sec and upTo30sec. Use {@code all} for
 *       every category.
 * </ul>
 *
 * <p>Usage: {@code mvn -pl jacop-benchmarks -Dtest=MinizincByConstraintTest
 * -DconstraintFilter=alldifferent test}
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class MinizincByConstraintTest {

  private static final String RELATIVE_PATH = "src/test/fz/";

  private static final LinkedHashMap<String, Integer> CATEGORY_TIMEOUTS = new LinkedHashMap<>();

  static {
    CATEGORY_TIMEOUTS.put("upTo5sec", 20);
    CATEGORY_TIMEOUTS.put("upTo30sec", 100);
    CATEGORY_TIMEOUTS.put("upTo1min", 180);
    CATEGORY_TIMEOUTS.put("upTo5min", 600);
    CATEGORY_TIMEOUTS.put("upTo10min", 1200);
    CATEGORY_TIMEOUTS.put("upTo1hour", 5400);
    CATEGORY_TIMEOUTS.put("above1hour", 7200);
  }

  private final Fz2jacop fz2jacop = new Fz2jacop();

  @TestFactory
  Stream<DynamicTest> testByConstraint() throws IOException {
    String constraintFilter = System.getProperty("constraintFilter", "");
    String timeFilter = System.getProperty("timeFilter", "upTo30sec");

    assumeTrue(
        !constraintFilter.isEmpty(),
        "No constraintFilter specified. Use -DconstraintFilter=<family1,family2,...>");

    Set<String> requestedFamilies = new LinkedHashSet<>();
    for (String f : constraintFilter.split(",")) {
      String trimmed = f.trim();
      if (!trimmed.isEmpty()) {
        requestedFamilies.add(trimmed);
      }
    }

    List<String> includedCategories = resolveCategories(timeFilter);
    List<BenchmarkEntry> benchmarks = collectBenchmarks(requestedFamilies, includedCategories);

    System.out.println(
        "MinizincByConstraintTest: constraintFilter="
            + requestedFamilies
            + " timeFilter="
            + timeFilter
            + " -> "
            + benchmarks.size()
            + " benchmarks");

    return benchmarks.stream()
        .map(entry -> DynamicTest.dynamicTest(entry.displayName(), () -> runBenchmark(entry)));
  }

  private void runBenchmark(BenchmarkEntry entry) {
    int timeoutSeconds = CATEGORY_TIMEOUTS.getOrDefault(entry.timeCategory, 100);
    assertTimeoutPreemptively(
        Duration.ofSeconds(timeoutSeconds),
        () -> {
          String outputFile = null;
          try {
            outputFile = executeBenchmark(entry.fullPath, entry.timeCategory);
          } finally {
            if (outputFile != null) {
              try {
                Files.deleteIfExists(Path.of(outputFile));
              } catch (IOException _) {
              }
            }
            System.gc();
          }
        },
        "Benchmark " + entry.fullPath + " exceeded timeout of " + timeoutSeconds + "s");
  }

  private String executeBenchmark(String fullPath, String timeCategory) throws IOException {
    String fznPath = RELATIVE_PATH + fullPath + ".fzn";
    String expectedPath = RELATIVE_PATH + fullPath + ".out";
    String outputFilename = fznPath + ".out";

    String optionsDir = fznPath.substring(0, fznPath.lastIndexOf('/'));
    if (Files.exists(Path.of(optionsDir + "/options.opt"))) {
      try (BufferedReader reader =
          Files.newBufferedReader(Path.of(optionsDir + "/options.opt"), Charset.defaultCharset())) {
        List<String> options = new ArrayList<>();
        String line;
        while ((line = reader.readLine()) != null) {
          options.add(line);
        }
        fz2jacop.callMain(
            new String[] {
              options.getFirst(), options.get(1), "--outputfile", outputFilename, fznPath
            });
        FloatDomain.setFormat(Double.MAX_VALUE);
      }
    } else {
      fz2jacop.callMain(new String[] {"--outputfile", outputFilename, fznPath});
    }

    List<String> expectedResult = Files.readAllLines(Path.of(expectedPath), StandardCharsets.UTF_8);
    String resultStr = Files.readString(Path.of(outputFilename), StandardCharsets.UTF_8);
    List<String> res = Arrays.asList(resultStr.split("\n"));

    List<String> result;
    if (!expectedResult.isEmpty() && "==========".equals(expectedResult.getLast())) {
      result = new ArrayList<>(res);
      result.add("==========");
    } else {
      result = res;
    }

    if (result.isEmpty()) {
      fail("\nFile path: " + fullPath + ".fzn  gave no output to compare against.");
    }

    for (int i = 0, j = 0; i < result.size() || j < expectedResult.size(); ) {
      if (i < result.size() && result.get(i).trim().isEmpty()) {
        i++;
        continue;
      }
      if (j < expectedResult.size() && expectedResult.get(j).trim().isEmpty()) {
        j++;
        continue;
      }
      if (result.size() == i) {
        fail(
            "\nFile path: "
                + fullPath
                + ".out  gave as a result less textlines that was expected. Expected line "
                + (j + 1)
                + " not found.");
      }
      if (expectedResult.size() == j) {
        fail(
            "\nFile path: "
                + fullPath
                + ".out  gave as a result more textlines that was expected. Actual line "
                + (i + 1)
                + " not found in expected result");
      }
      assertThat(result.get(i).trim())
          .as(
              "\nFile path: "
                  + fullPath
                  + ".out \nError line number (expected, actual): ("
                  + (j + 1)
                  + ","
                  + (i + 1)
                  + ")\n")
          .isEqualTo(expectedResult.get(j).trim());
      i++;
      j++;
    }
    return outputFilename;
  }

  /**
   * Resolves the cumulative list of time categories to include based on the timeFilter value. E.g.,
   * "upTo30sec" includes ["upTo5sec", "upTo30sec"].
   */
  static List<String> resolveCategories(String timeFilter) {
    if ("all".equalsIgnoreCase(timeFilter)) {
      return new ArrayList<>(CATEGORY_TIMEOUTS.keySet());
    }
    List<String> result = new ArrayList<>();
    for (String category : CATEGORY_TIMEOUTS.keySet()) {
      result.add(category);
      if (category.equals(timeFilter)) {
        break;
      }
    }
    return result;
  }

  /**
   * Collects benchmark entries matching any of the requested constraint families, scanning
   * metadata.json files in the included time categories. Deduplicates by full benchmark path.
   */
  private List<BenchmarkEntry> collectBenchmarks(
      Set<String> requestedFamilies, List<String> categories) throws IOException {
    LinkedHashSet<BenchmarkEntry> result = new LinkedHashSet<>();

    for (String category : categories) {
      Path categoryDir = Path.of(RELATIVE_PATH, category);
      if (!Files.isDirectory(categoryDir)) {
        continue;
      }
      try (DirectoryStream<Path> problemDirs = Files.newDirectoryStream(categoryDir)) {
        for (Path problemDir : problemDirs) {
          if (!Files.isDirectory(problemDir)) {
            continue;
          }
          Path metadataFile = problemDir.resolve("metadata.json");
          if (!Files.exists(metadataFile)) {
            continue;
          }
          Map<String, Set<String>> metadata =
              BenchmarkMetadataGenerator.readMetadataJson(metadataFile);
          Set<String> families = metadata.getOrDefault("constraintFamilies", Set.of());

          boolean matches = false;
          for (String family : requestedFamilies) {
            if (families.contains(family)) {
              matches = true;
              break;
            }
          }
          if (!matches) {
            continue;
          }

          try (DirectoryStream<Path> fznFiles = Files.newDirectoryStream(problemDir, "*.fzn")) {
            for (Path fznFile : fznFiles) {
              String fznName = fznFile.getFileName().toString();
              String benchName = fznName.substring(0, fznName.length() - 4);
              String fullPath = category + "/" + problemDir.getFileName() + "/" + benchName;

              Path outFile = problemDir.resolve(benchName + ".out");
              if (Files.exists(outFile)) {
                result.add(new BenchmarkEntry(fullPath, category));
              }
            }
          }
        }
      }
    }
    return new ArrayList<>(result);
  }

  record BenchmarkEntry(String fullPath, String timeCategory) {
    String displayName() {
      return "[" + timeCategory + "] " + fullPath;
    }

    @Override
    public int hashCode() {
      return fullPath.hashCode();
    }

    @Override
    public boolean equals(Object obj) {
      if (this == obj) {
        return true;
      }
      if (obj instanceof BenchmarkEntry other) {
        return fullPath.equals(other.fullPath);
      }
      return false;
    }
  }
}
