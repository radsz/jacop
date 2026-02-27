/*
 * BenchmarkMetadataGenerator.java
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

import java.io.BufferedReader;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.DirectoryStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Scans FlatZinc benchmark files and generates per-benchmark {@code metadata.json} files that
 * record which FlatZinc builtins and JaCoP constraint families each benchmark exercises.
 *
 * <p>Run as a standalone program or as a JUnit test via {@code mvn -pl jacop-benchmarks
 * -Dtest=BenchmarkMetadataGenerator#generateAll test}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class BenchmarkMetadataGenerator {

  private static final Path FZ_ROOT = Path.of("src/test/fz");

  static final String[] TIME_CATEGORIES = {
    "upTo5sec", "upTo30sec", "upTo1min", "upTo5min", "upTo10min", "upTo1hour", "above1hour"
  };

  private static final Pattern CONSTRAINT_PATTERN =
      Pattern.compile("^constraint\\s+(\\w+)\\s*\\(", Pattern.MULTILINE);

  private final Map<String, String> builtinToFamily;

  /** Creates a generator using the default {@code constraint-families.json} bundled in the repo. */
  public BenchmarkMetadataGenerator() throws IOException {
    this.builtinToFamily = loadFamilyMapping(FZ_ROOT.resolve("constraint-families.json"));
  }

  /** Generates metadata for all benchmarks across all time categories. */
  public void generateAll() throws IOException {
    int total = 0;
    for (String category : TIME_CATEGORIES) {
      Path categoryDir = FZ_ROOT.resolve(category);
      if (Files.isDirectory(categoryDir)) {
        total += generateForCategory(categoryDir);
      }
    }
    System.out.println("Generated metadata for " + total + " benchmarks.");
  }

  /** Generates metadata for all benchmarks in a single time category directory. */
  public int generateForCategory(Path categoryDir) throws IOException {
    int count = 0;
    try (DirectoryStream<Path> problems = Files.newDirectoryStream(categoryDir)) {
      for (Path problemDir : problems) {
        if (!Files.isDirectory(problemDir)) {
          continue;
        }
        count += generateForProblemDir(problemDir);
      }
    }
    return count;
  }

  /**
   * Generates metadata for all .fzn files in a problem directory. Some problems have multiple .fzn
   * files (different data instances).
   */
  int generateForProblemDir(Path problemDir) throws IOException {
    int count = 0;
    try (DirectoryStream<Path> files = Files.newDirectoryStream(problemDir, "*.fzn")) {
      for (Path fznFile : files) {
        generateForFznFile(fznFile);
        count++;
      }
    }
    return count;
  }

  /** Extracts constraint usage from a single .fzn file and writes the metadata.json. */
  void generateForFznFile(Path fznFile) throws IOException {
    Set<String> fznBuiltins = extractConstraints(fznFile);
    Set<String> families = mapToFamilies(fznBuiltins);

    Path metadataFile = fznFile.getParent().resolve("metadata.json");

    Map<String, Set<String>> existing = new LinkedHashMap<>();
    List<String> existingDomains = new ArrayList<>();
    if (Files.exists(metadataFile)) {
      existing = readExistingMetadata(metadataFile);
      if (existing.containsKey("domains")) {
        existingDomains = new ArrayList<>(existing.get("domains"));
      }
    }

    Set<String> mergedBuiltins = new TreeSet<>(fznBuiltins);
    Set<String> mergedFamilies = new TreeSet<>(families);

    if (Files.exists(metadataFile)) {
      for (Path otherFzn : listFznFiles(fznFile.getParent())) {
        if (!otherFzn.equals(fznFile)) {
          Set<String> otherBuiltins = extractConstraints(otherFzn);
          mergedBuiltins.addAll(otherBuiltins);
          mergedFamilies.addAll(mapToFamilies(otherBuiltins));
        }
      }
    }

    writeMetadataJson(metadataFile, mergedBuiltins, mergedFamilies, existingDomains);
  }

  Set<String> extractConstraints(Path fznFile) throws IOException {
    Set<String> builtins = new LinkedHashSet<>();
    try (BufferedReader reader = Files.newBufferedReader(fznFile, StandardCharsets.UTF_8)) {
      String line;
      while ((line = reader.readLine()) != null) {
        Matcher matcher = CONSTRAINT_PATTERN.matcher(line);
        if (matcher.find()) {
          builtins.add(matcher.group(1));
        }
      }
    }
    return builtins;
  }

  Set<String> mapToFamilies(Set<String> builtins) {
    Set<String> families = new TreeSet<>();
    for (String builtin : builtins) {
      String family = builtinToFamily.get(builtin);
      if (family != null) {
        families.add(family);
      }
    }
    return families;
  }

  private List<Path> listFznFiles(Path dir) throws IOException {
    List<Path> result = new ArrayList<>();
    try (DirectoryStream<Path> files = Files.newDirectoryStream(dir, "*.fzn")) {
      for (Path f : files) {
        result.add(f);
      }
    }
    return result;
  }

  // --- Simple JSON I/O (no external library required) ---

  static void writeMetadataJson(
      Path file, Set<String> fznBuiltins, Set<String> families, List<String> domains)
      throws IOException {
    StringBuilder sb = new StringBuilder();
    sb.append("{\n");
    sb.append("  \"fznBuiltins\": ").append(toJsonArray(fznBuiltins)).append(",\n");
    sb.append("  \"constraintFamilies\": ").append(toJsonArray(families)).append(",\n");
    sb.append("  \"domains\": ").append(toJsonArray(domains)).append("\n");
    sb.append("}\n");
    Files.writeString(file, sb.toString(), StandardCharsets.UTF_8);
  }

  private static String toJsonArray(Iterable<String> items) {
    StringBuilder sb = new StringBuilder("[");
    boolean first = true;
    for (String item : items) {
      if (!first) {
        sb.append(", ");
      }
      sb.append("\"").append(item).append("\"");
      first = false;
    }
    sb.append("]");
    return sb.toString();
  }

  /**
   * Reads an existing metadata.json, returning a map of field name to set of values. Handles the
   * simple flat JSON structure without a full parser.
   */
  static Map<String, Set<String>> readExistingMetadata(Path file) throws IOException {
    return readMetadataJson(file);
  }

  /**
   * Reads a metadata.json file. The format is simple enough to parse with string operations: each
   * field is a JSON array of strings on one or a few lines.
   */
  static Map<String, Set<String>> readMetadataJson(Path file) throws IOException {
    String content = Files.readString(file, StandardCharsets.UTF_8);
    Map<String, Set<String>> result = new LinkedHashMap<>();

    Pattern fieldPattern = Pattern.compile("\"(\\w+)\"\\s*:\\s*\\[([^\\]]*)\\]");
    Matcher fieldMatcher = fieldPattern.matcher(content);
    while (fieldMatcher.find()) {
      String fieldName = fieldMatcher.group(1);
      String arrayContent = fieldMatcher.group(2);
      Set<String> values = new LinkedHashSet<>();
      Pattern valuePattern = Pattern.compile("\"([^\"]+)\"");
      Matcher valueMatcher = valuePattern.matcher(arrayContent);
      while (valueMatcher.find()) {
        values.add(valueMatcher.group(1));
      }
      result.put(fieldName, values);
    }
    return result;
  }

  /**
   * Loads constraint-families.json which maps family -> [builtins], inverts to builtin -> family.
   */
  private static Map<String, String> loadFamilyMapping(Path familiesFile) throws IOException {
    String content = Files.readString(familiesFile, StandardCharsets.UTF_8);
    Map<String, String> builtinToFamily = new HashMap<>();

    Pattern familyPattern = Pattern.compile("\"(\\w+)\"\\s*:\\s*\\[([^\\]]*)\\]");
    Matcher familyMatcher = familyPattern.matcher(content);
    while (familyMatcher.find()) {
      String family = familyMatcher.group(1);
      String builtinsStr = familyMatcher.group(2);
      Pattern builtinPattern = Pattern.compile("\"([^\"]+)\"");
      Matcher builtinMatcher = builtinPattern.matcher(builtinsStr);
      while (builtinMatcher.find()) {
        builtinToFamily.put(builtinMatcher.group(1), family);
      }
    }
    return builtinToFamily;
  }

  /** JUnit entry point: generates metadata for all benchmarks. */
  @org.junit.jupiter.api.Test
  void generateAllMetadata() throws IOException {
    generateAll();
  }

  public static void main(String[] args) throws IOException {
    BenchmarkMetadataGenerator generator = new BenchmarkMetadataGenerator();
    if (args.length > 0) {
      for (String category : args) {
        Path categoryDir = FZ_ROOT.resolve(category);
        if (Files.isDirectory(categoryDir)) {
          int count = generator.generateForCategory(categoryDir);
          System.out.println("Generated metadata for " + count + " benchmarks in " + category);
        } else {
          System.err.println("Category directory not found: " + categoryDir);
        }
      }
    } else {
      generator.generateAll();
    }
  }
}
