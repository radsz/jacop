/*
 * MinizincBasedTestsHelper.java
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

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import lombok.extern.slf4j.Slf4j;
import org.jacop.floats.core.FloatDomain;
import org.jacop.fz.Fz2jacop;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;

/**
 * Test Helper used by all Minizinc based tests.
 *
 * @author Mariusz Świerkot and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
class MinizincBasedTestsHelper {
  protected static final String RELATIVE_PATH = "src/test/fz/";
  protected static final String LIST_FILE_NAME = "list.txt";
  protected static final boolean PRINT_INFO = false;
  private static final int COUNTER = 0;
  protected static Fz2jacop fz2jacop;
  final String timeCategory;
  protected String testFilename;

  protected MinizincBasedTestsHelper(String timeCategory) {
    this.timeCategory = timeCategory;
  }

  @BeforeAll
  static void initialize() {
    fz2jacop = new Fz2jacop();
  }

  protected static List<String> expected(String filename) throws IOException {

    String filePath = new File(RELATIVE_PATH + filename).getAbsolutePath();
    return Files.readAllLines(Path.of(filePath), StandardCharsets.UTF_8);
  }

  protected static Collection<String> fileReader(String timeCategory) throws IOException {
    return fileReader(timeCategory, LIST_FILE_NAME);
  }

  protected static Collection<String> fileReader(String timeCategory, String listFileName)
      throws IOException {

    log.info("timeCategory" + timeCategory);
    try (FileReader file = new FileReader(RELATIVE_PATH + timeCategory + listFileName);
        BufferedReader br = new BufferedReader(file)) {

      String line = "";
      List<String> list = new ArrayList<>();
      int i = 0;
      while ((line = br.readLine()) != null) {
        list.add(i, line);
        i++;
      }

      return list;
    }
  }

  @AfterEach
  void cleanUp() {
    System.gc();
  }

  public int counter() {
    return COUNTER;
  }

  /**
   * The arguments of the model's directory: every whitespace-separated word of every line of its
   * options.opt, or none when the directory has no such file.
   */
  protected static List<String> options(String modelDirectory) throws IOException {
    Path file = Path.of(modelDirectory, "options.opt");
    List<String> options = new ArrayList<>();
    if (Files.exists(file)) {
      for (String line : Files.readAllLines(file, Charset.defaultCharset())) {
        for (String word : line.trim().split("\\s+")) {
          if (!word.isEmpty()) {
            options.add(word);
          }
        }
      }
    }
    return options;
  }

  /**
   * Solves the model as fzn-jacop does from the command line and returns what it prints, its status
   * lines ({@code ==========}, {@code =====UNSATISFIABLE=====}, {@code =====UNKNOWN=====})
   * included. Comment lines (starting with %) are left out. A run that ends with a non-zero exit
   * status fails.
   */
  protected List<String> computeResult(String filename) throws IOException {

    String model = RELATIVE_PATH + filename;
    // The expected outputs of models without search annotation were recorded with the input order
    // search, so it is kept with --default-search input. The options of options.opt come first.
    List<String> args = options(model.substring(0, model.lastIndexOf('/')));
    args.addAll(List.of("--default-search", "input", model));

    PrintStream out = System.out;
    ByteArrayOutputStream printed = new ByteArrayOutputStream();
    int status;
    try (PrintStream capture = new PrintStream(printed, true, StandardCharsets.UTF_8)) {
      System.setOut(capture);
      status = fz2jacop.callMain(args.toArray(new String[0]));
    } finally {
      System.setOut(out);
      FloatDomain.setFormat(Double.MAX_VALUE);
    }
    String result = printed.toString(StandardCharsets.UTF_8);

    if (PRINT_INFO) {
      log.info(filename + "\n" + result);
    }
    assertThat(status)
        .as("\nFile path: " + filename + " ended with exit status " + status + ":\n" + result)
        .isZero();

    return withoutComments(Arrays.asList(result.split("\n")));
  }

  private static List<String> withoutComments(List<String> lines) {
    return lines.stream().filter(l -> !l.trim().startsWith("%")).toList();
  }

  protected void testExecution(String timeCategory) throws IOException {

    String test = timeCategory + testFilename;
    log.info("Test file: " + test);
    // the status line the expected output ends with (==========, =====UNSATISFIABLE=====) is
    // compared as any other line: a run that does not prove what the expected output claims fails
    List<String> expectedResult = withoutComments(expected(test + ".out"));
    String previous = FIRST_ATTEMPTS.get(test);
    try {
      compare(test, expectedResult, computeResult(test + ".fzn"));
    } catch (AssertionError e) {
      FIRST_ATTEMPTS.putIfAbsent(test, e.getMessage());
      throw e;
    }
    if (previous != null) {
      // a rerun (rerunFailingTestsCount) that passes after an attempt that printed another output:
      // the answer depends on the run, so the test fails rather than passing as a flake
      fail(
          "\nFile path: "
              + test
              + " printed the expected output only when run again:\n"
              + previous);
    }
  }

  /** The output of the first attempt of a test that printed a wrong output, by test. */
  private static final Map<String, String> FIRST_ATTEMPTS = new ConcurrentHashMap<>();

  private static void compare(String test, List<String> expectedResult, List<String> result) {

    if (result.stream().allMatch(l -> l.trim().isEmpty())) {
      fail("\n" + "File path: " + test + ".fzn " + " gave no output to compare against.");
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
            "\n"
                + "File path: "
                + test
                + ".out "
                + " gave as a result less textlines that was expected. Expected line "
                + (j + 1)
                + " ("
                + expectedResult.get(j).trim()
                + ") not found.");
      }
      if (expectedResult.size() == j) {
        fail(
            "\n"
                + "File path: "
                + test
                + ".out "
                + " gave as a result more textlines that was expected. Actual line "
                + (i + 1)
                + " ("
                + result.get(i).trim()
                + ") not found in expected result");
      }

      assertThat(result.get(i).trim())
          .as(
              "\n"
                  + "File path: "
                  + test
                  + ".out "
                  + "\nError line number (expected, actual): ("
                  + (j + 1)
                  + ","
                  + (i + 1)
                  + ")\n")
          .isEqualTo(expectedResult.get(j).trim());
      i++;
      j++;
    }
  }
}
