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
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
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
public class MinizincBasedTestsHelper {
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
  public static void initialize() {
    fz2jacop = new Fz2jacop();
  }

  protected static List<String> expected(String filename) throws IOException {

    String filePath = new File(RELATIVE_PATH + filename).getAbsolutePath();
    return Files.readAllLines(Path.of(filePath), StandardCharsets.UTF_8);
  }

  protected static Collection<String> fileReader(String timeCategory) throws IOException {

    IO.println("timeCategory" + timeCategory);
    try (FileReader file = new FileReader(RELATIVE_PATH + timeCategory + LIST_FILE_NAME);
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
  public void cleanUp() {
    String outputFilename = RELATIVE_PATH + timeCategory + testFilename + ".fzn" + ".out";
    try {
      Files.delete(Path.of(outputFilename));
    } catch (IOException _) {
      // e.printStackTrace(); // can be helpful when updating code and/or tests instances.
      // File was not created (because the test timeout before it was created so deleting it failed.
    }
    System.gc();
  }

  public int counter() {
    return COUNTER;
  }

  protected List<String> computeResult(String filename) throws IOException {

    String outputFilename =
        RELATIVE_PATH + filename + ".out"; // outputFilename contains path to *.out file.
    String foo = outputFilename.substring(0, outputFilename.lastIndexOf('/'));

    // If options.opt exist reads parameters from the file and uses them in fzn2jacop program.
    if (Files.exists(Path.of(foo + "/options.opt"))) {
      try (BufferedReader reader =
          Files.newBufferedReader(Path.of(foo + "/options.opt"), Charset.defaultCharset())) {
        String line;
        List<String> options = new ArrayList<>();
        while ((line = reader.readLine()) != null) {
          options.add(line);
        }
        // fz2jacop compute result with options
        fz2jacop.callMain(
            new String[] {
              options.getFirst(),
              options.get(1),
              "--outputfile",
              outputFilename,
              RELATIVE_PATH + filename
            });
        FloatDomain.setFormat(Double.MAX_VALUE);
      }
    } else {
      // fz2jacop compute result
      fz2jacop.callMain(new String[] {"--outputfile", outputFilename, RELATIVE_PATH + filename});
    }

    String result = new String(Files.readAllBytes(Path.of(outputFilename)));

    if (PRINT_INFO) {
      IO.println(filename + "\n" + result);
    }

    return Arrays.asList(result.split("\n"));
  }

  protected void testExecution(String timeCategory) throws IOException {

    IO.println("Test file: " + timeCategory + testFilename);
    List<String> result = new ArrayList<>();
    List<String> expectedResult =
        expected(timeCategory + testFilename + ".out"); // path to file name *.out
    List<String> res =
        computeResult(timeCategory + testFilename + ".fzn"); // path to file name *.fzn

    if ("==========".equals(expectedResult.getLast())) {
      int i;
      for (i = 0; i < res.size(); i++) {
        result.add(res.get(i));
      }
      result.add("==========");
    } else {
      result = res;
    }

    if (result.isEmpty()) {
      fail(
          "\n"
              + "File path: "
              + timeCategory
              + testFilename
              + ".fzn "
              + " gave no output to compare against.");
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
                + timeCategory
                + testFilename
                + ".out "
                + " gave as a result less textlines that was expected. Expected line "
                + (j + 1)
                + " not found.");
      }
      if (expectedResult.size() == j) {
        fail(
            "\n"
                + "File path: "
                + timeCategory
                + testFilename
                + ".out "
                + " gave as a result more textlines that was expected. Actual line "
                + (i + 1)
                + "not found in expected result");
      }

      assertThat(result.get(i).trim())
          .as(
              "\n"
                  + "File path: "
                  + timeCategory
                  + testFilename
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
