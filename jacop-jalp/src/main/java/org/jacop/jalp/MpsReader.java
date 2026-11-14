/*
 * MpsReader.java
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.jalp;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.zip.GZIPInputStream;

/**
 * Reads a linear program in MPS format, free or fixed (fields separated by white space, so names
 * must not contain spaces), plain or gzipped. Sections: NAME, OBJSENSE (MIN, MAX), ROWS, COLUMNS
 * (with integer MARKER lines), RHS (an entry on the objective row is minus the objective constant),
 * RANGES, BOUNDS (UP, LO, FX, FR, MI, PL, BV, LI, UI, SC taken as UP) and ENDATA. The first N row
 * is the objective; other N rows are dropped.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class MpsReader {

  private MpsReader() {}

  /**
   * Reads a file, gzipped when its name ends with .gz.
   *
   * @param file the file
   * @return the problem
   * @throws IOException when the file cannot be read or is not valid MPS
   */
  public static LpProblem read(Path file) throws IOException {
    String name = file.getFileName().toString().replaceAll("(\\.mps)?(\\.gz)?$", "");
    if (!file.toString().endsWith(".gz")) {
      return read(Files.readAllBytes(file), name);
    }
    try (InputStream in = new GZIPInputStream(Files.newInputStream(file), 1 << 16)) {
      return read(in.readAllBytes(), name);
    }
  }

  /**
   * Reads a problem from a stream.
   *
   * @param in the stream, plain MPS
   * @param defaultName the name used when the file has none
   * @return the problem
   * @throws IOException when the stream cannot be read or is not valid MPS
   */
  public static LpProblem read(InputStream in, String defaultName) throws IOException {
    return read(in.readAllBytes(), defaultName);
  }

  // free format first; names with spaces only parse in fixed format, so that is tried next
  private static LpProblem read(byte[] data, String defaultName) throws IOException {
    try {
      return read(data, defaultName, false);
    } catch (IOException free) {
      try {
        return read(data, defaultName, true);
      } catch (IOException fixed) {
        free.addSuppressed(fixed);
        throw free;
      }
    }
  }

  // the fields of a data line of fixed MPS (columns 2-3, 5-12, 15-22, 25-36, 40-47, 50-61), the
  // blank ones left out
  private static String[] fixedFields(String line) {
    int[][] f = {{1, 3}, {4, 12}, {14, 22}, {24, 36}, {39, 47}, {49, 61}};
    List<String> out = new ArrayList<>(6);
    for (int[] b : f) {
      if (b[0] < line.length()) {
        String t = line.substring(b[0], Math.min(b[1], line.length())).trim();
        if (!t.isEmpty()) {
          out.add(t);
        }
      }
    }
    return out.toArray(new String[0]);
  }

  @SuppressWarnings("checkstyle:CyclomaticComplexity")
  private static LpProblem read(byte[] data, String defaultName, boolean fixed) throws IOException {
    Iterator<String> lines = new String(data, StandardCharsets.US_ASCII).lines().iterator();
    String name = defaultName;
    boolean maximize = false;
    String objective = null;
    Map<String, Integer> rowIndex = new HashMap<>();
    List<String> rowNames = new ArrayList<>();
    List<Character> rowType = new ArrayList<>();
    Map<String, Integer> colIndex = new HashMap<>();
    List<String> colNames = new ArrayList<>();
    List<Boolean> colInteger = new ArrayList<>();
    // the nonzeros by column, as (row, value) pairs
    List<int[]> colRows = new ArrayList<>();
    List<double[]> colVals = new ArrayList<>();
    List<Integer> colLen = new ArrayList<>();
    double[] cost = new double[16];
    double[] rhs = new double[16];
    double[] range = new double[16];
    boolean[] hasRange = new boolean[16];
    double costConstant = 0;
    double[] lo = new double[16];
    double[] up = new double[16];
    boolean[] upSet = new boolean[16];
    boolean[] loSet = new boolean[16];
    Map<String, Boolean> skipRows = new HashMap<>();
    String section = "";
    boolean integerMarker = false;
    int lineNo = 0;
    while (lines.hasNext()) {
      String line = lines.next();
      lineNo++;
      if (line.isEmpty() || line.charAt(0) == '*') {
        continue;
      }
      String[] tok =
          fixed && Character.isWhitespace(line.charAt(0))
              ? fixedFields(line)
              : line.trim().split("\\s+");
      if (tok.length == 0 || tok[0].isEmpty()) {
        continue;
      }
      if (!Character.isWhitespace(line.charAt(0))) {
        section = tok[0].toUpperCase();
        if (section.equals("NAME")) {
          name = tok.length > 1 ? tok[1] : defaultName;
        } else if (section.equals("OBJSENSE") && tok.length > 1) {
          maximize = tok[1].toUpperCase().startsWith("MAX");
        } else if (section.equals("ENDATA")) {
          break;
        }
        continue;
      }
      switch (section) {
        case "OBJSENSE" -> maximize = tok[0].toUpperCase().startsWith("MAX");
        case "ROWS" -> {
          char t = Character.toUpperCase(tok[0].charAt(0));
          String rn = tok[1];
          if (t == 'N') {
            if (objective == null) {
              objective = rn;
            } else {
              skipRows.put(rn, true);
            }
          } else {
            rowIndex.put(rn, rowNames.size());
            rowNames.add(rn);
            rowType.add(t);
          }
        }
        case "COLUMNS" -> {
          if (tok.length >= 3 && tok[1].equals("'MARKER'")) {
            integerMarker = tok[2].equals("'INTORG'");
            continue;
          }
          String cn = tok[0];
          Integer jj = colIndex.get(cn);
          if (jj == null) {
            jj = colNames.size();
            colIndex.put(cn, jj);
            colNames.add(cn);
            colInteger.add(integerMarker);
            colRows.add(new int[4]);
            colVals.add(new double[4]);
            colLen.add(0);
            if (jj >= cost.length) {
              int sz = cost.length * 2;
              cost = Arrays.copyOf(cost, sz);
              lo = Arrays.copyOf(lo, sz);
              up = Arrays.copyOf(up, sz);
              upSet = Arrays.copyOf(upSet, sz);
              loSet = Arrays.copyOf(loSet, sz);
            }
          }
          int j = jj;
          for (int t = 1; t + 1 < tok.length; t += 2) {
            String rn = tok[t];
            double v = number(tok[t + 1], lineNo);
            if (rn.equals(objective)) {
              cost[j] += v;
            } else if (!skipRows.containsKey(rn)) {
              Integer i = rowIndex.get(rn);
              if (i == null) {
                throw new IOException("line " + lineNo + ": unknown row " + rn);
              }
              int len = colLen.get(j);
              int[] cr = colRows.get(j);
              double[] cv = colVals.get(j);
              if (len == cr.length) {
                cr = Arrays.copyOf(cr, len * 2);
                cv = Arrays.copyOf(cv, len * 2);
                colRows.set(j, cr);
                colVals.set(j, cv);
              }
              cr[len] = i;
              cv[len] = v;
              colLen.set(j, len + 1);
            }
          }
        }
        case "RHS", "RANGES" -> {
          // the set name is optional when the fields come in pairs
          int start = tok.length % 2 == 1 ? 1 : 0;
          for (int t = start; t + 1 < tok.length; t += 2) {
            String rn = tok[t];
            double v = number(tok[t + 1], lineNo);
            if (rn.equals(objective)) {
              if (section.equals("RHS")) {
                costConstant = -v;
              }
              continue;
            }
            if (skipRows.containsKey(rn)) {
              continue;
            }
            Integer i = rowIndex.get(rn);
            if (i == null) {
              throw new IOException("line " + lineNo + ": unknown row " + rn);
            }
            if (i >= rhs.length) {
              int sz = Math.max(rhs.length * 2, i + 1);
              rhs = Arrays.copyOf(rhs, sz);
              range = Arrays.copyOf(range, sz);
              hasRange = Arrays.copyOf(hasRange, sz);
            }
            if (section.equals("RHS")) {
              rhs[i] = v;
            } else {
              range[i] = v;
              hasRange[i] = true;
            }
          }
        }
        case "BOUNDS" -> {
          String type = tok[0].toUpperCase();
          boolean noValue =
              type.equals("FR") || type.equals("MI") || type.equals("PL") || type.equals("BV");
          // type, optional bound set name, column, value
          String cn;
          double v = 0;
          if (noValue) {
            cn = tok.length >= 3 ? tok[2] : tok[1];
          } else if (tok.length >= 4) {
            cn = tok[2];
            v = number(tok[3], lineNo);
          } else {
            cn = tok[1];
            v = number(tok[2], lineNo);
          }
          Integer jj = colIndex.get(cn);
          if (jj == null) {
            throw new IOException("line " + lineNo + ": unknown column " + cn);
          }
          int j = jj;
          switch (type) {
            case "UP", "UI", "SC" -> {
              up[j] = v;
              upSet[j] = true;
              if (v < 0 && !loSet[j]) {
                lo[j] = Double.NEGATIVE_INFINITY;
              }
              if (type.equals("UI")) {
                colInteger.set(j, true);
              }
            }
            case "LO", "LI" -> {
              lo[j] = v;
              loSet[j] = true;
              if (type.equals("LI")) {
                colInteger.set(j, true);
              }
            }
            case "FX" -> {
              lo[j] = v;
              up[j] = v;
              loSet[j] = true;
              upSet[j] = true;
            }
            case "FR" -> {
              lo[j] = Double.NEGATIVE_INFINITY;
              up[j] = Double.POSITIVE_INFINITY;
              loSet[j] = true;
              upSet[j] = true;
            }
            case "MI" -> {
              lo[j] = Double.NEGATIVE_INFINITY;
              loSet[j] = true;
            }
            case "PL" -> {
              up[j] = Double.POSITIVE_INFINITY;
              upSet[j] = true;
            }
            case "BV" -> {
              lo[j] = 0;
              up[j] = 1;
              loSet[j] = true;
              upSet[j] = true;
              colInteger.set(j, true);
            }
            default -> throw new IOException("line " + lineNo + ": unknown bound type " + type);
          }
        }
        default -> {
          // other sections (RANGES of no rows, QUADOBJ, ...) are not supported
          if (!section.isEmpty() && !section.equals("NAME")) {
            throw new IOException("line " + lineNo + ": unsupported section " + section);
          }
        }
      }
    }
    int m = rowNames.size();
    int n = colNames.size();
    rhs = Arrays.copyOf(rhs, Math.max(rhs.length, m));
    range = Arrays.copyOf(range, Math.max(range.length, m));
    hasRange = Arrays.copyOf(hasRange, Math.max(hasRange.length, m));
    double[] rowLo = new double[m];
    double[] rowHi = new double[m];
    for (int i = 0; i < m; i++) {
      double b = rhs[i];
      double rg = Math.abs(range[i]);
      switch (rowType.get(i)) {
        case 'E' -> {
          if (hasRange[i]) {
            rowLo[i] = range[i] >= 0 ? b : b - rg;
            rowHi[i] = range[i] >= 0 ? b + rg : b;
          } else {
            rowLo[i] = b;
            rowHi[i] = b;
          }
        }
        case 'L' -> {
          rowLo[i] = hasRange[i] ? b - rg : Double.NEGATIVE_INFINITY;
          rowHi[i] = b;
        }
        case 'G' -> {
          rowLo[i] = b;
          rowHi[i] = hasRange[i] ? b + rg : Double.POSITIVE_INFINITY;
        }
        default ->
            throw new IOException("unknown row type " + rowType.get(i) + " of " + rowNames.get(i));
      }
    }
    double[] colLo = new double[n];
    double[] colHi = new double[n];
    boolean[] integer = new boolean[n];
    for (int j = 0; j < n; j++) {
      integer[j] = colInteger.get(j);
      colLo[j] = lo[j];
      // an integer column of the marker with no upper bound is binary in old MPS; here it is not
      colHi[j] = upSet[j] ? up[j] : Double.POSITIVE_INFINITY;
    }
    // the rows from the columns
    int[] count = new int[m];
    for (int j = 0; j < n; j++) {
      int[] cr = colRows.get(j);
      for (int e = 0; e < colLen.get(j); e++) {
        count[cr[e]]++;
      }
    }
    int[][] rowColumns = new int[m][];
    double[][] rowValues = new double[m][];
    for (int i = 0; i < m; i++) {
      rowColumns[i] = new int[count[i]];
      rowValues[i] = new double[count[i]];
    }
    Arrays.fill(count, 0);
    for (int j = 0; j < n; j++) {
      int[] cr = colRows.get(j);
      double[] cv = colVals.get(j);
      for (int e = 0; e < colLen.get(j); e++) {
        int i = cr[e];
        rowColumns[i][count[i]] = j;
        rowValues[i][count[i]++] = cv[e];
      }
    }
    return new LpProblem(
        name,
        colNames.toArray(new String[0]),
        rowNames.toArray(new String[0]),
        rowColumns,
        rowValues,
        rowLo,
        rowHi,
        colLo,
        colHi,
        Arrays.copyOf(cost, n),
        costConstant,
        maximize,
        integer);
  }

  private static double number(String s, int lineNo) throws IOException {
    try {
      return Double.parseDouble(s);
    } catch (NumberFormatException e) {
      throw new IOException("line " + lineNo + ": not a number: " + s, e);
    }
  }
}
