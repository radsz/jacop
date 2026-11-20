/*
 * XcspOutput.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * preservation of specified reasonable legal notices and author attributions
 * in material modified versions of this work.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz.xcsp;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Turns the output of JaCoP's FlatZinc front end into the output format of the XCSP3 competition:
 * {@code o} lines for the objective of each solution, {@code s} for the status, {@code v} lines
 * with the instantiation of the (last) solution, and comments as {@code c} lines.
 */
final class XcspOutput extends OutputStream {

  /** How an XCSP3 variable's value reaches the output: a FlatZinc name and a position. */
  record Slot(String fzn, int position) {}

  private final PrintStream out;
  private final boolean optimization;
  private final List<String> ids;
  private final List<Slot> slots;
  private final Map<Integer, String[]> symbolsOf;
  private final String objectiveName;

  private final ByteArrayOutputStream line = new ByteArrayOutputStream();
  private final Map<String, String[]> current = new HashMap<>();
  private Map<String, String[]> last;
  private boolean finished;
  private long solutions;

  XcspOutput(
      PrintStream out,
      boolean optimization,
      List<String> ids,
      List<Slot> slots,
      Map<Integer, String[]> symbolsOf,
      String objectiveName) {
    this.out = out;
    this.optimization = optimization;
    this.ids = ids;
    this.slots = slots;
    this.symbolsOf = symbolsOf;
    this.objectiveName = objectiveName;
  }

  @Override
  public synchronized void write(int b) {
    if (b == '\n') {
      handle(line.toString(StandardCharsets.UTF_8));
      line.reset();
    } else if (b != '\r') {
      line.write(b);
    }
  }

  @Override
  public synchronized void write(byte[] b, int off, int len) {
    for (int i = off; i < off + len; i++) {
      write(b[i]);
    }
  }

  @Override
  public synchronized void flush() {
    out.flush();
  }

  private void handle(String l) {
    if (l.isEmpty()) {
      return;
    }
    if (finished) {
      if (l.startsWith("%")) {
        out.println("c " + l.substring(1).trim());
      }
      return;
    }
    switch (l) {
      case "----------" -> solution();
      case "==========" -> {
        if (optimization && last != null) {
          out.println("s OPTIMUM FOUND");
          values(last);
        } else if (last == null) {
          out.println("s UNSATISFIABLE");
        }
        finished = true;
      }
      case "=====UNSATISFIABLE=====" -> {
        out.println("s UNSATISFIABLE");
        finished = true;
      }
      case "=====UNKNOWN=====", "=====UNBOUNDED=====", "=====ERROR=====" -> {
        // the final status follows in finish()
      }
      default -> {
        if (l.startsWith("%")) {
          out.println("c " + l.substring(1).trim());
          return;
        }
        int eq = l.indexOf(" = ");
        if (eq > 0 && l.endsWith(";")) {
          String name = l.substring(0, eq);
          String value = l.substring(eq + 3, l.length() - 1).trim();
          current.put(name, parse(value));
          return;
        }
        out.println("c " + l);
      }
    }
    out.flush();
  }

  private static String[] parse(String value) {
    int open = value.indexOf('[');
    if (open >= 0) {
      String body = value.substring(open + 1, value.lastIndexOf(']'));
      String[] parts = body.isBlank() ? new String[0] : body.split(",");
      for (int i = 0; i < parts.length; i++) {
        parts[i] = number(parts[i].trim());
      }
      return parts;
    }
    return new String[] {number(value)};
  }

  private static String number(String v) {
    return switch (v) {
      case "true" -> "1";
      case "false" -> "0";
      default -> v;
    };
  }

  private void solution() {
    solutions++;
    last = new HashMap<>(current);
    if (optimization) {
      String[] o = current.get(objectiveName);
      if (o != null) {
        out.println("o " + o[0]);
      }
      return;
    }
    out.println("s SATISFIABLE");
    values(last);
    finished = true;
  }

  private void values(Map<String, String[]> sol) {
    StringBuilder list = new StringBuilder();
    StringBuilder vals = new StringBuilder();
    for (int i = 0; i < ids.size(); i++) {
      Slot s = slots.get(i);
      String[] v = sol.get(s.fzn());
      if (v == null || s.position() >= v.length) {
        continue;
      }
      list.append(' ').append(ids.get(i));
      String value = v[s.position()];
      String[] sym = symbolsOf.get(i);
      if (sym != null) {
        int k = Integer.parseInt(value);
        value = k >= 0 && k < sym.length ? sym[k] : value;
      }
      vals.append(' ').append(value);
    }
    out.println("v <instantiation type=\"solution\">");
    out.println("v   <list>" + list + " </list>");
    out.println("v   <values>" + vals + " </values>");
    out.println("v </instantiation>");
  }

  /** Prints the final status unless it is printed already. */
  synchronized void finish() {
    if (line.size() > 0) {
      handle(line.toString(StandardCharsets.UTF_8));
      line.reset();
    }
    if (finished) {
      out.flush();
      return;
    }
    finished = true;
    if (last != null) {
      out.println("s SATISFIABLE");
      values(last);
    } else {
      out.println("s UNKNOWN");
    }
    out.flush();
  }

  long solutions() {
    return solutions;
  }
}
