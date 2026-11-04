/*
 * RupChecker.java
 * <p>
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

package org.jacop.jasat.lcg;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * A small checker of the VeriPB subset that {@link VeriPbProof} writes, for tests: the OPB model
 * with right implications and an objective, and the rules rup, pol (with +, literal axioms, and
 * multiplication and division by scalars), red (for constraints whose witness only changes
 * variables outside the objective), soli, sol, del id, f and the conclusions. A rup step passes
 * when unit propagation over the database and the step's negation fails, as in VeriPB.
 */
final class RupChecker {

  // a normalised constraint: literals (name, or ~name) with positive coefficients, and its degree
  private record Pb(Map<String, Long> terms, long degree) {}

  private final Map<Long, Pb> db = new LinkedHashMap<>();
  private final Map<String, List<Long>> occurrences = new HashMap<>();
  // the constraints that propagate or fail with no literal assigned, where propagation starts
  private final Set<Long> eager = new LinkedHashSet<>();
  private long lastId;
  private List<Object[]> objective;
  private long objectiveConstant;
  private Long best;
  private int solutions;

  /** Rup steps checked. */
  int steps;

  /** The conclusion of the proof. */
  String conclusion;

  private static final Pattern INEQUALITY = Pattern.compile("(.*?)(>=|=)\\s*(-?\\d+)");

  /**
   * Checks a proof against its model.
   *
   * @return null when the proof checks, else the first problem
   */
  String check(String opb, String pbp) {
    long loaded = 0;
    for (String raw : opb.split("\n")) {
      String line = raw.strip();
      if (line.isEmpty() || line.startsWith("*")) {
        continue;
      }
      String body = line.substring(0, line.length() - 1).strip();
      if (body.startsWith("min:")) {
        objective = new ArrayList<>();
        String[] t = body.substring(4).strip().split("\\s+");
        int n = t.length % 2 == 1 ? t.length - 1 : t.length;
        for (int k = 0; k < n; k += 2) {
          objective.add(new Object[] {Long.parseLong(t[k]), t[k + 1]});
        }
        objectiveConstant = t.length % 2 == 1 ? Long.parseLong(t[t.length - 1]) : 0;
        continue;
      }
      String[] guard = new String[0];
      int arrow = body.indexOf("==>");
      if (arrow >= 0) {
        guard = body.substring(0, arrow).strip().split("\\s+");
        body = body.substring(arrow + 3).strip();
      }
      Matcher m = INEQUALITY.matcher(body);
      if (!m.matches()) {
        return "bad constraint " + line;
      }
      List<Object[]> terms = terms(m.group(1));
      long rhs = Long.parseLong(m.group(3));
      List<Pb> cs = new ArrayList<>();
      cs.add(normalise(terms, rhs));
      if (m.group(2).equals("=")) {
        List<Object[]> negated = new ArrayList<>();
        for (Object[] t : terms) {
          negated.add(new Object[] {-(Long) t[0], t[1]});
        }
        cs.add(normalise(negated, -rhs));
      }
      for (Pb c : cs) {
        if (guard.length > 0 && c.degree() > 0) {
          List<Object[]> t = new ArrayList<>();
          c.terms().forEach((l, a) -> t.add(new Object[] {a, l}));
          for (String g : guard) {
            t.add(new Object[] {c.degree(), negate(g)});
          }
          c = normalise(t, c.degree());
        }
        add(c);
        loaded++;
      }
    }
    String[] statements = pbp.split(";");
    String header = "pseudo-Boolean proof version 3.0";
    if (!statements[0].strip().startsWith(header)) {
      return "no header";
    }
    statements[0] = statements[0].strip().substring(header.length());
    for (String raw : statements) {
      StringBuilder sb = new StringBuilder();
      for (String l : raw.split("\n")) {
        if (!l.strip().startsWith("%")) {
          sb.append(l).append(' ');
        }
      }
      String st = sb.toString().strip();
      if (st.isEmpty()) {
        continue;
      }
      int space = st.indexOf(' ');
      String rule = space < 0 ? st : st.substring(0, space);
      String rest = space < 0 ? "" : st.substring(space + 1).strip();
      switch (rule) {
        case "f" -> {
          if (Long.parseLong(rest) != loaded) {
            return "f " + rest + " but " + loaded + " constraints";
          }
        }
        case "rup" -> {
          Matcher m = INEQUALITY.matcher(rest);
          if (!m.matches()) {
            return "bad step " + st;
          }
          Pb c = normalise(terms(m.group(1)), Long.parseLong(m.group(3)));
          Map<String, Long> neg = new HashMap<>();
          long sum = 0;
          for (Map.Entry<String, Long> e : c.terms().entrySet()) {
            neg.put(negate(e.getKey()), e.getValue());
            sum += e.getValue();
          }
          if (propagate(new Pb(neg, sum - c.degree() + 1), new HashMap<>()) != null) {
            return "rup step " + (steps + 1) + " fails: " + st;
          }
          add(c);
          steps++;
        }
        case "pol" -> {
          // postfix: constraint ids, literal axioms (l >= 0), "+", and "k *" and "k d" by scalars
          Deque<Pb> stack = new ArrayDeque<>();
          String[] tokens = rest.split("\\s+");
          for (int k = 0; k < tokens.length; k++) {
            String t = tokens[k];
            if (t.equals("+")) {
              Pb b = stack.pop();
              Pb a = stack.pop();
              List<Object[]> sum = new ArrayList<>();
              for (Pb c : List.of(a, b)) {
                for (Map.Entry<String, Long> e : c.terms().entrySet()) {
                  sum.add(new Object[] {e.getValue(), e.getKey()});
                }
              }
              stack.push(normalise(sum, a.degree() + b.degree()));
            } else if (k + 1 < tokens.length
                && (tokens[k + 1].equals("*") || tokens[k + 1].equals("d"))) {
              long scalar = Long.parseLong(t);
              boolean divide = tokens[++k].equals("d");
              Pb c = stack.pop();
              Map<String, Long> scaled = new LinkedHashMap<>();
              c.terms()
                  .forEach((l, a) -> scaled.put(l, divide ? Math.ceilDiv(a, scalar) : a * scalar));
              long degree = Math.max(0, c.degree());
              stack.push(new Pb(scaled, divide ? Math.ceilDiv(degree, scalar) : degree * scalar));
            } else if (Character.isDigit(t.charAt(0))) {
              Pb c = db.get(Long.parseLong(t));
              if (c == null) {
                return "pol on a missing constraint: " + st;
              }
              stack.push(c);
            } else {
              stack.push(new Pb(Map.of(t, 1L), 0));
            }
          }
          if (stack.size() != 1) {
            return "bad step " + st;
          }
          add(stack.pop());
          steps++;
        }
        case "red" -> {
          String problem = redundant(rest);
          if (problem != null) {
            return "red step " + (steps + 1) + " fails, " + problem + ": " + st;
          }
          steps++;
        }
        case "soli", "sol" -> {
          Map<String, Boolean> value = new HashMap<>();
          for (String l : rest.split("\\s+")) {
            value.put(l.replace("~", ""), !l.startsWith("~"));
          }
          if (propagate(null, value) == null) {
            return "the solution propagates to a conflict";
          }
          for (Map.Entry<Long, Pb> e : db.entrySet()) {
            if (slack(e.getValue(), value, true) < 0) {
              return "the solution violates constraint " + e.getKey();
            }
          }
          solutions++;
          if (objective != null) {
            long f = objectiveConstant;
            for (Object[] t : objective) {
              Boolean v = truth((String) t[1], value);
              if (v == null) {
                return "the objective is not fixed";
              }
              f += v ? (Long) t[0] : 0;
            }
            best = best == null ? f : Math.min(best, f);
            if (rule.equals("soli")) {
              List<Object[]> t = new ArrayList<>();
              for (Object[] o : objective) {
                t.add(new Object[] {-(Long) o[0], o[1]});
              }
              add(normalise(t, -(f - 1 - objectiveConstant)));
            }
          }
        }
        case "del" -> {
          String[] ids = rest.split("\\s+");
          for (int k = 1; k < ids.length; k++) {
            eager.remove(Long.parseLong(ids[k]));
            Pb c = db.remove(Long.parseLong(ids[k]));
            if (c == null) {
              return "deleting a missing constraint " + ids[k];
            }
          }
        }
        case "output" -> {
          // NONE
        }
        case "conclusion" -> {
          conclusion = rest;
          String[] p = rest.split("\\s+");
          boolean contradiction =
              db.values().stream()
                  .anyMatch(
                      c ->
                          c.terms().values().stream().mapToLong(Long::longValue).sum()
                              < c.degree());
          switch (p[0]) {
            case "UNSAT" -> {
              if (!contradiction) {
                return "UNSAT without a contradiction";
              }
            }
            case "SAT" -> {
              if (solutions == 0) {
                return "SAT without a solution";
              }
            }
            case "BOUNDS" -> {
              if (p.length == 5 && p[2].equals(":")) {
                // a lower bound stated by a constraint over the objective's literals
                String problem = lowerBound(Long.parseLong(p[1]), Long.parseLong(p[3]));
                if (problem != null) {
                  return problem;
                }
                conclusion = "BOUNDS " + p[1] + " " + p[4];
                p = conclusion.split("\\s+");
              } else if (!contradiction) {
                return "no contradiction for the lower bound";
              }
              if (!p[2].equals("INF") && (best == null || best > Long.parseLong(p[2]))) {
                return "no solution of value " + p[2];
              }
            }
            default -> {
              // NONE
            }
          }
        }
        case "end" -> {
          return conclusion == null ? "no conclusion" : null;
        }
        default -> {
          return "unknown rule " + rule;
        }
      }
    }
    return "no end";
  }

  /**
   * Checks a red step {@code C : x -> v ...} and adds C: C and each constraint of the database on
   * the witness's variables, under the witness, must be satisfied or follow by unit propagation
   * from the database and the negation of C. The witness may not change the objective.
   */
  private String redundant(String step) {
    int colon = step.indexOf(':');
    if (colon < 0) {
      return "no witness";
    }
    Matcher m = INEQUALITY.matcher(step.substring(0, colon).strip());
    if (!m.matches()) {
      return "bad constraint";
    }
    Pb c = normalise(terms(m.group(1)), Long.parseLong(m.group(3)));
    Map<String, Boolean> witness = new HashMap<>();
    String[] w = step.substring(colon + 1).strip().split("\\s+");
    for (int k = 0; k + 2 < w.length; k += 3) {
      if (!w[k + 1].equals("->")) {
        return "bad witness";
      }
      witness.put(w[k], w[k + 2].equals("1"));
    }
    for (Object[] t : objective == null ? List.<Object[]>of() : objective) {
      if (witness.containsKey(((String) t[1]).replace("~", ""))) {
        return "the witness changes the objective";
      }
    }
    Map<String, Long> neg = new HashMap<>();
    long sum = 0;
    for (Map.Entry<String, Long> e : c.terms().entrySet()) {
      neg.put(negate(e.getKey()), e.getValue());
      sum += e.getValue();
    }
    Pb negation = new Pb(neg, sum - c.degree() + 1);
    List<Pb> goals = new ArrayList<>();
    goals.add(c);
    for (String x : witness.keySet()) {
      for (String l : List.of(x, "~" + x)) {
        for (long id : occurrences.getOrDefault(l, List.of())) {
          Pb d = db.get(id);
          if (d != null) {
            goals.add(d);
          }
        }
      }
    }
    db.put(-1L, negation);
    eager.add(-1L);
    for (String l : negation.terms().keySet()) {
      occurrences.computeIfAbsent(l, k -> new ArrayList<>()).add(-1L);
    }
    try {
      for (Pb d : goals) {
        // d under the witness
        Map<String, Long> terms = new HashMap<>();
        long degree = d.degree();
        for (Map.Entry<String, Long> e : d.terms().entrySet()) {
          Boolean v = truth(e.getKey(), witness);
          if (v == null) {
            terms.put(e.getKey(), e.getValue());
          } else if (v) {
            degree -= e.getValue();
          }
        }
        if (degree <= 0 || implies(negation, terms, degree)) {
          continue;
        }
        Map<String, Long> goalNegation = new HashMap<>();
        long total = 0;
        for (Map.Entry<String, Long> e : terms.entrySet()) {
          goalNegation.put(negate(e.getKey()), e.getValue());
          total += e.getValue();
        }
        Pb extra = new Pb(goalNegation, total - degree + 1);
        if (propagate(extra, new HashMap<>()) != null) {
          return "a constraint under the witness does not follow";
        }
      }
    } finally {
      db.remove(-1L);
      eager.remove(-1L);
    }
    add(c);
    return null;
  }

  // whether h implies sum of terms >= degree by weakening: what h has beyond the terms is no more
  // than its degree is above the goal's, as VeriPB checks a red step's goals
  private static boolean implies(Pb h, Map<String, Long> terms, long degree) {
    long excess = 0;
    for (Map.Entry<String, Long> e : h.terms().entrySet()) {
      excess += Math.max(0, e.getValue() - terms.getOrDefault(e.getKey(), 0L));
    }
    return excess <= h.degree() - degree;
  }

  // whether the constraint of the id is the objective at least the bound
  private String lowerBound(long bound, long id) {
    Pb c = db.get(id);
    if (c == null || objective == null) {
      return "no constraint " + id + " for the lower bound";
    }
    List<Object[]> terms = new ArrayList<>();
    for (Object[] o : objective) {
      terms.add(new Object[] {o[0], o[1]});
    }
    Pb goal = normalise(terms, bound - objectiveConstant);
    if (!c.terms().equals(goal.terms()) || c.degree() < goal.degree()) {
      return "constraint " + id + " does not state the lower bound " + bound;
    }
    return null;
  }

  private void add(Pb c) {
    db.put(++lastId, c);
    long slack = slack(c, Map.of(), false);
    if (slack < 0 || c.terms().values().stream().anyMatch(a -> a > slack)) {
      eager.add(lastId);
    }
    for (String l : c.terms().keySet()) {
      occurrences.computeIfAbsent(l, k -> new ArrayList<>()).add(lastId);
    }
  }

  private static List<Object[]> terms(String s) {
    List<Object[]> out = new ArrayList<>();
    String[] t = s.strip().isEmpty() ? new String[0] : s.strip().split("\\s+");
    for (int k = 0; k < t.length; k += 2) {
      out.add(new Object[] {Long.parseLong(t[k]), t[k + 1]});
    }
    return out;
  }

  // sum terms >= rhs, normalised to positive coefficients over literals
  private static Pb normalise(List<Object[]> terms, long rhs) {
    Map<String, Long> coefficient = new LinkedHashMap<>();
    long constant = 0;
    for (Object[] t : terms) {
      long a = (Long) t[0];
      String l = (String) t[1];
      if (l.startsWith("~")) {
        constant += a;
        coefficient.merge(l.substring(1), -a, Long::sum);
      } else {
        coefficient.merge(l, a, Long::sum);
      }
    }
    long degree = rhs - constant;
    Map<String, Long> out = new LinkedHashMap<>();
    for (Map.Entry<String, Long> e : coefficient.entrySet()) {
      if (e.getValue() > 0) {
        out.put(e.getKey(), e.getValue());
      } else if (e.getValue() < 0) {
        out.put("~" + e.getKey(), -e.getValue());
        degree -= e.getValue();
      }
    }
    return new Pb(out, degree);
  }

  private static String negate(String l) {
    return l.startsWith("~") ? l.substring(1) : "~" + l;
  }

  private static Boolean truth(String l, Map<String, Boolean> value) {
    Boolean v = value.get(l.replace("~", ""));
    return v == null ? null : v != l.startsWith("~");
  }

  // the most the satisfied and open literals give above the degree; with satisfied, only the
  // literals true count
  private static long slack(Pb c, Map<String, Boolean> value, boolean satisfied) {
    long s = -c.degree();
    for (Map.Entry<String, Long> e : c.terms().entrySet()) {
      Boolean v = truth(e.getKey(), value);
      if (satisfied ? Boolean.TRUE.equals(v) : !Boolean.FALSE.equals(v)) {
        s += e.getValue();
      }
    }
    return s;
  }

  /**
   * Unit propagation over the database and an extra constraint from the given values.
   *
   * @return the values at the fixpoint, or null on a conflict
   */
  private Map<String, Boolean> propagate(Pb extra, Map<String, Boolean> value) {
    // a constraint that does not propagate at first waits for a literal of its to be falsified;
    // given values, every constraint may
    ArrayDeque<Long> queue = new ArrayDeque<>(value.isEmpty() ? eager : db.keySet());
    if (extra != null) {
      queue.add(0L);
    }
    ArrayDeque<String> trail = new ArrayDeque<>();
    while (true) {
      while (!queue.isEmpty()) {
        long id = queue.poll();
        Pb c = id == 0 ? extra : db.get(id);
        if (c == null) {
          continue;
        }
        long s = slack(c, value, false);
        if (s < 0) {
          return null;
        }
        for (Map.Entry<String, Long> e : c.terms().entrySet()) {
          if (e.getValue() > s && truth(e.getKey(), value) == null) {
            String l = e.getKey();
            value.put(l.replace("~", ""), !l.startsWith("~"));
            trail.add(l);
          }
        }
      }
      if (trail.isEmpty()) {
        return value;
      }
      String falsified = negate(trail.poll());
      queue.addAll(occurrences.getOrDefault(falsified, List.of()));
      if (extra != null && extra.terms().containsKey(falsified)) {
        queue.add(0L);
      }
    }
  }
}
