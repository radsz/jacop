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

package org.jacop.jasat.cdcl;

import java.util.Arrays;
import java.util.List;

/**
 * Checks a DRAT proof made only of RUP lemmas (the CDCL core never needs RAT). Each lemma must lead
 * to a conflict by unit propagation over the formula and the earlier lemmas once its literals are
 * negated, and the proof must derive the empty clause. Deletions are ignored, which keeps the check
 * sound (more clauses only make propagation stronger, and every kept clause is implied).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class RupChecker {

  private final int[][] watchLists;
  private final int[] watchCount;
  private int[][] clauses = new int[64][];
  private int numClauses;
  private final byte[] value; // per literal index: 1 true, -1 false
  private final int[] trail;
  private int trailSize;
  private int head;
  private boolean inconsistent;

  private RupChecker(int vars) {
    watchLists = new int[2 * vars + 2][];
    watchCount = new int[2 * vars + 2];
    value = new byte[2 * vars + 2];
    trail = new int[vars + 1];
  }

  /**
   * Checks a refutation.
   *
   * @param vars the number of variables
   * @param formula the clauses (DIMACS literals)
   * @param drat the proof in DRAT text format
   * @return null if the proof derives the empty clause by RUP steps, otherwise what is wrong
   */
  static String check(int vars, List<int[]> formula, String drat) {
    RupChecker c = new RupChecker(vars);
    for (int[] clause : formula) {
      c.add(clause);
    }
    int line = 0;
    for (String text : drat.split("\n")) {
      line++;
      text = text.strip();
      if (text.isEmpty() || text.startsWith("d")) {
        continue;
      }
      int[] lemma = Arrays.stream(text.split("\\s+")).mapToInt(Integer::parseInt).toArray();
      if (lemma[lemma.length - 1] != 0) {
        return "line " + line + " does not end with 0";
      }
      lemma = Arrays.copyOf(lemma, lemma.length - 1);
      if (!c.isRup(lemma)) {
        return "line " + line + " is not RUP: " + text;
      }
      if (lemma.length == 0) {
        return null;
      }
      c.add(lemma);
    }
    return c.inconsistent ? null : "the proof does not derive the empty clause";
  }

  private static int index(int lit) {
    return lit > 0 ? 2 * lit : 2 * -lit + 1;
  }

  private void add(int[] lits) {
    if (inconsistent) {
      return;
    }
    int[] c = Arrays.stream(lits).distinct().toArray();
    int n = 0;
    for (int l : c) {
      if (value[index(l)] > 0 || Arrays.stream(c).anyMatch(x -> x == -l)) {
        return; // satisfied at the root, or a tautology: it never propagates
      }
      if (value[index(l)] == 0) {
        c[n++] = l;
      }
    }
    c = Arrays.copyOf(c, n);
    if (n == 0) {
      inconsistent = true;
      return;
    }
    if (n == 1) {
      assign(c[0]);
      inconsistent = !propagate();
      return;
    }
    if (numClauses == clauses.length) {
      clauses = Arrays.copyOf(clauses, 2 * numClauses);
    }
    clauses[numClauses] = c;
    watch(c[0], numClauses);
    watch(c[1], numClauses);
    numClauses++;
  }

  private void watch(int lit, int clause) {
    int i = index(lit);
    if (watchLists[i] == null) {
      watchLists[i] = new int[4];
    } else if (watchCount[i] == watchLists[i].length) {
      watchLists[i] = Arrays.copyOf(watchLists[i], 2 * watchCount[i]);
    }
    watchLists[i][watchCount[i]++] = clause;
  }

  private void assign(int lit) {
    value[index(lit)] = 1;
    value[index(-lit)] = -1;
    trail[trailSize++] = lit;
  }

  /** Unit propagation from the trail head; false on a conflict. */
  private boolean propagate() {
    while (head < trailSize) {
      int falseLit = -trail[head++];
      int fi = index(falseLit);
      int[] ws = watchLists[fi];
      int n = watchCount[fi];
      int j = 0;
      for (int k = 0; k < n; k++) {
        int ci = ws[k];
        int[] c = clauses[ci];
        if (c[0] == falseLit) {
          c[0] = c[1];
          c[1] = falseLit;
        }
        if (value[index(c[0])] > 0) {
          ws[j++] = ci;
          continue;
        }
        boolean moved = false;
        for (int m = 2; m < c.length; m++) {
          if (value[index(c[m])] >= 0) {
            c[1] = c[m];
            c[m] = falseLit;
            watch(c[1], ci);
            moved = true;
            break;
          }
        }
        if (moved) {
          continue;
        }
        ws[j++] = ci;
        if (value[index(c[0])] < 0) {
          System.arraycopy(ws, k + 1, ws, j, n - k - 1);
          watchCount[fi] = j + n - k - 1;
          return false;
        }
        assign(c[0]);
      }
      watchCount[fi] = j;
    }
    return true;
  }

  private boolean isRup(int[] lemma) {
    if (inconsistent) {
      return true;
    }
    int saved = trailSize;
    boolean conflict = false;
    for (int l : lemma) {
      byte v = value[index(l)];
      if (v > 0) {
        conflict = true; // the lemma is true at the root, so its negation conflicts
        break;
      }
      if (v == 0) {
        assign(-l);
      }
    }
    if (!conflict) {
      conflict = !propagate();
    }
    while (trailSize > saved) {
      int l = trail[--trailSize];
      value[index(l)] = 0;
      value[index(-l)] = 0;
    }
    head = saved;
    return conflict;
  }
}
