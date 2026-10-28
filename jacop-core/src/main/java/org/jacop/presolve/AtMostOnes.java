/*
 * AtMostOnes.java
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

package org.jacop.presolve;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Consumer;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearForms;
import org.jacop.constraints.LinearInt;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.LinearForm;

/**
 * Presolve rule: at-most-one extraction and clique merging (CP-SAT's {@code
 * ExtractAtMostOneFromLinear} and {@code TransformIntoMaxCliques}, the clique tables of MIP
 * presolvers).
 *
 * <p>Every linear constraint, clause and Boolean conjunction or disjunction with a fixed result is
 * read as a linear relation ({@link LinearForms}) and, written as {@code sum c_i * l_i + rest <=
 * slack} over literals {@code l_i} (a 0/1 variable or its negation) with positive costs, gives
 *
 * <ul>
 *   <li>an <em>at-most-one</em> over the literals of largest cost, as long as the two smallest of
 *       them cost more than the slack together, and
 *   <li>a <em>clause</em> (at least one literal false) when all literals together cost more than
 *       the slack.
 * </ul>
 *
 * <p>The at-most-ones are the cliques of a conflict graph on literals. Each is extended greedily to
 * a maximal clique of that graph, and the maximal cliques give three reductions:
 *
 * <ul>
 *   <li>a literal in conflict with both {@code x} and {@code not x} is false;
 *   <li>a clause whose literals are all in one clique makes the other literals of the clique false
 *       and is an exactly-one over its own literals;
 *   <li>a clique that contains at least two constraints which are nothing but at-most-ones (for
 *       example the pairwise clauses {@code not a \/ not b} of a decomposed at-most-one) replaces
 *       them by one constraint.
 * </ul>
 *
 * <p>Every constraint added is implied by the model, and every constraint dropped is implied by
 * those added, so the rule keeps all solutions. A run that finds literals false only fixes them, so
 * that the store propagates before the rule runs again.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class AtMostOnes {

  /**
   * What the rule did.
   *
   * @param atMostOnes at-most-ones found in the constraints (cliques of the conflict graph before
   *     merging).
   * @param cliques at-most-one constraints added, each replacing at least two constraints.
   * @param exactlyOnes exactly-one constraints added, each replacing a clause.
   * @param replaced constraints dropped because the added ones imply them.
   * @param fixed literals found false.
   */
  public record Statistics(int atMostOnes, int cliques, int exactlyOnes, int replaced, int fixed) {

    /**
     * Tells whether the rule changed the problem.
     *
     * @return true if it added or replaced a constraint or fixed a literal.
     */
    public boolean changed() {
      return cliques + exactlyOnes + replaced + fixed > 0;
    }

    /**
     * Adds the changes of a later run; the at-most-ones found are those of the run that found more.
     *
     * @param later the later run.
     * @return the sum.
     */
    public Statistics plus(Statistics later) {
      return new Statistics(
          Math.max(atMostOnes, later.atMostOnes),
          cliques + later.cliques,
          exactlyOnes + later.exactlyOnes,
          replaced + later.replaced,
          fixed + later.fixed);
    }
  }

  // operations on the conflict graph; once they are spent the rule keeps what it has found
  static final long DEFAULT_BUDGET = 50_000_000L;

  private final long budget;
  private long work;

  // literal 2i is variable i, literal 2i + 1 its negation
  private final Map<IntVar, Integer> ids = new IdentityHashMap<>();
  private final List<IntVar> vars = new ArrayList<>();

  /** A clique or a clause over literals, sorted; {@code equivalent} if it is the whole relation. */
  private static final class Part {
    final int[] lits;
    final boolean equivalent;

    Part(int[] lits, boolean equivalent) {
      this.lits = lits;
      this.equivalent = equivalent;
    }
  }

  /** One relation {@code <=} of a constraint: an equality gives two. */
  private record Form(Part atMostOne, Part clause) {}

  private record Source(Constraint c, List<Form> forms, boolean pure) {}

  private final List<Source> sources = new ArrayList<>();

  // the conflict graph as a list of cliques, and the cliques of every literal in increasing order
  private final List<int[]> cliques = new ArrayList<>();
  private final List<Source> cliqueSource = new ArrayList<>();
  private int[][] cliquesOf;
  private int[] cliquesOfSize;

  private final List<int[]> maximal = new ArrayList<>();
  private int[][] maximalOf;
  private int[] maximalOfSize;

  private boolean[] isFalse;
  private int falseCount;

  /** A constraint to add over sorted literals: at most one of them, or exactly one. */
  private static final class Addition {
    final int[] lits;
    final boolean exactlyOne;

    Addition(int[] lits, boolean exactlyOne) {
      this.lits = lits;
      this.exactlyOne = exactlyOne;
    }
  }

  private final List<Addition> added = new ArrayList<>();
  private int[][] addedOf;
  private int[] addedOfSize;

  private final List<Constraint> dropped = new ArrayList<>();
  private Statistics statistics = new Statistics(0, 0, 0, 0, 0);

  private AtMostOnes(long budget) {
    this.budget = budget;
  }

  private static AtMostOnes run(List<Constraint> constraints, long budget) {
    AtMostOnes r = new AtMostOnes(budget);
    for (Constraint c : constraints) {
      r.read(c);
    }
    int n = 2 * r.vars.size();
    r.cliquesOf = new int[n][];
    r.cliquesOfSize = new int[n];
    r.maximalOf = new int[n][];
    r.maximalOfSize = new int[n];
    r.addedOf = new int[n][];
    r.addedOfSize = new int[n];
    r.isFalse = new boolean[n];
    for (int i = 0; i < r.cliques.size(); i++) {
      for (int l : r.cliques.get(i)) {
        r.cliquesOf[l] = push(r.cliquesOf[l], r.cliquesOfSize[l]++, i);
      }
    }
    r.merge();
    r.findFalse();
    if (r.falseCount == 0) {
      r.replace();
    }
    r.statistics =
        new Statistics(
            r.cliques.size(),
            (int) r.added.stream().filter(a -> !a.exactlyOne).count(),
            (int) r.added.stream().filter(a -> a.exactlyOne).count(),
            r.dropped.size(),
            r.falseCount);
    return r;
  }

  /**
   * Applies the rule once to constraints of a store at a fixpoint. When it finds literals false it
   * only fixes them, so that the store propagates before the rule runs again; otherwise it imposes
   * its constraints and removes those they imply. Run again on its own result it changes nothing.
   *
   * @param store the store.
   * @param level the level at which literals are fixed.
   * @param constraints the constraints of the store to read, in a deterministic order.
   * @param impose imposes a constraint implied by the problem.
   * @param remove leaves out a constraint that the others imply.
   * @return what the rule did.
   * @throws org.jacop.core.FailException if the store has no solution.
   */
  public static Statistics apply(
      Store store,
      int level,
      List<Constraint> constraints,
      Consumer<Constraint> impose,
      Consumer<Constraint> remove) {
    return apply(store, level, constraints, impose, remove, DEFAULT_BUDGET);
  }

  static Statistics apply(
      Store store,
      int level,
      List<Constraint> constraints,
      Consumer<Constraint> impose,
      Consumer<Constraint> remove,
      long budget) {
    AtMostOnes r = run(constraints, budget);
    if (r.falseCount > 0) {
      for (int l = 0; l < r.isFalse.length; l++) {
        if (r.isFalse[l]) {
          // a variable is 0 when its literal fails, 1 when its negation fails
          IntVar v = r.vars.get(l >> 1);
          v.domain.in(level, v, l & 1, l & 1);
        }
      }
    } else {
      for (Addition a : r.added) {
        impose.accept(r.constraint(a.lits, a.exactlyOne));
      }
      for (Constraint c : r.dropped) {
        remove.accept(c);
      }
    }
    return r.statistics;
  }

  /** {@code sum positive + sum (1 - negative)} is at most one, or exactly one. */
  private Constraint constraint(int[] lits, boolean exactlyOne) {
    IntVar[] list = new IntVar[lits.length];
    int[] weights = new int[lits.length];
    int negative = 0;
    for (int i = 0; i < lits.length; i++) {
      list[i] = vars.get(lits[i] >> 1);
      weights[i] = (lits[i] & 1) == 0 ? 1 : -1;
      negative += lits[i] & 1;
    }
    return new LinearInt(list, weights, exactlyOne ? "==" : "<=", 1 - negative);
  }

  // ---------------------------------------------------------------- reading the constraints

  private void read(Constraint c) {
    LinearForm f = LinearForms.of(c);
    if (f == null || f.relation() == LinearForm.NE) {
      return;
    }
    // merge repeated variables and fold fixed ones into the right-hand side
    Map<IntVar, Integer> position = new IdentityHashMap<>();
    List<IntVar> order = new ArrayList<>();
    long[] weights = new long[f.vars().length];
    long rhs = f.c();
    try {
      for (int i = 0; i < f.vars().length; i++) {
        IntVar v = f.vars()[i];
        long w = f.weights()[i];
        if (v.singleton()) {
          rhs = Math.subtractExact(rhs, Math.multiplyExact(w, (long) v.value()));
        } else {
          Integer p = position.putIfAbsent(v, order.size());
          if (p == null) {
            weights[order.size()] = w;
            order.add(v);
          } else {
            weights[p] = Math.addExact(weights[p], w);
          }
        }
      }
      List<Form> forms = new ArrayList<>();
      if (f.relation() != LinearForm.GE) {
        Form le = form(order, weights, 1, rhs);
        if (le == null) {
          return;
        }
        forms.add(le);
      }
      if (f.relation() != LinearForm.LE) {
        Form ge = form(order, weights, -1, Math.negateExact(rhs));
        if (ge == null) {
          return;
        }
        forms.add(ge);
      }
      boolean pure = true;
      for (Form form : forms) {
        pure &=
            form.atMostOne != null && form.atMostOne.equivalent
                || form.clause != null && form.clause.equivalent;
      }
      Source source = new Source(c, forms, pure);
      sources.add(source);
      for (Form form : forms) {
        if (form.atMostOne != null) {
          cliques.add(form.atMostOne.lits);
          cliqueSource.add(source);
        }
      }
    } catch (ArithmeticException e) {
      // weights or bounds too large to reason on: the constraint is left alone
    }
  }

  /**
   * Reads {@code sign * sum w_i x_i <= rhs}, or returns null if it has no literal or no at-most-one
   * or clause.
   */
  private Form form(List<IntVar> order, long[] weights, int sign, long rhs) {
    int n = 0;
    long[] cost = new long[order.size()];
    int[] lit = new int[order.size()];
    long base = 0;
    boolean rest = false;
    for (int i = 0; i < order.size(); i++) {
      IntVar v = order.get(i);
      long w = Math.multiplyExact(sign, weights[i]);
      if (w == 0) {
        continue;
      }
      if (v.min() == 0 && v.max() == 1) {
        int id = ids.computeIfAbsent(v, x -> vars.size());
        if (id == vars.size()) {
          vars.add(v);
        }
        // a positive weight counts when the variable is 1, a negative one when it is 0
        lit[n] = w > 0 ? 2 * id : 2 * id + 1;
        cost[n] = w > 0 ? w : Math.negateExact(w);
        if (w < 0) {
          base = Math.addExact(base, w);
        }
        n++;
      } else {
        rest = true;
        base = Math.addExact(base, Math.multiplyExact(w, (long) (w > 0 ? v.min() : v.max())));
      }
    }
    if (n < 2) {
      return null;
    }
    long slack = Math.subtractExact(rhs, base);
    Integer[] byCost = new Integer[n];
    for (int i = 0; i < n; i++) {
      byCost[i] = i;
    }
    Arrays.sort(byCost, (i, j) -> Long.compare(cost[j], cost[i]));
    Part atMostOne = null;
    int k = 0;
    while (k + 1 < n && Math.addExact(cost[byCost[k]], cost[byCost[k + 1]]) > slack) {
      k++;
    }
    if (k > 0) {
      int[] lits = new int[k + 1];
      for (int i = 0; i <= k; i++) {
        lits[i] = lit[byCost[i]];
      }
      Arrays.sort(lits);
      atMostOne = new Part(lits, !rest && k + 1 == n);
    }
    Part clause = null;
    long total = 0;
    for (int i = 0; i < n; i++) {
      total = Math.addExact(total, cost[i]);
    }
    if (total > slack) {
      // not all literals can hold: at least one negation holds
      int[] lits = new int[n];
      for (int i = 0; i < n; i++) {
        lits[i] = lit[i] ^ 1;
      }
      Arrays.sort(lits);
      clause = new Part(lits, !rest && total - cost[byCost[n - 1]] <= slack);
    }
    return atMostOne == null && clause == null ? null : new Form(atMostOne, clause);
  }

  // ---------------------------------------------------------------- the conflict graph

  private static int[] push(int[] a, int size, int value) {
    if (a == null) {
      a = new int[4];
    } else if (size == a.length) {
      a = Arrays.copyOf(a, 2 * size);
    }
    a[size] = value;
    return a;
  }

  private boolean spent() {
    return work > budget;
  }

  /** Two different literals are adjacent if a clique contains both. */
  private boolean adjacent(int u, int v) {
    int[] a = cliquesOf[u];
    int[] b = cliquesOf[v];
    int na = cliquesOfSize[u];
    int nb = cliquesOfSize[v];
    int i = 0;
    int j = 0;
    while (i < na && j < nb) {
      work++;
      if (a[i] == b[j]) {
        return true;
      }
      if (a[i] < b[j]) {
        i++;
      } else {
        j++;
      }
    }
    return false;
  }

  /** Returns a maximal clique that contains all the literals, or -1. */
  private int maximalContaining(int[] lits) {
    int first = lits[0];
    for (int m = 0; m < maximalOfSize[first]; m++) {
      int[] q = maximal.get(maximalOf[first][m]);
      boolean all = true;
      for (int l : lits) {
        work++;
        if (Arrays.binarySearch(q, l) < 0) {
          all = false;
          break;
        }
      }
      if (all) {
        return maximalOf[first][m];
      }
    }
    return -1;
  }

  /** Extends every clique to a maximal clique, largest first, unless one already contains it. */
  private void merge() {
    Integer[] order = new Integer[cliques.size()];
    for (int i = 0; i < order.length; i++) {
      order[i] = i;
    }
    Arrays.sort(order, (i, j) -> Integer.compare(cliques.get(j).length, cliques.get(i).length));
    int[] mark = new int[cliquesOf.length];
    int stamp = 0;
    for (int i : order) {
      int[] s = cliques.get(i);
      if (maximalContaining(s) >= 0) {
        continue;
      }
      stamp++;
      for (int l : s) {
        mark[l] = stamp;
      }
      List<Integer> grown = new ArrayList<>();
      if (!spent()) {
        // candidates: the neighbours of the literal with the fewest, adjacent to the whole clique
        int pivot = s[0];
        long fewest = Long.MAX_VALUE;
        for (int l : s) {
          long degree = 0;
          for (int m = 0; m < cliquesOfSize[l]; m++) {
            degree += cliques.get(cliquesOf[l][m]).length;
          }
          if (degree < fewest) {
            fewest = degree;
            pivot = l;
          }
        }
        work += fewest;
        for (int m = 0; m < cliquesOfSize[pivot] && !spent(); m++) {
          for (int candidate : cliques.get(cliquesOf[pivot][m])) {
            if (mark[candidate] == stamp || spent()) {
              continue;
            }
            mark[candidate] = stamp;
            boolean all = true;
            for (int l : s) {
              if (!adjacent(candidate, l)) {
                all = false;
                break;
              }
            }
            for (int j = 0; all && j < grown.size(); j++) {
              all = adjacent(candidate, grown.get(j));
            }
            if (all) {
              grown.add(candidate);
            }
          }
        }
      }
      int[] q = Arrays.copyOf(s, s.length + grown.size());
      for (int j = 0; j < grown.size(); j++) {
        q[s.length + j] = grown.get(j);
      }
      Arrays.sort(q);
      int index = maximal.size();
      maximal.add(q);
      for (int l : q) {
        maximalOf[l] = push(maximalOf[l], maximalOfSize[l]++, index);
      }
    }
  }

  // ---------------------------------------------------------------- literals found false

  private void setFalse(int l) {
    if (!isFalse[l]) {
      isFalse[l] = true;
      falseCount++;
    }
  }

  private void findFalse() {
    // a literal adjacent to x and to not x
    int[] seen = new int[cliquesOf.length];
    Arrays.fill(seen, -1);
    for (int l = 0; l < cliquesOf.length && !spent(); l++) {
      for (int m = 0; m < cliquesOfSize[l]; m++) {
        for (int u : cliques.get(cliquesOf[l][m])) {
          work++;
          if (u != l) {
            seen[u] = l;
            if (seen[u ^ 1] == l) {
              setFalse(l);
            }
          }
        }
      }
    }
    // a clause inside a clique: one of its literals holds, so the other literals of the clique fail
    for (Source s : sources) {
      for (Form form : s.forms) {
        if (form.clause != null) {
          int q = maximalContaining(form.clause.lits);
          if (q >= 0) {
            for (int l : maximal.get(q)) {
              if (Arrays.binarySearch(form.clause.lits, l) < 0) {
                setFalse(l);
              }
            }
          }
        }
      }
    }
  }

  // ---------------------------------------------------------------- replacing constraints

  private void add(int[] lits, boolean exactlyOne) {
    int index = added.size();
    added.add(new Addition(lits, exactlyOne));
    for (int l : lits) {
      addedOf[l] = push(addedOf[l], addedOfSize[l]++, index);
    }
  }

  private void removeLastAdded() {
    int index = added.size() - 1;
    for (int l : added.remove(index).lits) {
      addedOfSize[l]--;
    }
  }

  /** An at-most-one is implied by an added constraint that contains its literals. */
  private boolean impliedAtMostOne(int[] lits) {
    int first = lits[0];
    for (int m = 0; m < addedOfSize[first]; m++) {
      int[] a = added.get(addedOf[first][m]).lits;
      boolean all = true;
      for (int l : lits) {
        if (Arrays.binarySearch(a, l) < 0) {
          all = false;
          break;
        }
      }
      if (all) {
        return true;
      }
    }
    return lits.length == 2 && impliedClause(negated(lits), false);
  }

  /** A clause is implied by an added exactly-one over some of its literals. */
  private boolean impliedClause(int[] lits, boolean viaAtMostOne) {
    for (int l : lits) {
      for (int m = 0; m < addedOfSize[l]; m++) {
        int index = addedOf[l][m];
        if (added.get(index).exactlyOne) {
          boolean all = true;
          for (int u : added.get(index).lits) {
            if (Arrays.binarySearch(lits, u) < 0) {
              all = false;
              break;
            }
          }
          if (all) {
            return true;
          }
        }
      }
    }
    if (viaAtMostOne && lits.length == 2) {
      return impliedAtMostOne(negated(lits));
    }
    return false;
  }

  private boolean implied(Source s) {
    if (!s.pure) {
      return false;
    }
    for (Form form : s.forms) {
      boolean holds =
          form.atMostOne != null
                  && form.atMostOne.equivalent
                  && impliedAtMostOne(form.atMostOne.lits)
              || form.clause != null
                  && form.clause.equivalent
                  && impliedClause(form.clause.lits, true);
      if (!holds) {
        return false;
      }
    }
    return true;
  }

  private void replace() {
    // exactly-ones: a clause that is the whole relation of a constraint and lies inside a clique
    for (Source s : sources) {
      if (!s.pure) {
        continue;
      }
      for (Form form : s.forms) {
        if (form.clause == null || !form.clause.equivalent || form.clause.lits.length < 2) {
          continue;
        }
        if (maximalContaining(form.clause.lits) < 0) {
          continue;
        }
        if (alreadyExactlyOne(s, form.clause.lits)
            || impliedClause(form.clause.lits, false)
            || form.clause.lits.length == 2 && impliedClause(negated(form.clause.lits), false)) {
          // an exactly-one over two literals is also one over their negations
          continue;
        }
        add(form.clause.lits, true);
      }
    }
    // cliques that imply two or more constraints; the candidates are the pure constraints with an
    // at-most-one on a literal of the clique
    Set<Source> seen = Collections.newSetFromMap(new IdentityHashMap<>());
    for (int[] q : maximal) {
      seen.clear();
      List<Source> candidates = new ArrayList<>();
      for (int l : q) {
        for (int m = 0; m < cliquesOfSize[l]; m++) {
          Source s = cliqueSource.get(cliquesOf[l][m]);
          if (s.pure && seen.add(s) && inside(s, q) && !implied(s)) {
            candidates.add(s);
          }
        }
      }
      if (candidates.size() < 2) {
        continue;
      }
      add(q, false);
      if (candidates.stream().filter(this::implied).count() < 2) {
        removeLastAdded();
      }
    }
    for (Source s : sources) {
      if (implied(s)) {
        dropped.add(s.c);
      }
    }
  }

  // a constraint whose at-most-ones all lie inside the clique
  private boolean inside(Source s, int[] q) {
    boolean any = false;
    for (Form form : s.forms) {
      if (form.atMostOne != null) {
        for (int l : form.atMostOne.lits) {
          if (Arrays.binarySearch(q, l) < 0) {
            return false;
          }
        }
        any = true;
      }
    }
    return any;
  }

  private static int[] negated(int[] lits) {
    int[] result = new int[lits.length];
    for (int i = 0; i < lits.length; i++) {
      result[i] = lits[i] ^ 1;
    }
    Arrays.sort(result);
    return result;
  }

  // the constraint is itself an exactly-one over these literals
  private static boolean alreadyExactlyOne(Source s, int[] lits) {
    for (Form form : s.forms) {
      if (form.atMostOne != null
          && form.atMostOne.equivalent
          && Arrays.equals(form.atMostOne.lits, lits)) {
        return true;
      }
    }
    return false;
  }
}
