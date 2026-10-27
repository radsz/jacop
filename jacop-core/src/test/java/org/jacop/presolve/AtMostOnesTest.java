/*
 * AtMostOnesTest.java
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

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.Consumer;
import org.jacop.constraints.AndBoolSimple;
import org.jacop.constraints.AndBoolVector;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearBool;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.OrBoolSimple;
import org.jacop.constraints.OrBoolVector;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.api.Test;

/** The at-most-one rule: exact reductions on small models, and solution sets on random models. */
class AtMostOnesTest {

  private static final int TRIALS = Integer.getInteger("atmostones.trials", 600);

  private record Model(Store store, IntVar[] x, IntVar[] b) {}

  private static Model model(int booleans, Consumer<Model> impose) {
    Store store = new Store();
    IntVar[] b = new IntVar[booleans];
    for (int i = 0; i < booleans; i++) {
      b[i] = i % 2 == 0 ? new BooleanVar(store, "b" + i) : new IntVar(store, "b" + i, 0, 1);
    }
    IntVar[] x = {new IntVar(store, "x0", 0, 3), new IntVar(store, "x1", -1, 2)};
    Model m = new Model(store, x, b);
    impose.accept(m);
    return m;
  }

  private static Derivation derive(Model m) {
    Derivation d = Presolver.of(m.store()).keep(all(m)).checking(true).presolve();
    assertThat(d.outcome()).isEqualTo(Derivation.Outcome.DERIVED);
    return d;
  }

  @Test
  void pairwiseConflictsBecomeOneAtMostOne() {
    Model m =
        model(
            4,
            v -> {
              IntVar[] b = v.b();
              Store s = v.store();
              s.impose(new AndBoolSimple(b[0], b[1], new IntVar(s, 0, 0)));
              s.impose(new BoolClause(new IntVar[0], new IntVar[] {b[0], b[2]}));
              s.impose(new XplusYlteqZ(b[0], b[3], new IntVar(s, 1, 1)));
              s.impose(new SumBool(new IntVar[] {b[1], b[2]}, "<=", new IntVar(s, 1, 1)));
              s.impose(new LinearInt(new IntVar[] {b[1], b[3]}, new int[] {2, 3}, "<=", 4));
              s.impose(new AndBoolVector(new IntVar[] {b[2], b[3]}, new IntVar(s, 0, 0)));
            });
    Derivation d = derive(m);
    assertThat(d.atMostOnes().cliques()).isEqualTo(1);
    assertThat(d.atMostOnes().replaced()).isEqualTo(6);
    assertThat(d.statistics().childConstraints()).isEqualTo(1);
    // at most one of the four Booleans, and the two integers free
    assertThat(solutionsThrough(m, d)).hasSize(5 * 4 * 4);
  }

  @Test
  void aClauseInsideACliqueIsAnExactlyOneAndFixesTheRest() {
    // b0 + b1 + b2 <= 1 by pairs, and b0 \/ b1: so b2 = 0 and exactly one of b0, b1
    Model m =
        model(
            3,
            v -> {
              IntVar[] b = v.b();
              Store s = v.store();
              IntVar zero = new IntVar(s, 0, 0);
              s.impose(new AndBoolSimple(b[0], b[1], zero));
              s.impose(new AndBoolSimple(b[0], b[2], zero));
              s.impose(new AndBoolSimple(b[1], b[2], zero));
              s.impose(new OrBoolSimple(b[0], b[1], new IntVar(s, 1, 1)));
            });
    Derivation d = derive(m);
    assertThat(d.atMostOnes().fixed()).isEqualTo(1);
    assertThat(d.atMostOnes().exactlyOnes()).isEqualTo(1);
    assertThat(m.b()[2].singleton(0)).isTrue();
    assertThat(solutionsThrough(m, d)).hasSize(2 * 4 * 4);
  }

  @Test
  void aLiteralInConflictWithBothPolaritiesIsFalse() {
    // b0 + b1 <= 1 and b0 <= b1 (b0 + not b1 <= 1): b0 = 0
    Model m =
        model(
            2,
            v -> {
              v.store().impose(new XplusYlteqZ(v.b()[0], v.b()[1], new IntVar(v.store(), 1, 1)));
              v.store().impose(new XlteqY(v.b()[0], v.b()[1]));
            });
    Derivation d = derive(m);
    assertThat(d.atMostOnes().fixed()).isEqualTo(1);
    assertThat(m.b()[0].singleton(0)).isTrue();
  }

  @Test
  void anAtMostOneIsExtractedFromAWeightedLinearConstraint() {
    // 5 b0 + 4 b1 + 3 b2 + b3 + x0 <= 9 with x0 >= 1 leaves 8 for the Booleans, so b0 and b1
    // conflict (5 + 4 > 8) but b1 and b2 do not (4 + 3 <= 8); two clauses add the pairs b0-b2 and
    // b1-b2, and the three Booleans form one clique
    Consumer<Model> impose =
        v -> {
          IntVar[] b = v.b();
          Store s = v.store();
          v.x()[0].domain.in(0, v.x()[0], 1, 3);
          s.impose(
              new LinearInt(
                  new IntVar[] {b[0], b[1], b[2], b[3], v.x()[0]},
                  new int[] {5, 4, 3, 1, 1},
                  "<=",
                  9));
          s.impose(new BoolClause(new IntVar[0], new IntVar[] {b[1], b[2]}));
          s.impose(new BoolClause(new IntVar[0], new IntVar[] {b[0], b[2]}));
        };
    Model m = model(4, impose);
    Derivation d = derive(m);
    // the clique {b0, b1, b2} replaces the two clauses; the linear constraint stays
    assertThat(d.atMostOnes().cliques()).isEqualTo(1);
    assertThat(d.atMostOnes().replaced()).isEqualTo(2);
    assertThat(d.statistics().childConstraints()).isEqualTo(2);
    assertThat(solutionsThrough(m, d)).isEqualTo(solutionsDirectly(model(4, impose)));
  }

  @Test
  void runningTheRuleAgainChangesNothing() {
    Random random = new Random(7);
    for (int trial = 0; trial < 200; trial++) {
      long seed = random.nextLong();
      Model m = model(6, v -> randomModel(new Random(seed), v));
      Store s = m.store();
      if (!s.consistency()) {
        continue;
      }
      List<Constraint> removed = new ArrayList<>();
      AtMostOnes.Statistics first = null;
      boolean feasible = true;
      for (int round = 0; round < 10 && feasible; round++) {
        try {
          List<Constraint> live = live(s, removed);
          AtMostOnes.Statistics st = AtMostOnes.apply(s, s.level, live, s::impose, removed::add);
          feasible = s.consistency();
          if (!st.changed()) {
            first = st;
            break;
          }
        } catch (org.jacop.core.FailException e) {
          feasible = false;
        }
      }
      if (feasible) {
        assertThat(first).as("trial %d reaches a fixpoint", trial).isNotNull();
      }
    }
  }

  @Test
  void randomModelsHaveTheSameSolutionsWithTheRule() {
    Random random = new Random(20261027);
    int changed = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      long seed = random.nextLong();
      Set<List<Integer>> expected =
          solutionsDirectly(model(6, v -> randomModel(new Random(seed), v)));
      Model m = model(6, v -> randomModel(new Random(seed), v));
      Derivation d = Presolver.of(m.store()).keep(all(m)).checking(trial % 2 == 0).presolve();
      Set<List<Integer>> found =
          d.outcome() == Derivation.Outcome.INFEASIBLE ? Set.of() : solutionsThrough(m, d);
      assertThat(found).as("trial %d", trial).isEqualTo(expected);
      if (d.atMostOnes() != null && d.atMostOnes().changed()) {
        changed++;
      }
    }
    // the generator plants conflicts often enough for the rule to change most models
    assertThat(changed).isGreaterThan(TRIALS / 5);
  }

  private static void randomModel(Random r, Model v) {
    IntVar[] b = v.b();
    Store s = v.store();
    int constraints = 3 + r.nextInt(6);
    for (int k = 0; k < constraints; k++) {
      IntVar p = b[r.nextInt(b.length)];
      IntVar q = b[r.nextInt(b.length)];
      while (q == p) {
        q = b[r.nextInt(b.length)];
      }
      IntVar[] some = some(r, b, 2 + r.nextInt(3));
      switch (r.nextInt(12)) {
        case 0 -> s.impose(new AndBoolSimple(p, q, new IntVar(s, 0, 0)));
        case 1 -> s.impose(new OrBoolSimple(p, q, new IntVar(s, 1, 1)));
        case 2 -> s.impose(new BoolClause(new IntVar[0], new IntVar[] {p, q}));
        case 3 -> {
          int split = r.nextInt(some.length + 1);
          s.impose(
              new BoolClause(
                  Arrays.copyOfRange(some, 0, split),
                  Arrays.copyOfRange(some, split, some.length)));
        }
        case 4 -> s.impose(new OrBoolVector(some, new IntVar(s, 1, 1)));
        case 5 -> s.impose(new AndBoolVector(some, new IntVar(s, 0, 0)));
        case 6 -> s.impose(new SumBool(some, r.nextBoolean() ? "<=" : "==", new IntVar(s, 1, 1)));
        case 7 -> {
          int[] w = new int[some.length + 1];
          for (int i = 0; i < some.length; i++) {
            w[i] = r.nextInt(9) - 3;
          }
          w[some.length] = r.nextInt(3) - 1;
          IntVar[] list = Arrays.copyOf(some, some.length + 1);
          list[some.length] = v.x()[r.nextInt(2)];
          String[] rel = {"<=", ">=", "==", "<", ">"};
          s.impose(new LinearInt(list, w, rel[r.nextInt(rel.length)], r.nextInt(7) - 1));
        }
        case 8 -> {
          int[] w = new int[some.length];
          for (int i = 0; i < w.length; i++) {
            w[i] = 1 + r.nextInt(4);
          }
          s.impose(new LinearBool(some, w, r.nextBoolean() ? "<=" : ">=", 1 + r.nextInt(5)));
        }
        case 9 -> s.impose(new XlteqY(p, q));
        case 10 -> s.impose(new XneqY(p, q));
        default ->
            s.impose(
                new SumWeight(
                    new IntVar[] {p, q, v.x()[1]}, new int[] {2, 1 + r.nextInt(2), 1}, 2));
      }
    }
  }

  private static IntVar[] some(Random r, IntVar[] b, int k) {
    List<IntVar> pool = new ArrayList<>(Arrays.asList(b));
    IntVar[] result = new IntVar[Math.min(k, pool.size())];
    for (int i = 0; i < result.length; i++) {
      result[i] = pool.remove(r.nextInt(pool.size()));
    }
    return result;
  }

  private static List<Constraint> live(Store s, List<Constraint> removed) {
    List<Constraint> result = new ArrayList<>();
    Set<Constraint> seen = java.util.Collections.newSetFromMap(new java.util.IdentityHashMap<>());
    for (int i = 0; i < s.size(); i++) {
      for (Constraint c : s.vars[i].dom().constraints()) {
        if (!c.isEntailed() && seen.add(c) && !removed.contains(c)) {
          result.add(c);
        }
      }
    }
    for (var v : s.variablesHashMap.values()) {
      if (v.index() < 0) {
        for (Constraint c : v.dom().constraints()) {
          if (!c.isEntailed() && seen.add(c) && !removed.contains(c)) {
            result.add(c);
          }
        }
      }
    }
    return result;
  }

  private static IntVar[] all(Model m) {
    IntVar[] all = Arrays.copyOf(m.b(), m.b().length + m.x().length);
    System.arraycopy(m.x(), 0, all, m.b().length, m.x().length);
    return all;
  }

  private static Set<List<Integer>> solutionsDirectly(Model m) {
    Set<List<Integer>> found = new HashSet<>();
    if (!m.store().consistency()) {
      return found;
    }
    IntVar[] vars = all(m);
    search(m.store(), vars, () -> found.add(values(vars)));
    return found;
  }

  private static Set<List<Integer>> solutionsThrough(Model m, Derivation d) {
    Set<List<Integer>> found = new HashSet<>();
    IntVar[] vars = all(m);
    search(
        d.child(),
        d.counterparts(vars),
        () -> {
          if (d.returnSolution()) {
            found.add(values(vars));
          }
        });
    return found;
  }

  private static List<Integer> values(IntVar[] vars) {
    return Arrays.stream(vars).map(IntVar::value).toList();
  }

  private static void search(Store store, IntVar[] vars, Runnable onSolution) {
    if (vars.length == 0) {
      onSolution.run();
      return;
    }
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setSolutionListener(
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> select) {
            boolean result = super.executeAfterSolution(s, select);
            onSolution.run();
            return result;
          }
        });
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    search.labeling(store, new SimpleSelect<>(vars, null, new IndomainMin<>()));
  }
}
