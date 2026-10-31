/*
 * VariableEliminationTest.java
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
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.AndBoolSimple;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.ElementInteger;
import org.jacop.constraints.Implies;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.LinearIntDom;
import org.jacop.constraints.Max;
import org.jacop.constraints.OrBoolVector;
import org.jacop.constraints.Reified;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XorBool;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainRandom;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.junit.jupiter.api.Test;

/**
 * Presolve rule 8, variable elimination: which variables it eliminates, and on random small models
 * that every solution through presolve, with the eliminated variables given values by postsolve, is
 * a solution of the original model, and that the solutions projected on the kept variables are the
 * same.
 */
class VariableEliminationTest {

  private static final int TRIALS = Integer.getInteger("presolve.elimination.trials", 2000);

  private static final String[] RELATIONS = {"==", "!=", "<", "<=", ">", ">="};

  @Test
  void eliminationOnAChainOfEqualitiesKeepsTheModel() {
    Store store = new Store();
    IntVar x0 = new IntVar(store, "x0", 0, 1);
    IntVar x1 = new IntVar(store, "x1", 0, 1);
    IntVar x2 = new IntVar(store, "x2", 0, 11);
    IntVar x3 = new IntVar(store, "x3", 0, 2);
    IntVar x4 = new IntVar(store, "x4", 1, 1);
    IntVar x5 = new IntVar(store, "x5", 1, 12);
    IntVar z = new IntVar(store, "z", -20, 20);
    store.impose(new LinearInt(new IntVar[] {x0, z}, new int[] {1, -2}, "<", -1));
    store.impose(new XplusYlteqZ(x1, x2, x5));
    store.impose(new XeqY(x3, x2));
    store.impose(new XplusYeqZ(x4, x5, z));
    store.impose(new XeqY(x3, x5));
    IntVar[] all = {x0, x1, x2, x3, x4, x5, z};

    Derivation d =
        Presolver.of(store).keep(x0, x1, x2).solutionPreserving(false).checking(true).presolve();

    Set<List<Integer>> found = new HashSet<>();
    System.err.println(
        "CHILD "
            + d.child()
            + " entries "
            + Arrays.stream(all).map(v -> v.id() + ":" + d.entry(v)).toList());
    search(
        d.child(),
        d.counterparts(all),
        0,
        () -> {
          assertThat(d.returnSolution()).isTrue();
          found.add(values(new IntVar[] {x0, x1, x2}));
        });
    assertThat(found)
        .containsExactlyInAnyOrder(
            List.of(0, 0, 1), List.of(0, 0, 2), List.of(1, 0, 1), List.of(1, 0, 2));
  }

  @Test
  void aDefinedVariableIsEliminatedWithItsDefinition() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    IntVar y = new IntVar(store, "y", 0, 3);
    IntVar z = new IntVar(store, "z", 0, 10);
    store.impose(new XplusYeqZ(x, y, z));
    store.impose(new XltY(x, y));

    Derivation d = Presolver.of(store).keep(x, y).presolve();

    assertThat(d.entry(z)).isInstanceOf(Entry.Eliminated.class);
    assertThat(d.get(z)).isNull();
    assertThat(d.statistics().childConstraints()).isEqualTo(1);
    assertThat(d.eliminated()).isEqualTo(1);
    // postsolve computes z
    IntVar[] kept = d.counterparts(new IntVar[] {x, y});
    kept[0].domain.in(0, kept[0], 1, 1);
    kept[1].domain.in(0, kept[1], 3, 3);
    assertThat(d.returnSolution()).isTrue();
    assertThat(z.value()).isEqualTo(4);
  }

  @Test
  void aDefinedVariableWhoseDomainRestrictsTheSumIsKept() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    IntVar y = new IntVar(store, "y", 0, 3);
    IntVar z = new IntVar(store, "z", 0, 4);
    store.impose(new XplusYeqZ(x, y, z));

    Derivation d = Presolver.of(store).keep(x, y).presolve();

    assertThat(d.entry(z)).isInstanceOf(Entry.Kept.class);
    assertThat(d.eliminated()).isZero();
  }

  @Test
  void withoutKeptVariablesNothingIsEliminated() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    IntVar y = new IntVar(store, "y", 0, 3);
    IntVar z = new IntVar(store, "z", 0, 10);
    store.impose(new XplusYeqZ(x, y, z));

    Derivation d = Presolver.of(store).presolve();

    assertThat(d.entry(z)).isInstanceOf(Entry.Kept.class);
  }

  @Test
  void aChainOfDefinitionsIsEliminated() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    IntVar y = new IntVar(store, "y", 0, 3);
    IntVar w = new IntVar(store, "w", 0, 3);
    IntVar z1 = new IntVar(store, "z1", -100, 100);
    IntVar z2 = new IntVar(store, "z2", -100, 100);
    store.impose(new XplusYeqZ(x, y, z1));
    store.impose(new XplusYeqZ(z1, w, z2));

    Derivation d = Presolver.of(store).keep(x, y, w).presolve();

    assertThat(d.eliminated()).isEqualTo(2);
    IntVar[] kept = d.counterparts(new IntVar[] {x, y, w});
    for (IntVar k : kept) {
      k.domain.in(0, k, 2, 2);
    }
    assertThat(d.returnSolution()).isTrue();
    assertThat(z1.value()).isEqualTo(4);
    assertThat(z2.value()).isEqualTo(6);
  }

  @Test
  void aDefinedVariableIsSubstitutedIntoItsOnlyOtherConstraint() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    IntVar y = new IntVar(store, "y", 0, 3);
    IntVar w = new IntVar(store, "w", 0, 8);
    IntVar z = new IntVar(store, "z", -100, 100);
    store.impose(new XplusYeqZ(x, y, z));
    store.impose(new LinearInt(new IntVar[] {z, w}, new int[] {1, -1}, "<=", 2));

    Derivation d = Presolver.of(store).keep(x, y, w).presolve();

    assertThat(d.entry(z)).isInstanceOf(Entry.Eliminated.class);
    assertThat(d.substitutions()).isEqualTo(1);
    assertThat(d.statistics().childConstraints()).isEqualTo(1);
  }

  @Test
  void withoutDoubletonsADefinedVariableIsKeptForItsOtherConstraint() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    IntVar y = new IntVar(store, "y", 0, 3);
    IntVar w = new IntVar(store, "w", 0, 8);
    IntVar z = new IntVar(store, "z", -100, 100);
    store.impose(new XplusYeqZ(x, y, z));
    store.impose(new LinearInt(new IntVar[] {z, w}, new int[] {1, -1}, "<=", 2));

    Derivation d = Presolver.of(store).keep(x, y, w).doubletons(false).presolve();

    assertThat(d.entry(z)).isInstanceOf(Entry.Kept.class);
    assertThat(d.substitutions()).isZero();
    assertThat(d.statistics().childConstraints()).isEqualTo(2);
  }

  @Test
  void aReificationWhoseBooleanIsUsedNowhereElseIsEliminated() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    IntVar y = new IntVar(store, "y", 0, 3);
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar c = new IntVar(store, "c", 0, 1);
    store.impose(new Reified(new XltY(x, y), b));
    store.impose(new Implies(c, new XeqC(x, 2)));

    Derivation d = Presolver.of(store).keep(x, y).solutionPreserving(false).presolve();

    // the reification cleanup may take them first and leave them free
    assertThat(d.entry(b)).isNotInstanceOf(Entry.Kept.class);
    assertThat(d.entry(c)).isNotInstanceOf(Entry.Kept.class);
    assertThat(d.statistics().childConstraints()).isZero();
  }

  /**
   * Keeping every solution, only variables the others determine are eliminated: the Boolean of a
   * reification, but not that of an implication, which can be 0 or 1 when the inner constraint
   * holds, nor a variable bounded by an inequality.
   */
  @Test
  void keepingEverySolutionEliminatesOnlyDefinedVariables() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 0, 3);
    IntVar y = new IntVar(store, "y", 0, 3);
    IntVar b = new IntVar(store, "b", 0, 1);
    IntVar c = new IntVar(store, "c", 0, 1);
    IntVar z = new IntVar(store, "z", 0, 10);
    store.impose(new Reified(new XltY(x, y), b));
    store.impose(new Implies(c, new XeqC(x, 2)));
    store.impose(new LinearInt(new IntVar[] {x, z}, new int[] {1, -1}, "<=", 0));

    Derivation d = Presolver.of(store).keep(x, y).presolve();

    assertThat(d.entry(b)).isInstanceOf(Entry.Eliminated.class);
    assertThat(d.entry(c)).isInstanceOf(Entry.Kept.class);
    assertThat(d.entry(z)).isInstanceOf(Entry.Kept.class);
  }

  /** A channel forces its integer variable to the value whose Boolean is set. */
  @Test
  void aChannelledIntegerIsNotEliminated() {
    Store store = new Store();
    IntVar x = new IntVar(store, "x", 1, 1);
    x.addDom(3, 3);
    IntVar b1 = new IntVar(store, "b1", 0, 1);
    IntVar b3 = new IntVar(store, "b3", 0, 1);
    store.impose(new ChannelReif(x, new IntVar[] {b1, b3}, new int[] {1, 3}));

    Derivation d = Presolver.of(store).keep(b1, b3).presolve();

    assertThat(d.entry(x)).isInstanceOf(Entry.Kept.class);
  }

  /**
   * A variable merged with another by aliasing is still named by its constraints, where it stands
   * for the whole class: its only other constraint does not define it. Which variable of the class
   * stays depends on the order of the equation's arguments, so the model is built several times.
   */
  @Test
  void anAliasedVariableIsNotEliminated() {
    for (int i = 0; i < 20; i++) {
      Store store = new Store();
      IntVar x = new IntVar(store, "x", 0, 1);
      IntVar y = new IntVar(store, "y", 0, 1);
      IntVar z = new IntVar(store, "z", 0, 1);
      store.impose(new OrBoolVector(new IntVar[] {x, y}, x));
      store.impose(new XeqY(z, y));

      Derivation d = Presolver.of(store).keep(x, z).presolve();

      assertThat(d.eliminated()).isZero();
      assertThat(d.entry(y)).isNotInstanceOf(Entry.Eliminated.class);
      d.discard();
    }
  }

  @Test
  void randomModelsHaveTheSameProjectedSolutionsWithElimination() {
    Random random = new Random(20261027);
    int eliminated = 0;
    int substituted = 0;
    for (int trial = 0; trial < TRIALS; trial++) {
      Model model = randomModel(random);
      boolean checking = trial % 2 == 0;
      boolean preserving = trial % 4 < 2;
      Store store = new Store();
      IntVar[] vars = model.build(store);
      IntVar[] kept = model.kept(vars);
      Set<List<Integer>> expected = new HashSet<>();
      if (store.consistency()) {
        search(store, vars, 0, () -> expected.add(values(kept)));
      }

      Store parent = new Store();
      IntVar[] pvars = model.build(parent);
      IntVar[] pkept = model.kept(pvars);
      Derivation d =
          Presolver.of(parent)
              .keep(pkept)
              .solutionPreserving(preserving)
              .checking(checking)
              .presolve();
      Set<List<Integer>> found = new HashSet<>();
      if (d.outcome() != Derivation.Outcome.INFEASIBLE) {
        eliminated += d.eliminated();
        substituted += d.substitutions();
        int t = trial;
        search(
            d.child(),
            d.counterparts(pvars),
            random.nextInt(),
            () -> {
              assertThat(d.returnSolution()).as("trial %d", t).isTrue();
              assertThat(isSolution(model, pvars))
                  .as("trial %d: %s %s", t, model, Arrays.toString(pvars))
                  .isTrue();
              found.add(values(pkept));
            });
        d.discard();
      }
      assertThat(found).as("trial %d, checking %b", trial, checking).isEqualTo(expected);
    }
    // the random models exercise both parts of the rule
    assertThat(eliminated).isGreaterThan(TRIALS / 4);
    assertThat(substituted).isGreaterThan(TRIALS / 100);
  }

  /**
   * Whether the values of the variables satisfy the model in a fresh store. A variable postsolve
   * leaves open (free, or half-reified) must have a value that completes them.
   */
  private static boolean isSolution(Model model, IntVar[] assigned) {
    Store store = new Store();
    IntVar[] vars = model.build(store);
    try {
      for (int i = 0; i < vars.length; i++) {
        if (assigned[i].singleton()) {
          vars[i].domain.in(0, vars[i], assigned[i].value(), assigned[i].value());
        }
      }
      if (!store.consistency()) {
        return false;
      }
    } catch (FailException e) {
      return false;
    }
    // a variable postsolve leaves open must have a value that completes the solution
    boolean[] found = {false};
    search(store, vars, 0, () -> found[0] = true);
    return found[0];
  }

  /** A random model: domains, which variables are kept, and the constraints from a seed. */
  private record Model(int[][] domains, boolean[] keep, long seed, int constraints) {

    IntVar[] build(Store store) {
      IntVar[] x = new IntVar[domains.length];
      for (int i = 0; i < x.length; i++) {
        x[i] = new IntVar(store, "x" + i, domains[i][0], domains[i][1]);
      }
      Random r = new Random(seed);
      for (int k = 0; k < constraints; k++) {
        store.impose(randomConstraint(r, x));
      }
      if (!r.nextBoolean()) {
        return x;
      }
      // a variable with a wide domain defined by a sum and used in one more linear constraint,
      // which rule 8 substitutes
      IntVar z = new IntVar(store, "z", -20, 20);
      IntVar[] terms = distinct(r, Arrays.copyOfRange(x, 2, x.length), 2);
      store.impose(new XplusYeqZ(terms[0], terms[1], z));
      IntVar w = x[r.nextInt(x.length)];
      int weight = r.nextInt(4) - 2;
      store.impose(
          new LinearInt(
              new IntVar[] {z, w},
              new int[] {weight >= 0 ? weight + 1 : weight, 1 + r.nextInt(2)},
              RELATIONS[r.nextInt(RELATIONS.length)],
              r.nextInt(5) - 2));
      IntVar[] all = Arrays.copyOf(x, x.length + 1);
      all[x.length] = z;
      return all;
    }

    IntVar[] kept(IntVar[] vars) {
      List<IntVar> result = new ArrayList<>();
      for (int i = 0; i < keep.length; i++) {
        if (keep[i]) {
          result.add(vars[i]);
        }
      }
      return result.toArray(new IntVar[0]);
    }

    @Override
    public String toString() {
      return "Model[domains="
          + Arrays.deepToString(domains)
          + ", keep="
          + Arrays.toString(keep)
          + ", seed="
          + seed
          + ", constraints="
          + constraints
          + "]";
    }
  }

  private static Model randomModel(Random random) {
    int n = 4 + random.nextInt(4);
    int[][] domains = new int[n][];
    boolean[] keep = new boolean[n];
    for (int i = 0; i < n; i++) {
      // the first variables are Boolean, for the reifications
      int min = i < 2 ? 0 : random.nextInt(3) - 1;
      int width = i < 2 ? 1 : random.nextInt(random.nextInt(4) == 0 ? 12 : 4);
      domains[i] = new int[] {min, min + width};
      keep[i] = random.nextInt(3) == 0;
    }
    return new Model(domains, keep, random.nextLong(), 1 + random.nextInt(4));
  }

  private static Constraint randomConstraint(Random r, IntVar[] x) {
    IntVar[] three = distinct(r, x, 3);
    IntVar a = three[0];
    IntVar c = three[1];
    IntVar d = three[2];
    IntVar b = x[r.nextInt(2)];
    return switch (r.nextInt(16)) {
      case 0 -> new XplusYeqZ(a, c, d);
      case 1 -> {
        IntVar[] vs = distinct(r, x, 2 + r.nextInt(2));
        int[] w = new int[vs.length];
        for (int i = 0; i < w.length; i++) {
          w[i] = r.nextInt(2) == 0 ? (r.nextBoolean() ? 1 : -1) : r.nextInt(5) - 2;
        }
        String rel = RELATIONS[r.nextInt(RELATIONS.length)];
        yield r.nextInt(4) == 0
            ? new LinearIntDom(vs, w, rel, r.nextInt(5) - 2)
            : new LinearInt(vs, w, rel, r.nextInt(5) - 2);
      }
      case 2 -> new XplusYlteqZ(a, c, d);
      case 3 -> new SumInt(new IntVar[] {a, c}, RELATIONS[r.nextInt(RELATIONS.length)], d);
      case 4 -> new XeqY(a, c);
      case 5 -> new Reified(new XltY(a, c), b);
      case 6 -> new Reified(new XeqC(a, r.nextInt(3) - 1), b);
      case 7 -> new Implies(b, new XeqC(a, r.nextInt(3) - 1));
      case 8 -> new ChannelReif(a, new IntVar[] {x[0], x[1]}, new int[] {0, 1});
      case 9 -> new AndBoolSimple(x[0], x[1], d.min() >= 0 && d.max() <= 1 ? d : x[0]);
      case 10 ->
          new OrBoolVector(new IntVar[] {x[0], x[1]}, a.min() >= 0 && a.max() <= 1 ? a : x[0]);
      case 11 -> new XorBool(new IntVar[] {x[0]}, x[1]);
      case 12 -> new XmulYeqZ(a, c, d);
      case 13 -> new AbsXeqY(a, c);
      case 14 -> new Max(new IntVar[] {a, c}, d);
      default -> new ElementInteger(a, new int[] {r.nextInt(3), r.nextInt(3), r.nextInt(3)}, c, -1);
    };
  }

  private static IntVar[] distinct(Random r, IntVar[] x, int k) {
    List<IntVar> pool = new ArrayList<>(Arrays.asList(x));
    IntVar[] result = new IntVar[Math.min(k, pool.size())];
    for (int i = 0; i < result.length; i++) {
      result[i] = pool.remove(r.nextInt(pool.size()));
    }
    return result;
  }

  private static List<Integer> values(IntVar[] vars) {
    return Arrays.stream(vars).map(IntVar::value).toList();
  }

  private static void search(Store store, IntVar[] vars, int seed, Runnable onSolution) {
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
    search.labeling(store, new SimpleSelect<>(vars, null, new IndomainRandom<>(seed)));
  }
}
