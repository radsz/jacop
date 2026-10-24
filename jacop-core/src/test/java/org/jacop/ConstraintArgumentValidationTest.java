/*
 * ConstraintArgumentValidationTest.java
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatThrownBy;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;
import java.util.function.Predicate;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.AndBool;
import org.jacop.constraints.AndBoolSimple;
import org.jacop.constraints.AndBoolVector;
import org.jacop.constraints.ArgMax;
import org.jacop.constraints.ArgMin;
import org.jacop.constraints.Assignment;
import org.jacop.constraints.BoolClause;
import org.jacop.constraints.ChannelImply;
import org.jacop.constraints.ChannelReif;
import org.jacop.constraints.Conditional;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.CountBounds;
import org.jacop.constraints.CountValues;
import org.jacop.constraints.CountValuesBounds;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.Diff2;
import org.jacop.constraints.Disjoint;
import org.jacop.constraints.DisjointConditional;
import org.jacop.constraints.EqBool;
import org.jacop.constraints.ExtensionalConflictVa;
import org.jacop.constraints.ExtensionalSupportStr;
import org.jacop.constraints.ExtensionalSupportVa;
import org.jacop.constraints.IfThenBool;
import org.jacop.constraints.Implies;
import org.jacop.constraints.Lex;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.LinearIntDom;
import org.jacop.constraints.Not;
import org.jacop.constraints.OrBool;
import org.jacop.constraints.OrBoolSimple;
import org.jacop.constraints.OrBoolVector;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Rectangle;
import org.jacop.constraints.Reified;
import org.jacop.constraints.Sequence;
import org.jacop.constraints.Stretch;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.Values;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XgtC;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XltC;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XorBool;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeOptional;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.constraints.cumulative.CumulativeUnaryOptional;
import org.jacop.constraints.diffn.DiffnDecomposed;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.SimpleSelect;
import org.junit.jupiter.api.Test;

/**
 * Tests that constraints reject arguments they cannot handle with an IllegalArgumentException,
 * instead of crashing later or silently giving wrong solutions, and that the corner cases they do
 * accept give the right solutions.
 */
public class ConstraintArgumentValidationTest {

  private interface Model {
    Object post(Store store, IntVar[] v);
  }

  private static IntVar[] vars(Store store, int[]... domains) {
    IntVar[] v = new IntVar[domains.length];
    for (int i = 0; i < domains.length; i++) {
      v[i] = new IntVar(store, "v" + i);
      for (int value : domains[i]) {
        v[i].addDom(value, value);
      }
    }
    return v;
  }

  private static int[] range(int min, int max) {
    int[] r = new int[max - min + 1];
    Arrays.setAll(r, i -> min + i);
    return r;
  }

  private static final int[] BOOL = range(0, 1);
  private static final int[] NON_BOOL = range(-1, 2);

  /** Posts the model on fresh variables with the given domains and expects it to be rejected. */
  private static void assertRejected(Model model, int[]... domains) {
    Store store = new Store();
    IntVar[] v = vars(store, domains);
    assertThatThrownBy(() -> impose(store, model.post(store, v)))
        .isInstanceOf(IllegalArgumentException.class);
  }

  @SuppressWarnings("unchecked")
  private static void impose(Store store, Object c) {
    if (c instanceof Constraint constraint) {
      store.impose(constraint);
    } else {
      store.imposeDecomposition((DecomposedConstraint<Constraint>) c);
    }
  }

  /** Counts the solutions of the model and compares them with a brute force enumeration. */
  private static void assertSolutions(Model model, Predicate<int[]> relation, int[]... domains) {
    Store store = new Store();
    IntVar[] v = vars(store, domains);
    impose(store, model.post(store, v));

    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.getSolutionListener().searchAll(true);
    search.getSolutionListener().recordSolutions(false);
    boolean found = search.labeling(store, new SimpleSelect<>(v, null, new IndomainMin<>()));
    int solutions = found ? search.getSolutionListener().solutionsNo() : 0;

    assertThat(solutions).isEqualTo(bruteForce(domains, relation));
  }

  private static int bruteForce(int[][] domains, Predicate<int[]> relation) {
    List<int[]> assignments = new ArrayList<>();
    assignments.add(new int[0]);
    for (int[] domain : domains) {
      List<int[]> next = new ArrayList<>();
      for (int[] a : assignments) {
        for (int value : domain) {
          int[] b = Arrays.copyOf(a, a.length + 1);
          b[a.length] = value;
          next.add(b);
        }
      }
      assignments = next;
    }
    return (int) assignments.stream().filter(relation).count();
  }

  private static IntVar[] ones(Store store, int n, int value) {
    IntVar[] r = new IntVar[n];
    Arrays.setAll(r, i -> new IntVar(store, value, value));
    return r;
  }

  // ---- boolean constraints accepted variables outside 0..1 and gave solutions with -1 or 2

  @Test
  public void booleanConstraintsRejectNonBooleanVariables() {
    List<Model> models =
        List.of(
            (s, v) -> new AndBool(new IntVar[] {v[0], v[1], v[2]}, v[3]),
            (s, v) -> new AndBoolVector(new IntVar[] {v[0], v[1], v[2]}, v[3]),
            (s, v) -> new AndBoolSimple(v[0], v[1], v[3]),
            (s, v) -> new OrBool(new IntVar[] {v[0], v[1]}, v[3]),
            (s, v) -> new OrBoolVector(new IntVar[] {v[0], v[1], v[2]}, v[3]),
            (s, v) -> new OrBoolSimple(v[0], v[1], v[3]),
            (s, v) -> new XorBool(new IntVar[] {v[0], v[1]}, v[3]),
            (s, v) -> new EqBool(new IntVar[] {v[0], v[1]}, v[3]),
            (s, v) -> new IfThenBool(v[0], v[1], v[3]),
            (s, v) -> new BoolClause(new IntVar[] {v[0], v[1]}, new IntVar[] {v[2]}),
            (s, v) -> new Implies(v[0], new XeqC(v[1], 1)),
            (s, v) -> new Reified(new XeqC(v[1], 1), v[0]),
            (s, v) ->
                new Conditional(
                    new IntVar[] {v[0], new IntVar(s, 1, 1)},
                    new PrimitiveConstraint[] {new XeqC(v[1], 1), new XeqC(v[1], 0)}),
            (s, v) -> new ChannelImply(new IntVar(s, 0, 2), new IntVar[] {v[0], v[1], v[2]}),
            (s, v) -> new ChannelReif(new IntVar(s, 0, 2), new IntVar[] {v[0], v[1], v[2]}));
    for (Model model : models) {
      assertRejected(model, NON_BOOL, BOOL, BOOL, BOOL);
    }
  }

  @Test
  public void andOrBoolStillAcceptBooleanVariables() {
    assertSolutions(
        (s, v) -> new AndBool(new IntVar[] {v[0], v[1], v[2]}, v[3]),
        a -> a[3] == (a[0] & a[1] & a[2]),
        BOOL,
        BOOL,
        BOOL,
        BOOL);
    assertSolutions(
        (s, v) -> new OrBoolSimple(v[0], v[1], v[2]), a -> a[2] == (a[0] | a[1]), BOOL, BOOL, BOOL);
    assertSolutions(
        (s, v) -> new Implies(v[0], new XeqC(v[1], 1)),
        a -> a[0] == 0 || a[1] == 1,
        BOOL,
        range(0, 3));
  }

  @Test
  public void channelReifRejectsRepeatedValues() {
    assertRejected(
        (s, v) -> new ChannelReif(v[0], new IntVar[] {v[1], v[2]}, new int[] {1, 1}),
        range(0, 2),
        BOOL,
        BOOL);
  }

  @Test
  public void optionalCumulativesRejectBadOptionalVariables() {
    Model nonBoolean =
        (s, v) ->
            new CumulativeOptional(
                new IntVar[] {v[0], v[1]},
                ones(s, 2, 2),
                ones(s, 2, 1),
                new IntVar(s, 1, 1),
                new IntVar[] {v[2], v[3]});
    assertRejected(nonBoolean, range(0, 2), range(0, 2), NON_BOOL, BOOL);

    Model nonBooleanUnary =
        (s, v) ->
            new CumulativeUnaryOptional(
                new IntVar[] {v[0], v[1]},
                ones(s, 2, 2),
                ones(s, 2, 1),
                new IntVar(s, 1, 1),
                new IntVar[] {v[2], v[3]});
    assertRejected(nonBooleanUnary, range(0, 2), range(0, 2), NON_BOOL, BOOL);

    Model shortOpt =
        (s, v) ->
            new CumulativeOptional(
                new IntVar[] {v[0], v[1]},
                ones(s, 2, 2),
                ones(s, 2, 1),
                new IntVar(s, 1, 1),
                new IntVar[] {v[2]});
    assertRejected(shortOpt, range(0, 2), range(0, 2), BOOL);
  }

  // ---- relations

  @Test
  public void linearConstraintsRejectUnknownRelations() {
    assertRejected(
        (s, v) -> new LinearInt(new IntVar[] {v[0], v[1]}, new int[] {1, 1}, "=<>", 0), BOOL, BOOL);
    assertRejected(
        (s, v) -> new LinearIntDom(new IntVar[] {v[0], v[1]}, new int[] {1, 1}, "<>", 0),
        BOOL,
        BOOL);
    assertRejected((s, v) -> new SumInt(new IntVar[] {v[0]}, "=!", v[1]), BOOL, BOOL);
    assertRejected((s, v) -> new SumInt(new IntVar[] {v[0]}, null, v[1]), BOOL, BOOL);
  }

  @Test
  public void linearConstraintsWithConstantSumRejectEmptyList() {
    assertRejected((s, v) -> new LinearInt(new IntVar[] {}, new int[] {}, "==", 0), BOOL);
    assertRejected((s, v) -> new LinearIntDom(new IntVar[] {}, new int[] {}, "==", 0), BOOL);
  }

  // ---- constants at the int limits: c + 1 and c - 1 overflowed and pruned nothing

  @Test
  public void comparisonsWithConstantsAtTheIntLimits() {
    int[] d = range(0, 2);
    assertSolutions((s, v) -> new XgtC(v[0], Integer.MAX_VALUE), a -> false, d);
    assertSolutions((s, v) -> new XltC(v[0], Integer.MIN_VALUE), a -> false, d);
    assertSolutions((s, v) -> new XgtC(v[0], Integer.MIN_VALUE), a -> true, d);
    assertSolutions((s, v) -> new XltC(v[0], Integer.MAX_VALUE), a -> true, d);
    assertSolutions((s, v) -> new Not(new XgteqC(v[0], Integer.MIN_VALUE)), a -> false, d);
    assertSolutions((s, v) -> new Not(new XlteqC(v[0], Integer.MAX_VALUE)), a -> false, d);
    assertSolutions((s, v) -> new Not(new XgtC(v[0], Integer.MAX_VALUE)), a -> true, d);
  }

  // ---- lengths and shapes of arguments

  @Test
  public void argMinMaxRejectEmptyList() {
    assertRejected((s, v) -> new ArgMax(new IntVar[] {}, v[0]), range(0, 2));
    assertRejected((s, v) -> new ArgMin(new IntVar[] {}, v[0]), range(0, 2));
  }

  @Test
  public void countValuesRejectsCountersNotMatchingValues() {
    int[] d = range(0, 2);
    assertRejected(
        (s, v) -> new CountValues(new IntVar[] {v[0], v[1]}, new IntVar[] {v[2]}, new int[] {0, 1}),
        d,
        d,
        d);
    // one counter fewer than values silently left the last value unconstrained
    assertRejected(
        (s, v) ->
            new CountValues(new IntVar[] {v[0], v[1]}, new IntVar[] {v[2], v[3]}, new int[] {0}),
        d,
        d,
        d,
        d);
    assertRejected(
        (s, v) ->
            new CountValuesBounds(
                new IntVar[] {v[0], v[1]}, new int[] {0}, new int[] {1, 1}, new int[] {0, 1}),
        d,
        d);
  }

  @Test
  public void countValuesWithoutValues() {
    int[] d = range(0, 2);
    assertSolutions(
        (s, v) -> new CountValues(new IntVar[] {v[0], v[1]}, new IntVar[] {}, new int[] {}),
        a -> true,
        d,
        d);
  }

  @Test
  public void countBoundsWithEmptyRangeHasNoSolution() {
    int[] d = range(0, 2);
    assertSolutions(
        (s, v) -> new CountBounds(new IntVar[] {v[0], v[1]}, 1, 2, 1), a -> false, d, d);
  }

  @Test
  public void valuesOfEmptyList() {
    assertSolutions((s, v) -> new Values(new IntVar[] {}, v[0]), a -> a[0] == 0, range(0, 3));
  }

  @Test
  public void assignmentRejectsListsOfDifferentLengths() {
    assertRejected(
        (s, v) -> new Assignment(new IntVar[] {v[0], v[1]}, new IntVar[] {v[2]}), BOOL, BOOL, BOOL);
  }

  @Test
  public void lexOfVectorsOfDifferentLengths() {
    int[] d = range(0, 2);
    // a vector is lexicographically smaller than any vector it is a proper prefix of
    assertSolutions(
        (s, v) -> new Lex(new IntVar[][] {{v[0], v[1]}, {v[2]}}, false), a -> a[0] < a[2], d, d, d);
    assertSolutions(
        (s, v) -> new Lex(new IntVar[][] {{v[0]}, {v[1], v[2]}}, true), a -> a[0] <= a[1], d, d, d);
    assertSolutions(
        (s, v) -> new Lex(new IntVar[][] {{v[0]}, {v[1], v[2]}, {v[3]}}, false),
        a -> a[0] <= a[1] && a[1] < a[3],
        d,
        d,
        d,
        d);
    assertSolutions((s, v) -> new Lex(new IntVar[][] {{v[0], v[1]}}, true), a -> true, d, d);
  }

  @Test
  public void extensionalConstraintsRejectTuplesOfWrongLength() {
    int[] d = range(0, 2);
    int[][] shortTuple = {{0, 1}, {2}};
    int[][] longTuple = {{0, 1}, {2, 2, 2}};
    for (int[][] tuples : new int[][][] {shortTuple, longTuple}) {
      assertRejected((s, v) -> new ExtensionalSupportVa(new IntVar[] {v[0], v[1]}, tuples), d, d);
      assertRejected((s, v) -> new ExtensionalSupportStr(new IntVar[] {v[0], v[1]}, tuples), d, d);
      assertRejected((s, v) -> new ExtensionalConflictVa(new IntVar[] {v[0], v[1]}, tuples), d, d);
    }
    assertRejected((s, v) -> new ExtensionalSupportVa(new IntVar[] {v[0], v[1]}, null), d, d);
  }

  @Test
  public void stretchRejectsBadParameters() {
    assertRejected(
        (s, v) -> new Stretch(new int[] {0, 1}, new int[] {1}, new int[] {2, 2}, v),
        BOOL,
        BOOL,
        BOOL);
    assertRejected(
        (s, v) -> new Stretch(new int[] {0, 0, 1}, new int[] {1, 3, 1}, new int[] {1, 3, 1}, v),
        BOOL,
        BOOL,
        BOOL);
  }

  @Test
  public void sequenceSubsequenceLength() {
    IntervalDomain one = new IntervalDomain(1, 1);
    assertRejected((s, v) -> new Sequence(v, one, 0, 0, 1), BOOL, BOOL, BOOL);
    // no subsequence of length 4 in 3 variables
    assertSolutions((s, v) -> new Sequence(v, one, 4, 0, 1), a -> true, BOOL, BOOL, BOOL);
    assertSolutions(
        (s, v) -> new Sequence(v, one, 3, 0, 1), a -> a[0] + a[1] + a[2] <= 1, BOOL, BOOL, BOOL);
  }

  @Test
  public void conditionalRejectsEmptyLists() {
    assertRejected((s, v) -> new Conditional(new IntVar[] {}, new PrimitiveConstraint[] {}), BOOL);
  }

  // ---- scheduling and geometry

  @Test
  public void cumulativeUnaryRejectsTasksThatFitTogether() {
    Function<IntVar, Model> unary =
        limit ->
            (s, v) ->
                new CumulativeUnary(new IntVar[] {v[0], v[1]}, ones(s, 2, 2), ones(s, 2, 1), limit);
    Store store = new Store();
    assertRejected(unary.apply(new IntVar(store, 2, 2)), range(0, 2), range(0, 2));
    assertRejected(unary.apply(new IntVar(store, 1, 3)), range(0, 2), range(0, 2));
  }

  @Test
  public void cumulativeUnaryAcceptsUnaryResources() {
    // tasks that use nothing, or a resource with limit 1
    assertSolutions(
        (s, v) ->
            new CumulativeUnary(
                new IntVar[] {v[0], v[1]},
                new IntVar[] {new IntVar(s, 2, 2), v[4]},
                new IntVar[] {v[2], v[3]},
                new IntVar(s, 1, 1)),
        a -> a[2] == 0 || a[3] == 0 || a[4] == 0 || a[0] + 2 <= a[1] || a[1] + a[4] <= a[0],
        range(0, 2),
        range(0, 2),
        BOOL,
        BOOL,
        range(0, 2));
    // resources 2 and 2 do not fit together within limit 3
    assertSolutions(
        (s, v) ->
            new CumulativeUnary(
                new IntVar[] {v[0], v[1]},
                ones(s, 2, 2),
                new IntVar[] {v[2], v[3]},
                new IntVar(s, 3, 3)),
        a -> a[2] == 0 || a[3] == 0 || Math.abs(a[0] - a[1]) >= 2,
        range(0, 2),
        range(0, 2),
        new int[] {0, 2},
        new int[] {0, 2});
  }

  @Test
  public void cumulativeWithoutTasks() {
    assertSolutions(
        (s, v) -> new Cumulative(new IntVar[] {}, new IntVar[] {}, new IntVar[] {}, v[0]),
        a -> true,
        range(0, 2));
  }

  @Test
  public void rectangleConstraintsRejectNegativeLengths() {
    int[] o = range(0, 1);
    int[] l = range(-1, 1);
    assertRejected(
        (s, v) ->
            new Diff2(
                new IntVar[][] {
                  {v[0], v[1], v[2], new IntVar(s, 1, 1)}, {v[3], v[4], v[5], new IntVar(s, 1, 1)}
                }),
        o,
        o,
        l,
        o,
        o,
        l);
    assertRejected(
        (s, v) ->
            new Disjoint(
                new IntVar[][] {
                  {v[0], v[1], v[2], new IntVar(s, 1, 1)}, {v[3], v[4], v[5], new IntVar(s, 1, 1)}
                }),
        o,
        o,
        l,
        o,
        o,
        l);
  }

  private static Rectangle unitSquare(Store s, IntVar x) {
    return new Rectangle(
        new IntVar[] {x, new IntVar(s, 0, 0), new IntVar(s, 1, 1), new IntVar(s, 1, 1)});
  }

  @Test
  public void diff2RejectsBadExclusiveList() {
    int[] o = range(0, 1);
    assertRejected(
        (s, v) ->
            new Diff2(
                new Rectangle[] {unitSquare(s, v[0]), unitSquare(s, v[1])}, new int[] {1}, true),
        o,
        o);
    assertRejected(
        (s, v) ->
            new Diff2(
                new Rectangle[] {unitSquare(s, v[0]), unitSquare(s, v[1])}, new int[] {1, 5}, true),
        o,
        o);
  }

  private static Model disjointConditional(List<List<Integer>> pairs, int conditions) {
    return (s, v) ->
        new DisjointConditional(
            new IntVar[] {v[0], v[1]},
            new IntVar[] {new IntVar(s, 0, 0), new IntVar(s, 0, 0)},
            ones(s, 2, 1),
            ones(s, 2, 1),
            pairs,
            Arrays.asList(v).subList(2, 2 + conditions));
  }

  @Test
  public void disjointConditionalRejectsBadExceptions() {
    int[] o = range(0, 1);
    assertRejected(disjointConditional(List.of(List.of(1, 2)), 0), o, o);
    // rectangles are numbered from 1
    assertRejected(disjointConditional(List.of(List.of(0, 1)), 1), o, o, BOOL);
    assertRejected(disjointConditional(List.of(List.of(1, 7)), 1), o, o, BOOL);
    assertRejected(disjointConditional(List.of(List.of(1, 2)), 1), o, o, NON_BOOL);
    // the condition tells whether the pair must not overlap
    assertSolutions(
        disjointConditional(List.of(List.of(1, 2)), 1), a -> a[2] == 0 || a[0] != a[1], o, o, BOOL);
  }

  @Test
  public void diffnDecomposedAcceptsListOfRectangles() {
    assertSolutions(
        (s, v) ->
            new DiffnDecomposed(
                List.of(
                    List.of(v[0], new IntVar(s, 0, 0), new IntVar(s, 1, 1), new IntVar(s, 1, 1)),
                    List.of(v[1], new IntVar(s, 0, 0), new IntVar(s, 1, 1), new IntVar(s, 1, 1)))),
        a -> a[0] != a[1],
        range(0, 1),
        range(0, 1));
    assertRejected(
        (s, v) -> new DiffnDecomposed(List.of(List.of(v[0], v[1], v[0]))), range(0, 1), BOOL);
  }

  @Test
  public void absStillHandlesAliasedVariables() {
    assertSolutions((s, v) -> new AbsXeqY(v[0], v[0]), a -> a[0] >= 0, range(-3, 3));
  }
}
