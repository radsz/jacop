/*
 * SocialGolfer.java
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

package org.jacop.examples.set;

import java.util.ArrayList;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.XlteqY;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.set.constraints.AdisjointB;
import org.jacop.set.constraints.AeqS;
import org.jacop.set.constraints.AintersectBeqC;
import org.jacop.set.constraints.AunionBeqC;
import org.jacop.set.constraints.CardA;
import org.jacop.set.constraints.Match;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetVar;
import org.jacop.set.search.IndomainSetMin;
import org.jacop.set.search.MaxGlbCard;
import org.jacop.set.search.MinLubCard;

/**
 * It is a Social Golfer example based on set variables.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class SocialGolfer extends ExampleSet {

  // 2, 7, 4

  int weeks = 3;

  int groups = 2;

  int players = 2;

  SetVar[][] golferGroup;

  /**
   * It runs a number of social golfer problems.
   *
   * @param args parameters (none)
   */
  public static void main(String[] args) {
    if (args == null) {
      throw new IllegalArgumentException("args must not be null");
    }

    SocialGolfer example = new SocialGolfer();

    int[][] problems = {
      {3, 2, 2},
      {2, 5, 4}, // weeks - groups - players in each group
      {2, 6, 4},
      {2, 7, 4},
      {3, 5, 4},
      {3, 6, 4},
      {3, 7, 4},
      {4, 5, 4},
      {4, 6, 5},
      {4, 7, 4},
      {4, 9, 4},
      {5, 5, 3},
      {5, 7, 4},
      {5, 8, 3},
      {6, 6, 3},
      {5, 3, 2},
      {4, 3, 3}
    };

    for (int[] problem : problems) {
      example.setup(problem[0], problem[1], problem[2]);
      example.model();
      example.search();
    }
  }

  /**
   * It sets the parameters for the model creation function.
   *
   * @param weeks how many weeks to play
   * @param groups how many groups will play
   * @param players how many players will play
   */
  public void setup(int weeks, int groups, int players) {

    this.weeks = weeks;
    this.groups = groups;
    this.players = players;
  }

  /** Creates the constraint model for the social golfer problem. */
  @Override
  public void model() {

    final int n = groups * players;

    int[] weights = computeWeights(players);

    log.info("Social golfer problem " + weeks + "-" + groups + "-" + players);

    store = new Store();

    golferGroup = new SetVar[weeks][groups];

    vars = new ArrayList<>();

    imposeGroupCardinalityConstraints(n);

    imposeDisjointConstraints();

    imposeUnionConstraints(n);

    imposeIntersectionConstraints(n);

    imposeMatchAndOrderingConstraints(n, weights);
  }

  private int[] computeWeights(int playerCount) {
    int[] weights = new int[playerCount];
    int base = Math.max(10, playerCount + 1); // at least players + 1

    weights[playerCount - 1] = 1;

    for (int i = playerCount - 2; i >= 0; i--) {
      weights[i] = weights[i + 1] * base;
    }
    return weights;
  }

  private void imposeGroupCardinalityConstraints(int n) {
    for (int i = 0; i < weeks; i++) {
      for (int j = 0; j < groups; j++) {
        golferGroup[i][j] = new SetVar(store, "g_" + i + "_" + j, new BoundSetDomain(1, n));
        vars.add(golferGroup[i][j]);
        store.impose(new CardA(golferGroup[i][j], players));
      }
    }
  }

  private void imposeDisjointConstraints() {
    for (int i = 0; i < weeks; i++) {
      for (int j = 0; j < groups; j++) {
        for (int k = j + 1; k < groups; k++) {
          store.impose(new AdisjointB(golferGroup[i][j], golferGroup[i][k]));
        }
      }
    }
  }

  private void imposeUnionConstraints(int n) {
    for (int i = 0; i < weeks; i++) {
      SetVar t = golferGroup[i][0];

      for (int j = 1; j < groups; j++) {
        SetVar r = new SetVar(store, "r-" + i + "-" + j, new BoundSetDomain(1, n));
        store.impose(new AunionBeqC(t, golferGroup[i][j], r));
        t = r;
      }

      store.impose(new AeqS(t, new IntervalDomain(1, n)));
    }
  }

  private void imposeIntersectionConstraints(int n) {
    for (int i = 0; i < weeks; i++) {
      for (int j = i + 1; j < weeks; j++) {
        for (int k = 0; k < groups; k++) {
          for (int l = 0; l < groups; l++) {
            SetVar result =
                new SetVar(
                    store, "res" + i + "-" + j + "-" + k + "-" + l, new BoundSetDomain(1, n));
            store.impose(new AintersectBeqC(golferGroup[i][k], golferGroup[j][l], result));
            store.impose(new CardA(result, 0, 1));
          }
        }
      }
    }
  }

  private void imposeMatchAndOrderingConstraints(int n, int[] weights) {
    IntVar[] v = new IntVar[weeks];
    IntVar[][] var = new IntVar[weeks][players];
    for (int i = 0; i < weeks; i++) {
      v[i] = new IntVar(store, "v" + i, 0, 100000000);
      for (int j = 0; j < players; j++) {
        var[i][j] = new IntVar(store, "var" + i + "-" + j, 1, n);
      }
      store.impose(new Match(golferGroup[i][0], var[i]));

      int varLen = var[i].length;
      IntVar[] vs = new IntVar[varLen + 1];
      int[] ws = new int[varLen + 1];
      System.arraycopy(var[i], 0, vs, 0, varLen);
      System.arraycopy(weights, 0, ws, 0, varLen);
      vs[varLen] = v[i];
      ws[varLen] = -1;
      store.impose(new LinearInt(vs, ws, "==", 0));
    }

    for (int i = 0; i < weeks - 1; i++) {
      store.impose(new XlteqY(v[i], v[i + 1]));
    }
  }

  /**
   * Performs the search for a solution to the social golfer problem.
   *
   * @return true if a solution is found, false otherwise.
   */
  @Override
  public boolean search() {

    Thread tread = Thread.currentThread();
    java.lang.management.ThreadMXBean b = java.lang.management.ManagementFactory.getThreadMXBean();

    final long startCpu = b.getThreadCpuTime(tread.threadId());
    final long startUser = b.getThreadUserTime(tread.threadId());

    boolean result = store.consistency();
    log.info("*** consistency = " + result);

    Search<SetVar> label = new DepthFirstSearch<>();

    SelectChoicePoint<SetVar> select =
        new SimpleSelect<>(
            vars.toArray(SetVar[]::new),
            new MinLubCard<>(),
            new MaxGlbCard<>(),
            new IndomainSetMin<>());

    label.getSolutionListener().searchAll(false);
    label.getSolutionListener().recordSolutions(false);

    result = label.labeling(store, select);

    if (result) {
      log.info("*** Yes");
      for (int i = 0; i < weeks; i++) {
        for (int j = 0; j < groups; j++) {
          IO.print(golferGroup[i][j].dom() + " ");
        }
        log.info("");
      }
    } else {
      log.info("*** No");
    }

    log.info(
        "ThreadCpuTime = " + (b.getThreadCpuTime(tread.threadId()) - startCpu) / 1_000_000L + "ms");
    log.info(
        "ThreadUserTime = "
            + (b.getThreadUserTime(tread.threadId()) - startUser) / 1_000_000L
            + "ms");

    return result;
  }
}
