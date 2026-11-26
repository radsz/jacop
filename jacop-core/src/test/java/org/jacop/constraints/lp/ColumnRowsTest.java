package org.jacop.constraints.lp;

import static org.assertj.core.api.Assertions.assertThat;

import org.jacop.constraints.LinearInt;
import org.jacop.constraints.MaxSimple;
import org.jacop.constraints.MinSimple;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XlteqC;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Test;

/**
 * The rows over columns the relaxation already has that come past the share of the further rows
 * (org.jacop.lp.columnRows).
 */
class ColumnRowsTest {

  private final boolean saved = LinearRelaxation.columnRowsOn;
  private final boolean savedTail = LinearRelaxation.CLAUSE_ROWS;

  @AfterEach
  void restore() {
    LinearRelaxation.columnRowsOn = saved;
    LinearRelaxation.CLAUSE_ROWS = savedTail;
  }

  // a path of n legs from 0 to k on a line, each leg of length max - min of its two ends, and
  // reified comparisons of the inner points that take the share; the root bound of the relaxation
  private static double rootBound(int n, int k, boolean columnRows) {
    LinearRelaxation.columnRowsOn = columnRows;
    LinearRelaxation.CLAUSE_ROWS = columnRows;
    Store store = new Store();
    IntVar[] x = new IntVar[n + 1];
    for (int i = 0; i <= n; i++) {
      x[i] = new IntVar(store, "x" + i, i == n ? k : 0, i == 0 ? 0 : k);
    }
    IntVar[] terms = new IntVar[n + 1];
    int[] weights = new int[n + 1];
    for (int i = 0; i < n; i++) {
      IntVar hi = new IntVar(store, "hi" + i, 0, k);
      IntVar lo = new IntVar(store, "lo" + i, 0, k);
      IntVar length = new IntVar(store, "l" + i, 0, k);
      store.impose(new MaxSimple(x[i], x[i + 1], hi));
      store.impose(new MinSimple(x[i], x[i + 1], lo));
      store.impose(new LinearInt(new IntVar[] {length, hi, lo}, new int[] {1, -1, 1}, "==", 0));
      // the points are columns of rows of their own, as the coordinates of a routing model are
      IntVar room = new IntVar(store, "r" + i, 0, k);
      store.impose(new LinearInt(new IntVar[] {x[i + 1], room}, new int[] {1, 1}, "==", k));
      // reified comparisons of the lengths, nearer to the objective, take the share
      for (int c = 1; c < 8; c++) {
        store.impose(new Reified(new XlteqC(length, c * k / 8), new BooleanVar(store)));
      }
      terms[i] = length;
      weights[i] = 1;
    }
    IntVar total = new IntVar(store, "total", 0, n * k);
    terms[n] = total;
    weights[n] = -1;
    store.impose(new LinearInt(terms, weights, "==", 0));
    assertThat(store.consistency()).isTrue();
    LinearRelaxation r = LinearRelaxation.of(store, total, false);
    assertThat(r).isNotNull();
    store.impose(r);
    assertThat(store.consistency()).isTrue();
    return r.rootBound;
  }

  @Test
  void rowsOverTakenColumnsPastTheShareKeepTheBound() {
    double with = rootBound(60, 100, true);
    double without = rootBound(60, 100, false);
    // without them the max and min rows of the legs miss the share and nothing bounds the lengths
    assertThat(without).isLessThan(1.0);
    // with them every leg is at least the distance of its ends: the bound is the optimum
    assertThat(with).isEqualTo(100.0);
  }
}
