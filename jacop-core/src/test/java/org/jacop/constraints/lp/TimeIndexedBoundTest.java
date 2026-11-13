package org.jacop.constraints.lp;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.LinearForm;
import org.junit.jupiter.api.Test;

/** Tests of {@link TimeIndexedBound}: its bound never cuts off an optimum. */
class TimeIndexedBoundTest {

  private static final int INSTANCES = Integer.getInteger("timeIndexed.instances", 200);

  // two tasks of length 5 on a unit resource: the time-indexed bound is 8 (LP 7.5), and no
  // schedule ends by 9, which the program finds infeasible once the horizon is 9
  @Test
  void twoTasksOnOneMachine() {
    Store store = new Store();
    IntVar[] s = {new IntVar(store, "s0", 0, 20), new IntVar(store, "s1", 0, 20)};
    IntVar c = new IntVar(store, "c", 0, 25);
    IntVar one = new IntVar(store, 1, 1);
    IntVar five = new IntVar(store, 5, 5);
    store.impose(new Cumulative(s, new IntVar[] {five, five}, new IntVar[] {one, one}, one));
    List<LinearForm> rows = new ArrayList<>();
    for (IntVar x : s) {
      rows.add(new LinearForm(new IntVar[] {x, c}, new long[] {1, -1}, -5, LinearForm.LE));
    }
    TimeIndexedBound bound = TimeIndexedBound.of(store, c, false, rows);
    assertThat(bound).isNotNull();
    store.impose(bound);
    assertThat(store.consistency()).isTrue();
    assertThat(c.min()).isEqualTo(8);
    store.setLevel(store.level + 1);
    c.domain.inMax(store.level, c, 9);
    assertThat(store.consistency()).isFalse();
  }

  private record Instance(int[] dur, int[][] use, int[] cap, int[][] prec, int horizon) {

    // the least makespan over all starts in [0, horizon - dur], or -1
    int optimum() {
      int n = dur.length;
      int[] st = new int[n];
      int best = Integer.MAX_VALUE;
      while (true) {
        if (feasible(st)) {
          int end = 0;
          for (int j = 0; j < n; j++) {
            end = Math.max(end, st[j] + dur[j]);
          }
          best = Math.min(best, end);
        }
        int j = 0;
        while (j < n && st[j] == horizon - dur[j]) {
          st[j] = 0;
          j++;
        }
        if (j == n) {
          return best == Integer.MAX_VALUE ? -1 : best;
        }
        st[j]++;
      }
    }

    boolean feasible(int[] st) {
      for (int[] p : prec) {
        if (st[p[0]] + dur[p[0]] > st[p[1]]) {
          return false;
        }
      }
      for (int r = 0; r < cap.length; r++) {
        for (int t = 0; t < horizon; t++) {
          int used = 0;
          for (int j = 0; j < dur.length; j++) {
            if (st[j] <= t && t < st[j] + dur[j]) {
              used += use[r][j];
            }
          }
          if (used > cap[r]) {
            return false;
          }
        }
      }
      return true;
    }
  }

  private static Instance random(Random rnd) {
    int n = 2 + rnd.nextInt(3);
    int resources = 1 + rnd.nextInt(2);
    int[] dur = new int[n];
    int horizon = 0;
    for (int j = 0; j < n; j++) {
      dur[j] = 1 + rnd.nextInt(3);
      horizon += dur[j];
    }
    int[] cap = new int[resources];
    int[][] use = new int[resources][n];
    for (int r = 0; r < resources; r++) {
      cap[r] = 1 + rnd.nextInt(3);
      for (int j = 0; j < n; j++) {
        use[r][j] = rnd.nextInt(cap[r] + 1);
      }
    }
    List<int[]> prec = new ArrayList<>();
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (rnd.nextInt(4) == 0) {
          prec.add(new int[] {i, j});
        }
      }
    }
    return new Instance(dur, use, cap, prec.toArray(new int[0][]), horizon);
  }

  // the bound at the root is at most the optimum, and with the makespan below the optimum the
  // bound proves it (or at least does not cut off the optimum when the makespan is the optimum)
  @Test
  void boundKeepsTheOptimum() {
    Random rnd = new Random(11);
    int raised = 0;
    for (int instance = 0; instance < INSTANCES; instance++) {
      Instance in = random(rnd);
      int opt = in.optimum();
      for (int limit : new int[] {in.horizon, opt}) {
        Store store = new Store();
        int n = in.dur.length;
        IntVar[] s = new IntVar[n];
        for (int j = 0; j < n; j++) {
          s[j] = new IntVar(store, "s" + j, 0, in.horizon - in.dur[j]);
        }
        IntVar c = new IntVar(store, "c", 0, limit);
        List<LinearForm> rows = new ArrayList<>();
        for (int j = 0; j < n; j++) {
          rows.add(new LinearForm(new IntVar[] {s[j], c}, new long[] {1, -1}, -in.dur[j], 0));
        }
        for (int[] p : in.prec) {
          rows.add(
              new LinearForm(
                  new IntVar[] {s[p[0]], s[p[1]]}, new long[] {1, -1}, -in.dur[p[0]], 0));
        }
        for (int r = 0; r < in.cap.length; r++) {
          IntVar[] d = new IntVar[n];
          IntVar[] u = new IntVar[n];
          for (int j = 0; j < n; j++) {
            d[j] = new IntVar(store, in.dur[j], in.dur[j]);
            u[j] = new IntVar(store, in.use[r][j], in.use[r][j]);
          }
          store.impose(new Cumulative(s, d, u, new IntVar(store, in.cap[r], in.cap[r])));
        }
        TimeIndexedBound bound = TimeIndexedBound.of(store, c, false, rows);
        if (bound == null) {
          continue;
        }
        store.impose(bound);
        // the bound alone, with the other propagators as given: no optimum is ever cut off
        boolean ok = store.consistency();
        assertThat(ok).as("instance %d, limit %d, optimum %d", instance, limit, opt).isTrue();
        assertThat(c.min()).as("instance %d, limit %d", instance, limit).isLessThanOrEqualTo(opt);
        if (limit == in.horizon && bound.bestBound > 0) {
          raised++;
        }
        // below the optimum the bound may prove infeasibility; it must never raise past limit
        store.setLevel(store.level + 1);
        if (opt > c.min()) {
          c.domain.inMax(store.level, c, opt - 1);
          store.consistency();
        }
      }
    }
    assertThat(raised).isPositive();
  }
}
