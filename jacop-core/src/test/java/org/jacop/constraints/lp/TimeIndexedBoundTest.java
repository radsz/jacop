package org.jacop.constraints.lp;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.assertThatThrownBy;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import org.jacop.constraints.binpacking.Binpacking;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.LinearForm;
import org.junit.jupiter.api.Test;

/**
 * Tests of {@link TimeIndexedBound}: its bound never cuts off an optimum, with arc-flow blocks too.
 */
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

  // a model of a bin packing with the cost sum (load_b - target)^2, the objective c
  private static IntVar binPackingModel(
      Store store,
      int[] w,
      int bins,
      int target,
      int limit,
      List<LinearForm> rows,
      List<TimeIndexedBound.LoadFunction> functions) {
    IntVar[] bin = new IntVar[w.length];
    int total = 0;
    for (int i = 0; i < w.length; i++) {
      bin[i] = new IntVar(store, "b" + i, 1, bins);
      total += w[i];
    }
    IntVar[] load = new IntVar[bins];
    IntVar[] cost = new IntVar[bins];
    long[] values = new long[total + 1];
    for (int v = 0; v <= total; v++) {
      values[v] = (long) (v - target) * (v - target);
    }
    for (int b = 0; b < bins; b++) {
      load[b] = new IntVar(store, "l" + b, 0, total);
      cost[b] = new IntVar(store, "z" + b, 0, (total + target) * (total + target));
      functions.add(new TimeIndexedBound.LoadFunction(cost[b], load[b], 0, values));
    }
    store.impose(new Binpacking(bin, load, w));
    IntVar c = new IntVar(store, "c", 0, limit);
    IntVar[] vs = new IntVar[bins + 1];
    long[] ws = new long[bins + 1];
    for (int b = 0; b < bins; b++) {
      vs[b] = cost[b];
      ws[b] = 1;
    }
    vs[bins] = c;
    ws[bins] = -1;
    rows.add(new LinearForm(vs, ws, 0, LinearForm.EQ));
    long[] ones = new long[bins];
    Arrays.fill(ones, 1);
    rows.add(new LinearForm(load, ones, total, LinearForm.EQ));
    return c;
  }

  // three items of weight 2 in two bins, cost load^2: the loads can only be 0, 2, 4 or 6, so the
  // arc-flow bound is 4 + 16 = 20 (the plain relaxation allows 3 + 3, cost 18)
  @Test
  void arcFlowSquaredLoads() {
    Store store = new Store();
    List<LinearForm> rows = new ArrayList<>();
    List<TimeIndexedBound.LoadFunction> functions = new ArrayList<>();
    IntVar c = binPackingModel(store, new int[] {2, 2, 2}, 2, 0, 100, rows, functions);
    TimeIndexedBound bound = TimeIndexedBound.of(store, c, false, rows, false, true, functions);
    assertThat(bound).isNotNull();
    store.impose(bound);
    assertThat(store.consistency()).isTrue();
    assertThat(c.min()).isEqualTo(20);
    assertThat(bound.lastArcs).isPositive();
  }

  // a solve at a level where the items were fixed proves 36; back above that level, with the items
  // free again, the bound is 20 (regression: the stronger solve stayed in force with looser bounds,
  // which proved a wrong optimum under lazy clause generation free search on gbac)
  @Test
  void arcFlowSolveHoldsOnlyWithinItsBounds() {
    Store store = new Store();
    List<LinearForm> rows = new ArrayList<>();
    List<TimeIndexedBound.LoadFunction> functions = new ArrayList<>();
    IntVar c = binPackingModel(store, new int[] {2, 2, 2}, 2, 0, 100, rows, functions);
    TimeIndexedBound bound = TimeIndexedBound.of(store, c, false, rows, false, true, functions);
    store.setLevel(store.level + 1);
    for (int i = 0; i < 3; i++) {
      IntVar b = (IntVar) store.findVariable("b" + i);
      b.domain.in(store.level, b, 1, 1);
    }
    store.impose(bound);
    assertThat(store.consistency()).isTrue();
    assertThat(c.min()).isEqualTo(36);
    store.removeLevel(store.level);
    store.setLevel(store.level - 1);
    assertThat(c.min()).isZero();
    bound.consistency(store);
    assertThat(c.min()).isLessThanOrEqualTo(20);
  }

  // the root solve proves c >= 20 assuming c <= 100; when a lower bound probe sets c <= 19 the
  // failure is explained by c <= 19 (before: by c <= 100, which is no condition at all, so the
  // learnt clause cut off every solution and proved a wrong optimum on gbac under -f)
  @Test
  void arcFlowFailureIsExplainedByTheObjectiveBelowTheBound() {
    Store store = new Store();
    List<LinearForm> rows = new ArrayList<>();
    List<TimeIndexedBound.LoadFunction> functions = new ArrayList<>();
    IntVar c = binPackingModel(store, new int[] {2, 2, 2}, 2, 0, 100, rows, functions);
    AtomicTrail trail = new AtomicTrail(store);
    TimeIndexedBound bound = TimeIndexedBound.of(store, c, false, rows, false, true, functions);
    store.setLevel(store.level + 1);
    store.impose(bound);
    // restarts that change other root bounds (the bound wakes on the objective only, so it is
    // called here) solve again; the solves do not improve the bound and
    // back off, so the probe below the bound reuses the solve that assumed no objective limit
    IntVar z = (IntVar) store.findVariable("z0");
    for (int k = 0; k < 8; k++) {
      store.setLevel(store.level + 1);
      z.domain.inMax(store.level, z, 36 - k);
      bound.consistency(store);
      assertThat(c.min()).isEqualTo(20);
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
    }
    // a probe of the objective limit below the bound, as core-guided lower bound runs make
    store.setLevel(store.level + 1);
    c.domain.inMax(store.level, c, 19);
    assertThatThrownBy(() -> bound.consistency(store)).isInstanceOf(FailException.class);
    EntryList out = new EntryList();
    assertThat(bound.explainFailure(trail, out)).isTrue();
    boolean cited = false;
    for (int k = 0; k < out.size(); k++) {
      int e = out.get(k);
      if (trail.variable(e) == c) {
        assertThat(trail.kind(e)).isEqualTo(AtomicTrail.LE);
        assertThat(trail.value(e)).isLessThanOrEqualTo(19);
        cited = true;
      }
    }
    assertThat(cited).isTrue();
    trail.detach();
  }

  // the least cost of the bin packing over all assignments
  private static int binPackingOptimum(int[] w, int bins, int target) {
    int n = w.length;
    int[] a = new int[n];
    int best = Integer.MAX_VALUE;
    while (true) {
      int[] load = new int[bins];
      for (int i = 0; i < n; i++) {
        load[a[i]] += w[i];
      }
      int cost = 0;
      for (int l : load) {
        cost += (l - target) * (l - target);
      }
      best = Math.min(best, cost);
      int i = 0;
      while (i < n && a[i] == bins - 1) {
        a[i] = 0;
        i++;
      }
      if (i == n) {
        return best;
      }
      a[i]++;
    }
  }

  // random bin packings with a squared deviation cost: the arc-flow bound at the root never
  // passes the optimum, and it raises the bound on some
  @Test
  void arcFlowKeepsTheOptimum() {
    Random rnd = new Random(5);
    int raised = 0;
    for (int instance = 0; instance < INSTANCES; instance++) {
      int n = 2 + rnd.nextInt(5);
      int bins = 2 + rnd.nextInt(2);
      int[] w = new int[n];
      int total = 0;
      for (int i = 0; i < n; i++) {
        w[i] = 1 + rnd.nextInt(5);
        total += w[i];
      }
      int target = rnd.nextInt(total + 1);
      int opt = binPackingOptimum(w, bins, target);
      for (int limit : new int[] {10_000, opt}) {
        Store store = new Store();
        List<LinearForm> rows = new ArrayList<>();
        List<TimeIndexedBound.LoadFunction> functions = new ArrayList<>();
        IntVar c = binPackingModel(store, w, bins, target, limit, rows, functions);
        TimeIndexedBound bound = TimeIndexedBound.of(store, c, false, rows, false, true, functions);
        store.impose(bound);
        assertThat(store.consistency())
            .as("instance %d, limit %d, optimum %d", instance, limit, opt)
            .isTrue();
        assertThat(c.min()).as("instance %d, limit %d", instance, limit).isLessThanOrEqualTo(opt);
        if (limit > opt && bound.bestBound > 0) {
          raised++;
        }
      }
    }
    assertThat(raised).isPositive();
  }
}
