/*
 * CumulativeReductions.java
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
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.constraints.cumulative.CumulativeUnary;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.lcg.LinearExplainable;
import org.jacop.lcg.LinearForm;

/**
 * Presolve of cumulative resources, after Heinz, Schulz and Beck, "Using dual presolving reductions
 * to reformulate cumulative constraints", Constraints 18, 2013.
 *
 * <p>The rule reads the possible profile of a resource: at each time, the sum of the largest
 * resource uses of the tasks whose time windows (from the smallest start to the largest start plus
 * the largest duration) contain that time. Where this profile stays within the smallest limit, the
 * resource cannot be overloaded whatever the tasks do. Three reductions follow.
 *
 * <ul>
 *   <li><b>Irrelevant tasks.</b> A task whose whole window lies where the profile fits the limit
 *       never overloads the resource, so it is removed from the constraint; so is a task that can
 *       never use the resource. A constraint left without tasks is removed. These reductions keep
 *       every solution.
 *   <li><b>Subsumed resources.</b> A resource whose tasks are all tasks of another resource with a
 *       limit no larger is implied by it. A unary resource whose tasks, as pairs of start and
 *       duration, are all tasks of another unary resource is implied by it too, which merges the
 *       unary resources that the disjunctive cliques add with those of the model. These keep every
 *       solution as well.
 *   <li><b>Dual fixing.</b> If moving a start time earlier violates no other constraint and does
 *       not make the objective worse (the start has no down-locks), and the profile fits the limit
 *       from the smallest start to the smallest start plus the largest duration, in every resource
 *       of the task, then any solution stays a solution, and no worse, with the task moved to its
 *       smallest start: the start is fixed there. Symmetrically, a start without up-locks whose
 *       last window fits is fixed to its largest value. This keeps an optimal solution but not
 *       every solution, so it is only switched on when one solution, or one optimal solution, is
 *       wanted.
 * </ul>
 *
 * <p>The locks of a start come from the other constraints on it: a linear inequality locks it only
 * against the direction its weight moves the sum towards the bound, and any other constraint that
 * is neither entailed nor satisfied locks it both ways. The objective variable is locked in the
 * direction that worsens it, and variables the caller names (for example those of constraints kept
 * outside the store) are locked both ways.
 *
 * <p>The rule applies to the classes {@link CumulativeBasic}, {@link Cumulative} and {@link
 * CumulativeUnary}, whose resources hold when the tasks of positive duration and resource use never
 * exceed the limit together.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class CumulativeReductions implements Rule {

  // resources with more tasks are skipped; the profile costs time quadratic in the tasks
  private static final int MAX_TASKS = 5000;

  private final boolean dual;
  private IntVar objective;
  private boolean minimize;
  private final Set<Var> locked = Collections.newSetFromMap(new IdentityHashMap<>());

  private int fixedStarts;
  private int removedTasks;
  private int removedResources;

  /**
   * It creates the rule.
   *
   * @param dual true to apply dual fixing, which keeps an optimal solution but may lose others.
   */
  public CumulativeReductions(boolean dual) {
    this.dual = dual;
  }

  /**
   * Sets the objective, which dual fixing must not make worse.
   *
   * @param cost the objective variable, or null for a satisfaction problem.
   * @param minimize true if the objective is minimized, false if it is maximized.
   * @return this rule.
   */
  public CumulativeReductions objective(IntVar cost, boolean minimize) {
    this.objective = cost;
    this.minimize = minimize;
    return this;
  }

  /**
   * Locks variables both ways for dual fixing, because constraints the store does not see use them.
   *
   * @param vars the variables.
   * @return this rule.
   */
  public CumulativeReductions lock(Var... vars) {
    Collections.addAll(locked, vars);
    return this;
  }

  /**
   * Returns the number of start variables fixed by dual fixing.
   *
   * @return the number.
   */
  public int fixedStarts() {
    return fixedStarts;
  }

  /**
   * Returns the number of tasks removed from resources that are kept.
   *
   * @return the number.
   */
  public int removedTasks() {
    return removedTasks;
  }

  /**
   * Returns the number of resources removed, because no task is left or another resource implies
   * them.
   *
   * @return the number.
   */
  public int removedResources() {
    return removedResources;
  }

  // a resource of the rule and its tasks
  private static final class Resource {
    final CumulativeBasic constraint;
    final IntVar[] s;
    final IntVar[] d;
    final IntVar[] r;
    final IntVar limit;

    Resource(CumulativeBasic c) {
      constraint = c;
      IntVar[][] t = c.tasks();
      s = t[0];
      d = t[1];
      r = t[2];
      limit = c.limit();
    }

    int size() {
      return s.length;
    }

    boolean uses(int i) {
      return d[i].max() > 0 && r[i].max() > 0;
    }

    long est(int i) {
      return s[i].min();
    }

    long lct(int i) {
      return (long) s[i].max() + d[i].max();
    }
  }

  @Override
  public void apply(Context context) {
    List<Resource> resources = new ArrayList<>();
    for (Constraint c : context.constraints()) {
      if (isResource(c)) {
        resources.add(new Resource((CumulativeBasic) c));
      }
    }
    if (resources.isEmpty()) {
      return;
    }
    if (dual && fix(context, resources)) {
      // the next round sees the windows narrowed by propagation
      return;
    }
    removeSubsumed(context, resources);
    for (Resource res : resources) {
      if (!context.removed(res.constraint)) {
        removeIrrelevant(context, res);
      }
    }
  }

  private static boolean isResource(Constraint c) {
    Class<?> k = c.getClass();
    return k == CumulativeBasic.class || k == Cumulative.class || k == CumulativeUnary.class;
  }

  /** Returns the possible profile of a resource over the given tasks. */
  private static Profile profile(Resource res, boolean[] in) {
    int n = res.size();
    long[] times = new long[4 * n];
    int m = 0;
    for (int i = 0; i < n; i++) {
      if (in[i]) {
        times[m++] = res.est(i);
        times[m++] = res.lct(i);
        times[m++] = res.est(i) + res.d[i].max();
        times[m++] = (long) res.s[i].max();
      }
    }
    times = Arrays.stream(times, 0, m).sorted().distinct().toArray();
    Profile p = new Profile(times);
    for (int i = 0; i < n; i++) {
      if (in[i]) {
        p.add(res.est(i), res.lct(i), res.r[i].max());
      }
    }
    return p;
  }

  /** A step function over the segments between consecutive time points. */
  private static final class Profile {
    final long[] times;
    final long[] height;

    Profile(long[] times) {
      this.times = times;
      this.height = new long[Math.max(times.length - 1, 0)];
    }

    void add(long from, long to, long h) {
      for (int k = Arrays.binarySearch(times, from); k < height.length && times[k] < to; k++) {
        height[k] += h;
      }
    }

    long max(long from, long to) {
      long max = 0;
      for (int k = Arrays.binarySearch(times, from); k < height.length && times[k] < to; k++) {
        max = Math.max(max, height[k]);
      }
      return max;
    }
  }

  /**
   * Fixes the starts that can move to a bound of their domain without violating any constraint.
   *
   * @return true if a start was fixed.
   */
  private boolean fix(Context context, List<Resource> resources) {
    // directions in which each start may move: bit 0 earlier, bit 1 later
    Map<IntVar, Integer> free = new IdentityHashMap<>();
    for (Resource res : resources) {
      if (res.size() > MAX_TASKS) {
        continue;
      }
      boolean[] all = new boolean[res.size()];
      Arrays.fill(all, true);
      Profile p = profile(res, all);
      long cap = res.limit.min();
      Map<IntVar, Integer> seen = new IdentityHashMap<>();
      for (int i = 0; i < res.size(); i++) {
        IntVar s = res.s[i];
        if (s.singleton()) {
          continue;
        }
        int ways = 3;
        if (seen.put(s, i) != null) {
          ways = 0;
        } else if (res.uses(i)) {
          long dmax = res.d[i].max();
          if (p.max(s.min(), s.min() + dmax) > cap) {
            ways &= ~1;
          }
          if (p.max(s.max(), s.max() + dmax) > cap) {
            ways &= ~2;
          }
        }
        free.merge(s, ways, (a, b) -> a & b);
      }
    }
    // a start in a resource the rule skips, or twice in one, is locked by it, and so is a
    // variable that is also a duration, resource use or limit
    for (Resource res : resources) {
      for (IntVar[] other : new IntVar[][] {res.d, res.r, {res.limit}}) {
        for (IntVar v : other) {
          free.put(v, 0);
        }
      }
      if (res.size() > MAX_TASKS) {
        for (IntVar s : res.s) {
          free.put(s, 0);
        }
      } else {
        Map<IntVar, Integer> count = new IdentityHashMap<>();
        for (IntVar s : res.s) {
          if (count.merge(s, 1, Integer::sum) > 1) {
            free.put(s, 0);
          }
        }
      }
    }
    free.values().removeIf(w -> w == 0);
    if (free.isEmpty()) {
      return false;
    }

    for (Constraint c : context.constraints()) {
      if (isResource(c) || c.isEntailed() || c instanceof SatisfiedPresent sp && sp.satisfied()) {
        continue;
      }
      LinearForm f = linearForm(c);
      for (Var v : c.arguments()) {
        Integer ways = free.get(v);
        if (ways != null) {
          free.put((IntVar) v, ways & ~locks(f, (IntVar) v));
        }
      }
    }
    for (Var v : locked) {
      free.computeIfPresent((IntVar) v, (k, w) -> 0);
    }
    if (objective != null) {
      // decreasing a minimized objective is no worse
      free.computeIfPresent(objective, (k, w) -> w & (minimize ? 1 : 2));
    }

    boolean fixed = false;
    // the starts are fixed in the order of the resources, so the result is deterministic
    for (Resource res : resources) {
      for (IntVar s : res.s) {
        Integer ways = free.remove(s);
        if (ways == null || ways == 0 || s.singleton()) {
          continue;
        }
        int value = (ways & 1) != 0 ? s.min() : s.max();
        s.domain.in(context.level(), s, value, value);
        fixedStarts++;
        fixed = true;
      }
    }
    return fixed;
  }

  private static LinearForm linearForm(Constraint c) {
    if (c instanceof LinearExplainable e) {
      return e.linearForm();
    }
    if (c instanceof LinearInt l) {
      return l.linearForm();
    }
    return null;
  }

  /**
   * Returns the directions in which moving a variable can violate a constraint: bit 0 for
   * decreasing it, bit 1 for increasing it.
   */
  private static int locks(LinearForm f, IntVar v) {
    if (f == null || f.relation() == LinearForm.EQ || f.relation() == LinearForm.NE) {
      return 3;
    }
    long w = 0;
    boolean found = false;
    for (int i = 0; i < f.vars().length; i++) {
      if (f.vars()[i] == v) {
        w += f.weights()[i];
        found = true;
      }
    }
    if (!found) {
      // the variable was folded away or is used in another way
      return v.singleton() ? 0 : 3;
    }
    if (w == 0) {
      return 0;
    }
    // sum <= c is violated by increasing a term with a positive weight
    boolean up = (w > 0) == (f.relation() == LinearForm.LE);
    return up ? 2 : 1;
  }

  /** Removes the tasks of a resource that can never overload it. */
  private void removeIrrelevant(Context context, Resource res) {
    int n = res.size();
    if (n > MAX_TASKS) {
      return;
    }
    boolean[] kept = new boolean[n];
    Arrays.fill(kept, true);
    long cap = res.limit.min();
    Profile p = profile(res, kept);
    int removed = 0;
    for (int i = 0; i < n; i++) {
      // a task removed earlier cannot overload the resource whatever the others do, so the profile
      // of the remaining tasks decides for the next ones
      if (!res.uses(i) || p.max(res.est(i), res.lct(i)) <= cap) {
        kept[i] = false;
        removed++;
        if (res.uses(i)) {
          p.add(res.est(i), res.lct(i), -res.r[i].max());
        }
      }
    }
    if (removed == 0) {
      return;
    }
    if (removed == n) {
      context.remove(res.constraint);
      removedResources++;
      return;
    }
    CumulativeBasic smaller = res.constraint.restrict(kept);
    if (smaller != null) {
      context.remove(res.constraint);
      context.impose(smaller);
      removedTasks += removed;
    }
  }

  /** Removes resources that another resource implies. */
  private void removeSubsumed(Context context, List<Resource> resources) {
    Map<IntVar, List<Integer>> byStart = new IdentityHashMap<>();
    for (int k = 0; k < resources.size(); k++) {
      for (IntVar s : resources.get(k).s) {
        List<Integer> l = byStart.computeIfAbsent(s, x -> new ArrayList<>());
        if (l.isEmpty() || l.getLast() != k) {
          l.add(k);
        }
      }
    }
    boolean[] gone = new boolean[resources.size()];
    for (int a = 0; a < resources.size(); a++) {
      Resource ra = resources.get(a);
      if (ra.size() == 0 || ra.size() > MAX_TASKS) {
        continue;
      }
      for (int b : byStart.get(ra.s[0])) {
        Resource rb = resources.get(b);
        if (b == a || gone[b] || rb.size() < ra.size() || rb.size() == ra.size() && b > a) {
          continue;
        }
        if (implies(rb, ra)) {
          gone[a] = true;
          context.remove(ra.constraint);
          removedResources++;
          break;
        }
      }
    }
  }

  /** Tells whether resource b implies resource a. */
  private static boolean implies(Resource b, Resource a) {
    boolean unary = unary(a) && unary(b);
    if (!unary && a.limit.min() < b.limit.max()) {
      return false;
    }
    for (int i = 0; i < a.size(); i++) {
      if (!a.uses(i)) {
        continue;
      }
      if (unary && a.r[i].max() > a.limit.min()) {
        // the task must fit the limit of a, which b does not check
        return false;
      }
      boolean found = false;
      for (int j = 0; j < b.size() && !found; j++) {
        found = b.s[j] == a.s[i] && same(b.d[j], a.d[i]) && (unary || same(b.r[j], a.r[i]));
      }
      if (!found) {
        return false;
      }
    }
    return true;
  }

  /**
   * Tells whether a resource is unary for every task that may use it: every task uses it, and any
   * two that run at the same time exceed the limit.
   */
  private static boolean unary(Resource res) {
    long smallest = Long.MAX_VALUE;
    long next = Long.MAX_VALUE;
    for (int i = 0; i < res.size(); i++) {
      if (res.d[i].max() <= 0) {
        continue;
      }
      long u = res.r[i].min();
      if (u <= 0) {
        return false;
      }
      if (u < smallest) {
        next = smallest;
        smallest = u;
      } else if (u < next) {
        next = u;
      }
    }
    return next == Long.MAX_VALUE || smallest + next > res.limit.max();
  }

  private static boolean same(IntVar x, IntVar y) {
    return x == y || x.singleton() && y.singleton() && x.value() == y.value();
  }
}
