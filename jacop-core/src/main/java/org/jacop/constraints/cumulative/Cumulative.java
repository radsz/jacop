/*
 * Cumulative.java
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

package org.jacop.constraints.cumulative;

import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Cumulative implements the scheduling constraint using.
 *
 * <p>edge-finding (edgeFind) algorithms based on
 *
 * <p>Petr Vilim, "Edge Finding Filtering Algorithm for Discrete Cumulative Resources in O(kn log
 * n)", Principles and Practice of Constraint Programming - CP 2009 Volume 5732 of the series
 * Lecture Notes in Computer Science pp 802-816.
 *
 * <p>and
 *
 * <p>Joseph Scott, "Filtering Algorithms for Discrete Cumulative Resources", MSc thesis, Uppsala
 * University, Department of Information Technology, 2010, no IT 10 048,
 *
 * <p>edge-finding algorithm with quadratic complexity (edgeFindQuad) is based on
 *
 * <p>Roger Kameugne, Laure Pauline Fotso, Joseph Scott, and Youcheu Ngo-Kateu, "A quadratic
 * edge-finding filtering algorithm for cumulative resource constraints", Constraints, 2014, July,
 * vol. 19, no. 3, pp. 243--269.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 * @see <a
 *     href="http://urn.kb.se/resolve?urn=urn:nbn:se:uu:diva-132172">http://urn.kb.se/resolve?urn=urn:nbn:se:uu:diva-132172</a>
 */
@Slf4j
public class Cumulative extends CumulativeBasic {

  protected final Comparator<TaskView> taskIncEstComparator =
      (o1, o2) -> o1.est() == o2.est() ? (o1.lct() - o2.lct()) : (o1.est() - o2.est());
  protected final Comparator<TaskView> taskDecLctComparator =
      (o1, o2) -> o2.lct() == o1.lct() ? (o2.est() - o1.est()) : (o2.lct() - o1.lct());
  final TaskView[] taskReversed;
  boolean doEdgeFind;
  boolean doQuadraticEdgeFind;
  boolean doOverload = true;
  boolean doTimeTableEdgeFind = true;
  boolean doTimeTableDisjunctive = true;
  // one per view, so that each keeps its task orders between calls
  final EnergyReasoning energy = new EnergyReasoning();
  final EnergyReasoning energyReversed = new EnergyReasoning();
  private TaskView[] optionalTasks;
  private boolean[] optionalPresent;
  private IntVar[] optionalVars;
  private int[] optionalIndex;

  /**
   * It creates a cumulative constraint.
   *
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   */
  public Cumulative(IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit) {

    super(starts, durations, resources, limit);

    taskReversed = new TaskReversedView[starts.length];
    for (int i = 0; i < starts.length; i++) {
      taskReversed[i] = new TaskReversedView(starts[i], durations[i], resources[i]);
      taskReversed[i].index = i;
    }

    checkLimitOverflow(limit);
    doEdgeFind = starts.length <= getEdgeFindSizeLimit();
  }

  /**
   * It creates a cumulative constraint.
   *
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   */
  public Cumulative(
      List<? extends IntVar> starts,
      List<? extends IntVar> durations,
      List<? extends IntVar> resources,
      IntVar limit) {

    this(
        starts.toArray(IntVar[]::new),
        durations.toArray(IntVar[]::new),
        resources.toArray(IntVar[]::new),
        limit);
  }

  private void checkLimitOverflow(IntVar limit) {
    if (limit != null) {
      for (Task t : taskNormal) {
        Math.addExact(t.start.max(), t.dur.max());
      }
    }
  }

  private static int getEdgeFindSizeLimit() {
    String s = System.getProperty("max_edge_find_size");
    int limitOnEdgeFind = 100;
    if (s != null) {
      limitOnEdgeFind = Integer.parseInt(s);
    }
    return limitOnEdgeFind;
  }

  /**
   * Sets whether to use the quadratic edge-finding algorithm.
   *
   * @param doQef true to enable quadratic edge-finding, false otherwise.
   */
  public void doQuadraticEdgeFind(boolean doQef) {
    doQuadraticEdgeFind = doQef;
  }

  /**
   * Sets whether to use edge finding. By default it is used for at most max_edge_find_size tasks (a
   * system property, 100 if not set).
   *
   * @param doEf true to enable edge finding, false otherwise.
   */
  public void doEdgeFind(boolean doEf) {
    doEdgeFind = doEf;
  }

  /**
   * Sets whether to use the O(n log n) overload check when neither edge finding nor time-table edge
   * finding is used (both include it). It is on by default.
   *
   * @param doOverloadCheck true to enable the overload check, false otherwise.
   */
  public void doOverload(boolean doOverloadCheck) {
    doOverload = doOverloadCheck;
  }

  /**
   * Sets whether to use time-table edge finding (Vilím, CPAIOR 2011; Schutt, Feydy and Stuckey,
   * CPAIOR 2013). It is on by default.
   *
   * @param doTtef true to enable time-table edge finding, false otherwise.
   */
  public void doTimeTableEdgeFind(boolean doTtef) {
    doTimeTableEdgeFind = doTtef;
  }

  /**
   * Sets whether to use time-table disjunctive reasoning (Gay, Hartert and Schaus, CPAIOR 2015). It
   * is on by default.
   *
   * @param doTtdr true to enable time-table disjunctive reasoning, false otherwise.
   */
  public void doTimeTableDisjunctive(boolean doTtdr) {
    doTimeTableDisjunctive = doTtdr;
  }

  @Override
  public void consistency(Store store) {

    do {

      store.propagationHasOccurred = false;

      profileProp(store);

      if (!store.propagationHasOccurred) {
        energyProp(store);
      }

      if (!store.propagationHasOccurred && doEdgeFind) {
        if (doQuadraticEdgeFind) {
          edgeFindQuad(store);
        } else {
          edgeFind(store);
        }
      }

    } while (store.propagationHasOccurred);
  }

  /**
   * Runs the energy based rules that need neither edge finding trees nor optional tasks: the
   * overload check (only without edge finding, which includes it), time-table disjunctive reasoning
   * and time-table edge finding, in both directions. It stops after the first rule that changes a
   * domain so that the cheaper rules run again first.
   */
  void energyProp(Store store) {

    // edge finding and time-table edge finding both detect every overload this check finds
    boolean overload = doOverload && !doEdgeFind && !doTimeTableEdgeFind;
    if (!overload && !doTimeTableDisjunctive && !doTimeTableEdgeFind) {
      return;
    }
    TaskView[] tn = filterZeroTasks(taskNormal);
    if (tn == null) {
      return;
    }
    TaskView[] tr = filterZeroTasks(taskReversed);
    int n = tn.length;
    long capacity = limit.max();

    energy.load(tn, n);
    energyReversed.load(tr, n);
    if (overload) {
      energy.overload(capacity, n);
    }
    if (doTimeTableDisjunctive) {
      energy.timeTableDisjunctive(tn, n, capacity, store);
      if (store.propagationHasOccurred) {
        energyReversed.load(tr, n);
      }
      energyReversed.timeTableDisjunctive(tr, n, capacity, store);
      if (store.propagationHasOccurred) {
        return;
      }
    }
    if (doTimeTableEdgeFind) {
      energy.timeTableEdgeFind(tn, n, capacity, store);
      if (store.propagationHasOccurred) {
        energyReversed.load(tr, n);
      }
      energyReversed.timeTableEdgeFind(tr, n, capacity, store);
    }
  }

  /**
   * Overload check with optional tasks: an optional task that cannot be added to the present tasks
   * without overloading the resource is made absent (opt = 0).
   *
   * @param store the store.
   * @param opt the presence variables of the tasks.
   * @param unit true if the tasks pairwise cannot overlap, so each uses one unit of a unary
   *     resource.
   */
  void optionalOverload(Store store, IntVar[] opt, boolean unit) {

    int n = collectOptional(opt);
    if (n == 0) {
      return;
    }
    energy.load(optionalTasks, n, unit);
    energy.overloadOptional(unit ? 1 : limit.max(), n, optionalPresent, optionalVars, store);
  }

  /**
   * Edge finding with optional tasks on a unary resource: an optional task that would have to start
   * after its latest start time is made absent. The tasks must pairwise not overlap.
   *
   * @param store the store.
   * @param opt the presence variables of the tasks.
   */
  void optionalEdgeFind(Store store, IntVar[] opt) {

    int n = collectOptional(opt);
    if (n == 0) {
      return;
    }
    energy.load(optionalTasks, n, true);
    energy.unaryEdgeFindOptional(n, optionalPresent, optionalVars, store);
    for (int i = 0; i < n; i++) {
      optionalTasks[i] = taskReversed[optionalIndex[i]];
    }
    energy.load(optionalTasks, n, true);
    energy.unaryEdgeFindOptional(n, optionalPresent, optionalVars, store);
  }

  /**
   * Collects the tasks that use the resource and are not absent.
   *
   * @return the number of collected tasks, or 0 if none of them is optional.
   */
  private int collectOptional(IntVar[] opt) {
    if (optionalTasks == null) {
      optionalTasks = new TaskView[taskNormal.length];
      optionalPresent = new boolean[taskNormal.length];
      optionalVars = new IntVar[taskNormal.length];
      optionalIndex = new int[taskNormal.length];
    }
    int k = 0;
    boolean anyOptional = false;
    for (int i = 0; i < taskNormal.length; i++) {
      if (taskNormal[i].exists() && opt[i].max() > 0) {
        optionalTasks[k] = taskNormal[i];
        optionalPresent[k] = opt[i].min() > 0;
        optionalVars[k] = opt[i];
        optionalIndex[k] = i;
        anyOptional |= !optionalPresent[k];
        k++;
      }
    }
    return anyOptional ? k : 0;
  }

  void edgeFind(Store store) {

    edgeFind(store, taskNormal);
    edgeFind(store, taskReversed);
  }

  private void edgeFind(Store store, TaskView[] tn) {

    // tasks sorted in non-decreasing order of est
    TaskView[] estList = filterZeroTasks(tn); // new TaskView[taskNormal.length];
    if (estList == null) {
      return;
    }

    Arrays.sort(estList, taskIncEstComparator);

    ThetaLambdaTree tree = new ThetaLambdaTree(limit);
    tree.buildTree(estList);

    // tasks sorted in non-increasing order of lct
    TaskView[] lctList = new TaskView[estList.length];
    System.arraycopy(estList, 0, lctList, 0, estList.length);
    Arrays.sort(lctList, taskDecLctComparator);

    int[] auxOrderListInv = new int[lctList.length];
    for (int i = 0; i < lctList.length; i++) {
      auxOrderListInv[lctList[i].index] = i;
    }

    // ========== Detect Order ============
    int[] prec = detectOrder(tree, lctList, auxOrderListInv, limit.max());
    // write ThetaLambdaTree as dot file for visualization

    // ========== Adjust Bounds ============
    adjustBounds(store, tree, lctList, prec, limit.max());
  }

  private int[] detectOrder(ThetaLambdaTree tree, TaskView[] t, int[] lctInvOrder, long capacity) {

    int n = t.length;
    int[] prec = initPrecFromEct(t, n);
    processTasksForPrec(tree, t, prec, capacity);
    return buildLctPrec(prec, lctInvOrder);
  }

  private static int[] initPrecFromEct(TaskView[] t, int n) {
    int[] prec = new int[n];
    for (TaskView aT1 : t) {
      prec[aT1.index] = aT1.ect();
    }
    return prec;
  }

  private void processTasksForPrec(ThetaLambdaTree tree, TaskView[] t, int[] prec, long capacity) {
    for (TaskView aT : t) {
      if (tree.rootNode().env > capacity * aT.lct()) {
        throw Store.failException;
      }
      while (tree.rootNode().envLambda > capacity * aT.lct()) {
        int i = tree.rootNode().responsibleEnvLambda;
        prec[tree.get(i).task.index] = Math.max(prec[tree.get(i).task.index], aT.lct());
        tree.removeFromLambda(i);
      }
      tree.moveToLambda(aT.treeIndex);
    }
  }

  private static int[] buildLctPrec(int[] prec, int[] lctInvOrder) {
    int[] lctPrec = new int[prec.length];
    for (int i = 0; i < prec.length; i++) {
      lctPrec[lctInvOrder[i]] = prec[i];
    }
    return lctPrec;
  }

  private void adjustBounds(Store store, ThetaLambdaTree tree, TaskView[] t, int[] prec, long cap) {

    int n = t.length;
    if (capMap == null || capMap.length < n) {
      capMap = new int[taskNormal.length];
      capacities = new int[taskNormal.length];
      orderKeys = new long[taskNormal.length];
    }
    // distinct minimal resource uses; the map is rebuilt on every call since task indexes change
    // between calls (sweep pruning and filtering of zero and absent tasks renumber them)
    for (int i = 0; i < n; i++) {
      capacities[i] = t[i].res.min();
    }
    Arrays.sort(capacities, 0, n);
    int k = 0;
    for (int i = 0; i < n; i++) {
      if (i == 0 || capacities[i] != capacities[i - 1]) {
        capacities[k++] = capacities[i];
      }
    }
    for (TaskView aT : t) {
      capMap[aT.index] = Arrays.binarySearch(capacities, 0, k, aT.res.min());
    }
    if (update == null || update.length < k * n) {
      update = new int[k * n];
    }

    fillUpdateMatrix(tree, t, k, cap, n);
    applyPrecOrderUpdates(store, t, prec, n);
  }

  // buffers of edge finding reused between calls
  private int[] capMap;
  private int[] capacities;
  private int[] update;
  private long[] orderKeys;

  private void fillUpdateMatrix(ThetaLambdaTree tree, TaskView[] t, int k, long cap, int n) {
    for (int capi = 0; capi < k; capi++) {
      int ci = capacities[capi];
      tree.clearTree();
      int upd = Integer.MIN_VALUE;
      for (int l = n - 1; l >= 0; l--) {
        tree.enableNode(t[l].treeIndex, ci);
        long envlc = tree.calcEnvlc(t[l].lct(), ci);
        int diff = Integer.MIN_VALUE;
        if (envlc != Long.MIN_VALUE) {
          long tmp = envlc - (cap - ci) * t[l].lct();
          diff = long2int(IntDomain.divRoundUp(tmp, ci));
        }
        upd = Math.max(upd, diff);
        update[capi * n + l] = upd;
      }
    }
  }

  private void applyPrecOrderUpdates(Store store, TaskView[] t, int[] prec, int n) {
    // tasks by non-increasing prec, ties by position
    for (int i = 0; i < n; i++) {
      orderKeys[i] = ((long) prec[i] << 32) | (Integer.MAX_VALUE - i);
    }
    Arrays.sort(orderKeys, 0, n);

    int j = 0;
    for (int o = n - 1; o >= 0; o--) {
      int i = Integer.MAX_VALUE - (int) (orderKeys[o] & 0xFFFFFFFFL);
      TaskView taskI = t[i];
      int precI = prec[i];
      while (j < n && t[j].lct() > precI) {
        j++;
      }
      if (j >= n) {
        break;
      }
      int nj = j;
      while (nj < n && t[nj].lct() == precI) {
        if (t[nj].lct() < taskI.lct()) {
          taskI.updateEdgeFind(store.level, update[capMap[taskI.index] * n + nj]);
          break;
        }
        nj++;
      }
    }
  }

  void edgeFindQuad(Store store) {

    edgeFindQuad(store, taskNormal);
    edgeFindQuad(store, taskReversed);
  }

  private void edgeFindQuad(Store store, TaskView[] tn) {

    final long capacity = limit.max();
    TaskView[] ts = filterZeroTasks(tn);
    if (ts == null) {
      return;
    }

    int n = ts.length;
    QuadArrays q = quadArrays(n);

    // tasks sorted by non-decreasing deadline (lct), ties by position
    for (int i = 0; i < n; i++) {
      q.keys[i] = ((long) ts[i].lct() << 32) | i;
    }
    Arrays.sort(q.keys, 0, n);
    for (int k = 0; k < n; k++) {
      TaskView t = ts[(int) q.keys[k]];
      q.tasks[k] = t;
      q.est[k] = t.est();
      q.lct[k] = t.lct();
      q.ect[k] = t.ect();
      q.energy[k] = t.energy();
      q.resMin[k] = t.res.min();
      q.resMax[k] = t.res.max();
      q.lb[k] = q.est[k];
    }
    Arrays.fill(q.dupd, 0, n, Integer.MIN_VALUE);
    Arrays.fill(q.slUpd, 0, n, Integer.MIN_VALUE);

    // t1 by non-increasing release date (est), t2 by non-decreasing est; ties by lct order
    for (int k = 0; k < n; k++) {
      q.keys[k] = ((long) -q.est[k] << 32) | k;
    }
    Arrays.sort(q.keys, 0, n);
    for (int k = 0; k < n; k++) {
      q.t1[k] = (int) q.keys[k];
      q.keys[k] = ((long) q.est[k] << 32) | k;
    }
    Arrays.sort(q.keys, 0, n);
    for (int k = 0; k < n; k++) {
      q.t2[k] = (int) q.keys[k];
    }

    for (int u = 0; u < n; u++) {
      edgeFindQuadProcessU(q, n, u, capacity);
    }

    // update LB's
    for (int k = 0; k < n; k++) {
      q.tasks[k].updateEdgeFind(store.level, q.lb[k]);
    }
  }

  /** Reusable arrays of the quadratic edge finding, indexed by the lct order of the tasks. */
  private static final class QuadArrays {
    final TaskView[] tasks;
    final int[] est;
    final int[] lct;
    final int[] ect;
    final long[] energy;
    final int[] resMin;
    final int[] resMax;
    final int[] lb;
    final int[] dupd;
    final int[] slUpd;
    final long[] energyPrefix;
    final int[] t1;
    final int[] t2;
    final long[] keys;

    QuadArrays(int n) {
      tasks = new TaskView[n];
      est = new int[n];
      lct = new int[n];
      ect = new int[n];
      energy = new long[n];
      resMin = new int[n];
      resMax = new int[n];
      lb = new int[n];
      dupd = new int[n];
      slUpd = new int[n];
      energyPrefix = new long[n];
      t1 = new int[n];
      t2 = new int[n];
      keys = new long[n];
    }
  }

  private QuadArrays quadArrays;

  private QuadArrays quadArrays(int n) {
    if (quadArrays == null || quadArrays.est.length < n) {
      quadArrays = new QuadArrays(taskNormal.length);
    }
    return quadArrays;
  }

  private static void edgeFindQuadProcessU(QuadArrays q, int n, int u, long capacityLimit) {
    long energy = 0;
    long maxEnergy = 0;
    int rr = Integer.MIN_VALUE;
    final int lctU = q.lct[u];

    for (int k = 0; k < n; k++) {
      int i = q.t1[k];
      if (q.lct[i] <= lctU) {
        energy += q.energy[i];
        if (rr == Integer.MIN_VALUE
            || (double) energy / (lctU - q.est[i]) > (double) maxEnergy / (lctU - rr)) {
          maxEnergy = energy;
          rr = q.est[i];
        }
      } else if (rr != Integer.MIN_VALUE) {
        long rest = maxEnergy - (capacityLimit - q.resMin[i]) * (lctU - rr);
        if (rest > 0) {
          q.dupd[i] = (int) Math.max(q.dupd[i], rr + IntDomain.divRoundUp(rest, q.resMax[i]));
        }
        if (maxEnergy + (long) q.resMin[i] * (q.ect[i] - rr) > capacityLimit * (lctU - rr)) {
          q.lb[i] = Math.max(q.lb[i], q.dupd[i]);
        }
      }
      q.energyPrefix[i] = energy;
    }

    long minSl = Integer.MAX_VALUE;
    int rt = lctU;
    for (int k = 0; k < n; k++) {
      int i = q.t2[k];
      if (capacityLimit * (lctU - q.est[i]) - q.energyPrefix[i] < minSl) {
        rt = q.est[i];
        minSl = capacityLimit * (lctU - rt) - q.energyPrefix[i];
      }
      if (q.lct[i] > lctU) {
        long rest = (long) q.resMin[i] * (lctU - rt) - minSl;
        if (rt <= lctU && rest > 0) {
          q.slUpd[i] = (int) Math.max(q.slUpd[i], rt + IntDomain.divRoundUp(rest, q.resMax[i]));
        }
        if (q.ect[i] >= lctU || minSl - q.energy[i] < 0) {
          q.lb[i] = Math.max(Math.max(q.lb[i], q.dupd[i]), q.slUpd[i]);
        }
      }
    }
  }

  TaskView[] filterZeroTasks(TaskView[] ts) {

    if (possibleZeroTasks) {
      TaskView[] nonZeroTasks = new TaskView[ts.length];
      int k = 0;

      for (TaskView t1 : ts) {
        if (t1.exists()) {
          nonZeroTasks[k] = t1;
          t1.index = k++;
        }
      }

      if (k == 0) {
        return null;
      }
      TaskView[] t = new TaskView[k];
      System.arraycopy(nonZeroTasks, 0, t, 0, k);
      return t;
    } else {
      return ts;
    }
  }

  /**
   * Builds the common prefix of the toString representation.
   *
   * @param constraintName the name of the constraint (e.g., "cumulative", "cumulativeOptional")
   * @return StringBuilder with the common prefix
   */
  protected StringBuilder buildToStringPrefix(String constraintName) {

    StringBuilder result = new StringBuilder(id());
    if (doEdgeFind) {
      result.append(" : ").append(constraintName).append("([ ");
    } else if (super.cumulativeForConstants != null) {
      result.append(" : cumulativePrimary([ ");
    } else {
      result.append(" : cumulativeBasic([ ");
    }

    for (int i = 0; i < taskNormal.length - 1; i++) {
      result.append(taskNormal[i]).append(", ");
    }

    result.append(taskNormal[taskNormal.length - 1]);

    return result;
  }

  @Override
  public String toString() {

    StringBuilder result = buildToStringPrefix("cumulative");

    result
        .append(" ]")
        .append(", limit = ")
        .append(limit)
        .append(", quad=")
        .append(doQuadraticEdgeFind)
        .append(", ttef=")
        .append(doTimeTableEdgeFind)
        .append(", ttdr=")
        .append(doTimeTableDisjunctive)
        .append(" )");

    return result.toString();
  }
}
