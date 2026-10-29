/*
 * ReplayExplanation.java
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

package org.jacop.lcg;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import org.jacop.constraints.Constraint;
import org.jacop.core.FailException;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Explanations of a constraint that gives none of its own, found by running a copy of its
 * propagator again. The generic reason (the atoms of every variable of the constraint) is split
 * into groups, the lower bound, the upper bound and the holes of each variable, and QuickXplain
 * (Junker, "QuickXplain: preferred explanations and relaxations for over-constrained problems",
 * AAAI 2004) finds a subset of groups with which the copy, over the initial domains, still fails
 * once the explained atom is negated (or, for a failure, fails at all). Since the propagator is
 * sound, such a subset is a valid reason. Groups recorded at lower store levels are preferred, so
 * that the reason keeps the atoms that stay in a learnt clause rather than those resolved away.
 *
 * <p>The copy lives in a scratch store of its own, kept for the constraint, and each test imposes
 * the atoms at a new level that is removed afterwards. A constraint whose copy does not fail with
 * the whole generic reason (a propagator that depends on state the copy lacks) gets the generic
 * reason. Constraints with more than {@link #MAX_GROUPS} groups in a reason are not minimized:
 * QuickXplain needs about k log(n / k) tests for a reason of k groups out of n. Replaying is also
 * bounded in time: over all constraints to {@link #SHARE} of the time since the first replay, and
 * for one constraint to half of that.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class ReplayExplanation {

  /**
   * Reasons with more groups than this get the generic reason ({@code -Djacop.lcg.replayGroups}).
   */
  static final int MAX_GROUPS = Integer.getInteger("jacop.lcg.replayGroups", 256);

  /** Whether replayed explanations are used ({@code -Djacop.lcg.replay}, true by default). */
  static final boolean ENABLED =
      Boolean.parseBoolean(System.getProperty("jacop.lcg.replay", "true"));

  /**
   * The largest share of the time since the first replay that replaying may take, over all
   * constraints and for each one ({@code -Djacop.lcg.replayShare}, 0.25 by default); beyond it the
   * generic reason is given. A propagator as costly as edge finding could otherwise spend most of
   * the search in its own replays.
   */
  static final double SHARE =
      Double.parseDouble(System.getProperty("jacop.lcg.replayShare", "0.25"));

  // replaying one constraint may take this long before its share of the time applies
  private static final long GRACE = 50_000_000L;

  private long nanos;

  // a constraint whose copy failed to reproduce this many reasons in a row stops being replayed
  private static final int MAX_MISSES = 32;

  private final AtomicTrail trail;
  private final Constraint constraint;
  private final ScratchCopy scratch;
  private final int baseLevel;
  private int misses;
  private boolean disabled;

  // the groups of the reason being minimized: entries[groupStart[g] .. groupStart[g + 1])
  private int[] entries = new int[16];
  private int[] groupStart = new int[16];
  private int numGroups;
  private int target;

  private ReplayExplanation(AtomicTrail trail, Constraint constraint, ScratchCopy scratch) {
    this.trail = trail;
    this.constraint = constraint;
    this.scratch = scratch;
    scratch.imposeCopy(constraint);
    boolean consistent;
    try {
      consistent = scratch.store.consistency();
    } catch (FailException _) {
      consistent = false;
    }
    disabled = !consistent;
    baseLevel = scratch.store.level;
  }

  /**
   * Creates the replay of a constraint.
   *
   * @return the replay, or null when the constraint cannot be copied
   */
  static ReplayExplanation of(AtomicTrail trail, Constraint c) {
    ScratchCopy scratch = ScratchCopy.of(trail, c);
    if (scratch == null) {
      return null;
    }
    try {
      return new ReplayExplanation(trail, c, scratch);
    } catch (RuntimeException _) {
      // a copy that cannot be imposed alone
      return null;
    }
  }

  /**
   * Adds to {@code out} a reason of an entry (or of a failure, for a negative entry) found by
   * replaying the constraint at a trail position.
   *
   * @param entry the entry, or -1 for a failure now
   * @param out where the entries are added
   * @param elapsed the time since the first replay of any constraint, in nanoseconds
   * @return false when no reason was found this way
   */
  boolean explain(int entry, EntryList out, long elapsed) {
    if (disabled || nanos > SHARE * elapsed / 2 + GRACE) {
      return false;
    }
    long start = System.nanoTime();
    try {
      return replay(entry, out);
    } finally {
      nanos += System.nanoTime() - start;
    }
  }

  private boolean replay(int entry, EntryList out) {
    target = entry;
    int position = entry < 0 ? trail.size() : entry;
    collectGroups(position);
    if (numGroups > MAX_GROUPS) {
      return false;
    }
    int[] all = new int[numGroups];
    for (int g = 0; g < numGroups; g++) {
      all[g] = g;
    }
    if (!fails(all, all.length)) {
      if (++misses >= MAX_MISSES) {
        disabled = true;
      }
      return false;
    }
    misses = 0;
    if (numGroups == 0) {
      return true;
    }
    List<Integer> chosen = new ArrayList<>();
    quickXplain(new int[0], 0, all, 0, all.length, false, chosen);
    for (int g : chosen) {
      for (int k = groupStart[g]; k < groupStart[g + 1]; k++) {
        out.add(entries[k]);
      }
    }
    return true;
  }

  /**
   * Finds a minimal subset of the candidate groups {@code c[from, to)} that fails with the
   * background groups, and adds it to {@code chosen}. The candidates are ordered by preference.
   */
  private void quickXplain(
      int[] background,
      int backgroundSize,
      int[] c,
      int from,
      int to,
      boolean delta,
      List<Integer> chosen) {
    if (delta && fails(background, backgroundSize)) {
      return;
    }
    if (to - from == 1) {
      chosen.add(c[from]);
      return;
    }
    int mid = (from + to) >>> 1;
    // the preferred first half is the background of the search in the second half
    int[] b1 = Arrays.copyOf(background, backgroundSize + (mid - from));
    System.arraycopy(c, from, b1, backgroundSize, mid - from);
    List<Integer> second = new ArrayList<>();
    quickXplain(b1, b1.length, c, mid, to, true, second);
    int[] b2 = Arrays.copyOf(background, backgroundSize + second.size());
    for (int k = 0; k < second.size(); k++) {
      b2[backgroundSize + k] = second.get(k);
    }
    List<Integer> first = new ArrayList<>();
    quickXplain(b2, b2.length, c, from, mid, !second.isEmpty(), first);
    chosen.addAll(first);
    chosen.addAll(second);
  }

  // whether the copy fails with the atoms of the groups and the explained atom negated
  private boolean fails(int[] groups, int size) {
    Store store = scratch.store;
    store.setLevel(baseLevel + 1);
    boolean failed;
    try {
      for (int k = 0; k < size; k++) {
        imposeGroup(groups[k]);
      }
      if (target >= 0) {
        scratch.imposeNegation(target);
      }
      failed = !store.consistency();
    } catch (FailException _) {
      failed = true;
    }
    store.clearChanged();
    store.removeLevel(baseLevel + 1);
    store.setLevel(baseLevel);
    return failed;
  }

  private void imposeGroup(int g) {
    for (int k = groupStart[g]; k < groupStart[g + 1]; k++) {
      scratch.impose(entries[k]);
    }
  }

  /**
   * Splits the generic reason at a position into groups: the lower bound, the upper bound and the
   * holes of each variable, ordered by the highest store level among their entries.
   */
  private void collectGroups(int position) {
    EntryList atoms = new EntryList();
    List<int[]> groups = new ArrayList<>();
    for (Var v : constraint.arguments()) {
      atoms.clear();
      trail.atomsBefore(v, position, atoms);
      List<Integer> holes = new ArrayList<>();
      for (int k = 0; k < atoms.size(); k++) {
        int f = atoms.get(k);
        if (trail.kind(f) == AtomicTrail.NE) {
          holes.add(f);
        } else {
          groups.add(new int[] {f});
        }
      }
      if (!holes.isEmpty()) {
        groups.add(holes.stream().mapToInt(Integer::intValue).toArray());
      }
    }
    groups.sort((p, q) -> Integer.compare(maxLevel(p), maxLevel(q)));
    numGroups = groups.size();
    if (groupStart.length < numGroups + 1) {
      groupStart = new int[2 * numGroups + 1];
    }
    int n = 0;
    for (int g = 0; g < numGroups; g++) {
      groupStart[g] = n;
      for (int f : groups.get(g)) {
        if (n == entries.length) {
          entries = Arrays.copyOf(entries, 2 * n);
        }
        entries[n++] = f;
      }
    }
    groupStart[numGroups] = n;
  }

  private int maxLevel(int[] group) {
    int l = 0;
    for (int f : group) {
      l = Math.max(l, trail.level(f));
    }
    return l;
  }
}
