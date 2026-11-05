/*
 * Nooverlap.java This file is part of JaCoP.
 *
 * <p>JaCoP is a Java Constraint Programming solver.
 *
 * <p>Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 * <p>This program is free software: you can redistribute it and/or modify it under the terms of the
 * GNU Affero General Public License as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * <p>This program is distributed in the hope that it will be useful, but WITHOUT ANY WARRANTY;
 * without even the implied warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Affero General Public License for more details.
 *
 * <p>Notwithstanding any other provision of this License, the copyright owners of this work
 * supplement the terms of this License with terms prohibiting misrepresentation of the origin of
 * this work and requiring that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license terms is in accordance with
 * Section 7 of GNU Affero General Public License version 3.
 *
 * <p>You should have received a copy of the GNU Affero General Public License along with this
 * program. If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.constraints.diffn;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.Stateful;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.PbEncodable;
import org.jacop.lcg.PbModel;
import org.jacop.util.VarIntMap;

/**
 * Nooverlap constraint assures that any two rectangles from a vector of rectangles does not overlap
 * in at least one direction. It is a simple implementation which does not use sophisticated
 * techniques for efficient backtracking.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class Nooverlap extends Constraint
    implements Copyable<Nooverlap>, Explainable, Stateful, PbEncodable {

  static final int X = 0;
  static final int Y = 1;
  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * Defines how to treat rectangles with width zero strict = true means they still need to be
   * between other rectangles strict = false these rectangles can be anywhere.
   */
  boolean strict = true;

  // whether pruning also fails on the area and the count of the rectangles that may overlap one
  private boolean energyCheck = true;

  Store store;

  /** It specifies the list of rectangles which are of interest for this diff constraint. */
  Rectangle[] rectangle;

  /** Defines first position of the variable that is not ground to 1. */
  TimeStamp<BitSet>[] overlapping;

  boolean doAreaCheck = true;

  // bounds of the rectangles per dimension, read again whenever a domain changed (see syncBounds)
  int[][] est;
  int[][] lst;
  int[][] lMin;
  int[][] lMax;
  private long boundsStamp = -1;
  private int[] readAt;
  private int epoch;

  /*
   * What a pass of the pairwise pruning, the profile or the area check finds for a rectangle depends
   * only on the bounds of the rectangle and of the rectangles that may overlap it. A pass examines
   * a rectangle again only if one of them changed since the previous pass of the same kind began;
   * otherwise the previous pass already found nothing for it. Each pass that runs to its end without
   * a change leaves every rectangle examined, so the constraint is at its fixpoint at the end of
   * each search node and nothing needs to be examined again after a backtrack.
   */
  static final int PRUNING_PASS = 0;
  static final int PROFILE_PASS = 1;
  static final int AREA_PASS = 2;

  /*
   * The profile of another rectangle uses a rectangle only while it has a compulsory part, and a
   * rectangle that has none now had none since the previous pass, since compulsory parts only grow
   * until a backtrack. So the profile pass tracks such rectangles apart from all changed ones.
   */
  static final int PROFILE_OF_OTHERS = 3;

  /** For each kind of pass, the rectangles changed since the current pass of that kind began. */
  private final BitSet[] changed = new BitSet[4];

  /** For each kind of pass, the rectangles changed since the previous pass of that kind began. */
  private final BitSet[] changedBefore = new BitSet[4];

  /** The position in {@link #rectanglesOf} of each variable. */
  private VarIntMap rectanglesSlot;

  /** The rectangles of each variable, by its slot. */
  private int[][] rectanglesOf;

  /**
   * It specifies a diff constraint.
   *
   * @param rectangle list of rectangles which can not overlap in at least one dimension.
   */
  public Nooverlap(IntVar[][] rectangle) {

    if (rectangle == null) {
      throw new IllegalArgumentException("Rectangles list is null");
    }

    this.queueIndex = 2;
    this.numberId = idNumber.incrementAndGet();

    this.rectangle = new Rectangle[rectangle.length];

    for (int i = 0; i < rectangle.length; i++) {
      if (rectangle[i] == null) {
        throw new IllegalArgumentException(i + "-th rectangle in the list is null");
      }
      if (rectangle[i].length != 4) {
        throw new IllegalArgumentException("The rectangle has to have exactly two dimensions");
      }
      this.rectangle[i] =
          new Rectangle(rectangle[i][0], rectangle[i][1], rectangle[i][2], rectangle[i][3]);
      this.rectangle[i].index = i;
    }

    setScope(Rectangle.getStream(this.rectangle));
  }

  /**
   * It specifies a diff constraint.
   *
   * @param rectangle list of rectangles which can not overlap in at least one dimension.
   * @param strict true- zero size rectangles need to be between other rectangles; false- these
   *     rectangles can be anywhere
   */
  public Nooverlap(IntVar[][] rectangle, boolean strict) {
    this(rectangle);
    this.strict = strict;
  }

  /**
   * It constructs a diff constraint.
   *
   * @param origin1 list of variables denoting origin of the rectangle in the first dimension.
   * @param origin2 list of variables denoting origin of the rectangle in the second dimension.
   * @param length1 list of variables denoting length of the rectangle in the first dimension.
   * @param length2 list of variables denoting length of the rectangle in the second dimension.
   */
  public Nooverlap(IntVar[] origin1, IntVar[] origin2, IntVar[] length1, IntVar[] length2) {

    checkInputForNullness(
        new String[] {"origin1", "origin2", "length1", "length2"},
        origin1,
        origin2,
        length1,
        length2);

    int size = origin1.length;
    if (size == origin2.length && size == length1.length && size == length2.length) {

      this.queueIndex = 2;

      this.numberId = idNumber.incrementAndGet();

      this.rectangle = new Rectangle[size];

      for (int i = 0; i < size; i++) {
        this.rectangle[i] = new Rectangle(origin1[i], origin2[i], length1[i], length2[i]);
        this.rectangle[i].index = i;
      }
    } else {
      String s = "\nNot equal sizes of Variable vectors in Nooverlap";
      throw new IllegalArgumentException(s);
    }

    setScope(Rectangle.getStream(this.rectangle));
  }

  /**
   * It constructs a diff constraint.
   *
   * @param origin1 list of variables denoting origin of the rectangle in the first dimension.
   * @param origin2 list of variables denoting origin of the rectangle in the second dimension.
   * @param length1 list of variables denoting length of the rectangle in the first dimension.
   * @param length2 list of variables denoting length of the rectangle in the second dimension.
   * @param strict true- zero size rectangles need to be between other rectangles; false- these
   *     rectangles can be anywhere
   */
  public Nooverlap(
      IntVar[] origin1, IntVar[] origin2, IntVar[] length1, IntVar[] length2, boolean strict) {
    this(origin1, origin2, length1, length2);
    this.strict = strict;
  }

  /**
   * It specifies a diffn constraint.
   *
   * @param rectangle list of rectangles which can not overlap in at least one dimension.
   */
  public Nooverlap(List<? extends List<? extends IntVar>> rectangle) {

    queueIndex = 2;
    numberId = idNumber.incrementAndGet();

    this.rectangle = new Rectangle[rectangle.size()];

    int i = 0;

    for (List<? extends IntVar> r : rectangle) {
      if (r.size() == 4) {
        this.rectangle[i] =
            new Rectangle(
                rectangle.get(i).getFirst(),
                rectangle.get(i).get(1),
                rectangle.get(i).get(2),
                rectangle.get(i).get(3));
        this.rectangle[i].index = i;
        i++;
      } else {
        String s = "\nNot equal sizes of rectangle vectors in Nooverlap";
        throw new IllegalArgumentException(s);
      }
    }

    setScope(Rectangle.getStream(this.rectangle));
  }

  /**
   * It specifies a diffn constraint.
   *
   * @param rectangle list of rectangles which can not overlap in at least one dimension.
   * @param strict true- zero size rectangles need to be between other rectangles; false- these
   *     rectangles can be anywhere
   */
  public Nooverlap(List<? extends List<? extends IntVar>> rectangle, boolean strict) {
    this(rectangle);
    this.strict = strict;
  }

  /**
   * It constructs a diff constraint.
   *
   * @param o1 list of variables denoting origin of the rectangle in the first dimension.
   * @param o2 list of variables denoting origin of the rectangle in the second dimension.
   * @param l1 list of variables denoting length of the rectangle in the first dimension.
   * @param l2 list of variables denoting length of the rectangle in the second dimension.
   */
  public Nooverlap(
      List<? extends IntVar> o1,
      List<? extends IntVar> o2,
      List<? extends IntVar> l1,
      List<? extends IntVar> l2) {

    this(
        o1.toArray(IntVar[]::new),
        o2.toArray(IntVar[]::new),
        l1.toArray(IntVar[]::new),
        l2.toArray(IntVar[]::new));
  }

  /**
   * It constructs a diff constraint.
   *
   * @param o1 list of variables denoting origin of the rectangle in the first dimension.
   * @param o2 list of variables denoting origin of the rectangle in the second dimension.
   * @param l1 list of variables denoting length of the rectangle in the first dimension.
   * @param l2 list of variables denoting length of the rectangle in the second dimension.
   * @param strict true- zero size rectangles need to be between other rectangles; false- these
   *     rectangles can be anywhere
   */
  public Nooverlap(
      List<? extends IntVar> o1,
      List<? extends IntVar> o2,
      List<? extends IntVar> l1,
      List<? extends IntVar> l2,
      boolean strict) {
    this(o1, o2, l1, l2);
    this.strict = strict;
  }

  /**
   * Turns off the failures on the area and the count of the rectangles that may overlap one, so
   * that every failure and pruning follows from a pair of rectangles. A proof of the pairwise
   * encoding then follows each step by unit propagation.
   *
   * @return this constraint
   */
  public Nooverlap pairwiseOnly() {
    energyCheck = false;
    return this;
  }

  @Override
  public void consistency(Store store) {

    this.store = store;

    do {
      store.propagationHasOccurred = false;

      pruning();

    } while (store.propagationHasOccurred);
  }

  /**
   * Performs constraint propagation by pruning domains of rectangle variables. Checks for overlaps
   * and applies energy-based reasoning to detect infeasibility.
   */
  void pruning() {

    startPass(PRUNING_PASS);
    invalidateBounds();
    // the area check runs in Diffn if the last rectangle checked here asks for it
    int last = -1;
    boolean lastExamined = false;
    for (int j = 0; j < rectangle.length; j++) {
      Rectangle r = rectangle[j];

      BitSet os = overlapping[j].value();
      if (r.instantiatedBefore(store)) {
        if (!os.isEmpty()) {
          overlapping[j].update(new BitSet());
        }
        continue;
      }
      last = j;
      lastExamined = mustExamine(PRUNING_PASS, j, os);
      if (!lastExamined) {
        continue;
      }
      syncBounds();
      bounds(j);
      BitSet o = os;
      for (int i = os.nextSetBit(0); i >= 0; i = os.nextSetBit(i + 1)) {
        bounds(i);
        if (!possibleOverlap(j, i)) {
          if (o == os) {
            o = (BitSet) os.clone();
          }
          o.clear(i);
        }
      }
      if (o != os) {
        // the profile and the area check of r depend on the rectangles that may overlap it
        changed[PROFILE_PASS].set(j);
        changed[AREA_PASS].set(j);
        overlapping[j].update(o);
      }

      if (energyCheck) {
        energyCheck(j, o);
      }

      prune(r, o);
    }
    if (last >= 0 && !lastExamined) {
      doAreaCheck = areaExceedsSpace(rectangle[last], overlapping[last].value());
    }
  }

  /** Marks the bounds read by syncBounds as out of date, as at the start of a consistency call. */
  void invalidateBounds() {
    boundsStamp = -1;
  }

  /**
   * Starts a new reading of the bounds into est, lst, lMin and lMax if a domain changed since the
   * last one in this consistency call. A rectangle's bounds are then read on first use, see bounds.
   */
  void syncBounds() {
    long stamp = store.domainChanges();
    if (stamp == boundsStamp) {
      return;
    }
    if (est == null) {
      int n = rectangle.length;
      est = new int[2][n];
      lst = new int[2][n];
      lMin = new int[2][n];
      lMax = new int[2][n];
      readAt = new int[n];
    }
    epoch++;
    boundsStamp = stamp;
  }

  /**
   * Makes est, lst, lMin and lMax of rectangle i current. A changed variable can belong to several
   * rectangles, so any domain change makes syncBounds start a new reading of all of them.
   *
   * @param i the rectangle.
   */
  void bounds(int i) {
    if (readAt[i] == epoch) {
      return;
    }
    Rectangle r = rectangle[i];
    for (int d = 0; d < 2; d++) {
      est[d][i] = r.origin[d].min();
      lst[d][i] = r.origin[d].max();
      lMin[d][i] = r.length[d].min();
      lMax[d][i] = r.length[d].max();
    }
    readAt[i] = epoch;
  }

  // Rectangle.possibleOverlap on the bounds read by syncBounds
  private boolean possibleOverlap(int a, int b) {
    for (int d = 0; d < 2; d++) {
      if (est[d][a] >= lst[d][b] + lMax[d][b] || est[d][b] >= lst[d][a] + lMax[d][a]) {
        return false;
      }
    }
    return true;
  }

  // Rectangle.overlap on the bounds read by syncBounds
  private boolean overlap(int a, int b, int d) {
    int lstA = lst[d][a];
    int ectA = est[d][a] + lMin[d][a];
    int lstB = lst[d][b];
    int ectB = est[d][b] + lMin[d][b];
    return (lstA < ectA && ectB > lstA && ectA > lstB)
        || (lstB < ectB && ectA > lstB && ectB > lstA);
  }

  /**
   * Begins a pass of the given kind.
   *
   * @param pass the kind of pass.
   */
  void startPass(int pass) {
    swap(pass);
    if (pass == PROFILE_PASS) {
      swap(PROFILE_OF_OTHERS);
    }
  }

  private void swap(int set) {
    BitSet b = changedBefore[set];
    changedBefore[set] = changed[set];
    b.clear();
    changed[set] = b;
  }

  /**
   * Tells whether a pass has to examine a rectangle, that is, whether the rectangle or one that may
   * overlap it changed since the previous pass of the same kind began.
   *
   * @param pass the kind of pass.
   * @param j the index of the rectangle.
   * @param o the rectangles that may overlap it.
   * @return true if the rectangle has to be examined.
   */
  boolean mustExamine(int pass, int j, BitSet o) {
    int others = pass == PROFILE_PASS ? PROFILE_OF_OTHERS : pass;
    return changedBefore[pass].get(j)
        || changed[pass].get(j)
        || o.intersects(changedBefore[others])
        || o.intersects(changed[others]);
  }

  @Override
  public void queueVariable(int level, Var v) {
    int slot = rectanglesSlot.get(v);
    if (slot == VarIntMap.ABSENT) {
      return;
    }
    for (int j : rectanglesOf[slot]) {
      changed[PRUNING_PASS].set(j);
      changed[PROFILE_PASS].set(j);
      changed[AREA_PASS].set(j);
      if (hasCompulsoryPart(rectangle[j])) {
        changed[PROFILE_OF_OTHERS].set(j);
      }
    }
  }

  @Override
  public void removeLevel(int level) {
    // the store goes back to the end of a search node, where every pass found nothing; the area
    // check does not run in every call, so it examines all rectangles again
    changed[PRUNING_PASS].clear();
    changedBefore[PRUNING_PASS].clear();
    changed[PROFILE_PASS].clear();
    changedBefore[PROFILE_PASS].clear();
    changed[PROFILE_OF_OTHERS].clear();
    changedBefore[PROFILE_OF_OTHERS].clear();
    changed[AREA_PASS].set(0, rectangle.length);
  }

  // whether the profile of another rectangle in some dimension uses r
  private static boolean hasCompulsoryPart(Rectangle r) {
    return r.lst(X) < r.ect(X) && r.getLength(Y).min() > 0
        || r.lst(Y) < r.ect(Y) && r.getLength(X).min() > 0;
  }

  /**
   * The constraint reads only the bounds of its variables.
   *
   * @return the BOUND event.
   */
  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.BOUND;
  }

  /**
   * Prunes the domains of a rectangle based on its potential overlaps with other rectangles.
   *
   * @param r the rectangle to prune
   * @param rects the set of potentially overlapping rectangles
   */
  void prune(Rectangle r, BitSet rects) {

    for (int i = rects.nextSetBit(0); i >= 0; i = rects.nextSetBit(i + 1)) {
      for (int dim = 0; dim < 2; dim++) {
        int oDim = dim == 0 ? 1 : 0;
        syncBounds();
        bounds(r.index);
        bounds(i);
        if (overlap(r.index, i, dim)) {
          prune(r, rectangle[i], oDim);
        }
      }
    }
  }

  /**
   * Prunes two rectangles in a specific dimension based on their overlap. If rectangles overlap in
   * one dimension, they must not overlap in the other.
   *
   * @param ri the first rectangle
   * @param rj the second rectangle
   * @param dim the dimension (0 for x, 1 for y) in which to perform pruning
   */
  private void prune(Rectangle ri, Rectangle rj, int dim) {

    int lstI = ri.lst(dim);
    int ectI = ri.ect(dim);
    int lstJ = rj.lst(dim);
    int ectJ = rj.ect(dim);

    if (lstI < ectI || lstJ < ectJ) {
      IntVar riOrigin = ri.getOrigin(dim);
      IntVar rjOrigin = rj.getOrigin(dim);

      if (lstI < ectJ) { // i before j
        IntVar riLength = ri.getLength(dim);

        if (strict || (ri.exists() && rj.exists())) {
          rjOrigin.domain.inMin(store.level, rjOrigin, ectI);
          riOrigin.domain.inMax(store.level, riOrigin, lstJ - riLength.min());
          riLength.domain.inMax(store.level, riLength, lstJ - ri.est(dim));
        }
      } else if (lstJ < ectI) { // j before i
        IntVar rjLength = rj.getLength(dim);

        if (strict || (ri.exists() && rj.exists())) {
          riOrigin.domain.inMin(store.level, riOrigin, ectJ);
          rjOrigin.domain.inMax(store.level, rjOrigin, lstI - rjLength.min());
          rjLength.domain.inMax(store.level, rjLength, lstI - rj.est(dim));
        }
      }
    }
  }

  /**
   * Performs energy-based feasibility check for a rectangle and its potentially overlapping
   * rectangles. Verifies that the total minimum area of rectangles can fit within the bounding box.
   *
   * @param r the rectangle to check
   * @param rects the set of potentially overlapping rectangles
   */
  void energyCheck(int k, BitSet rects) {

    int xMin = est[X][k];
    int xMax = lst[X][k] + lMax[X][k];
    int yMin = est[Y][k];
    int yMax = lst[Y][k] + lMax[Y][k];
    long rSpace = (long) (xMax - xMin) * (yMax - yMin);
    int xLengthMin = lMin[X][k];
    int yLengthMin = lMin[Y][k];
    long minArea = (long) xLengthMin * yLengthMin;
    int count = 1;
    for (int j = rects.nextSetBit(0); j >= 0; j = rects.nextSetBit(j + 1)) {
      count++;
      xMin = Math.min(xMin, est[X][j]);
      xMax = Math.max(xMax, lst[X][j] + lMax[X][j]);
      yMin = Math.min(yMin, est[Y][j]);
      yMax = Math.max(yMax, lst[Y][j] + lMax[Y][j]);
      int rjxLength = lMin[X][j];
      int rjyLength = lMin[Y][j];
      xLengthMin = Math.min(xLengthMin, rjxLength);
      yLengthMin = Math.min(yLengthMin, rjyLength);
      minArea += (long) rjxLength * rjyLength;
      if (minArea > (long) (xMax - xMin) * (yMax - yMin)) {
        throw Store.failException;
      }
    }
    if (xLengthMin > 0 && yLengthMin > 0) {
      int maxNumberRectangles = (xMax - xMin) / xLengthMin * ((yMax - yMin) / yLengthMin);
      if (maxNumberRectangles < count) {
        throw Store.failException;
      }
    }

    doAreaCheck = rSpace < minArea;
  }

  // the flag energyCheck(r, rects) sets, for a rectangle that it would not fail
  private boolean areaExceedsSpace(Rectangle r, BitSet rects) {
    long rSpace = (long) (r.lct(X) - r.est(X)) * (r.lct(Y) - r.est(Y));
    long minArea = (long) r.getLength(X).min() * r.getLength(Y).min();
    for (int j = rects.nextSetBit(0); j >= 0; j = rects.nextSetBit(j + 1)) {
      minArea += (long) rectangle[j].getLength(X).min() * rectangle[j].getLength(Y).min();
    }
    return rSpace < minArea;
  }

  // registers the constraint in the constraint store
  @Override
  @SuppressWarnings("unchecked")
  public void impose(Store store) {

    super.impose(store);

    overlapping = new TimeStamp[rectangle.length];
    rectanglesSlot = new VarIntMap(4 * rectangle.length);
    rectanglesOf = new int[4 * rectangle.length][];
    for (int pass = 0; pass < changed.length; pass++) {
      changed[pass] = new BitSet(rectangle.length);
      changed[pass].set(0, rectangle.length);
      changedBefore[pass] = new BitSet(rectangle.length);
    }
    for (int i = 0; i < rectangle.length; i++) {
      BitSet bs = new BitSet(rectangle.length);
      bs.flip(0, rectangle.length); // set all bits to true == all rectangles overlap
      bs.set(i, false); // rectangle does not overlaps with itself
      overlapping[i] = new TimeStamp<>(store, bs);
      for (IntVar v :
          List.of(
              rectangle[i].origin[0],
              rectangle[i].origin[1],
              rectangle[i].length[0],
              rectangle[i].length[1])) {
        int slot = rectanglesSlot.get(v);
        if (slot == VarIntMap.ABSENT) {
          slot = rectanglesSlot.size();
          rectanglesSlot.put(v, slot);
        }
        int[] rs = rectanglesOf[slot];
        rs = rs == null ? new int[1] : Arrays.copyOf(rs, rs.length + 1);
        rs[rs.length - 1] = i;
        rectanglesOf[slot] = rs;
      }

      // impose constraint on rectangle length >= 0
      rectangle[i].getLength(0).domain.inMin(store.level, rectangle[i].getLength(0), 0);
      rectangle[i].getLength(1).domain.inMin(store.level, rectangle[i].getLength(1), 0);
    }
  }

  /**
   * Checks if the constraint is satisfied, i.e., no two rectangles overlap.
   *
   * @return true if constraint is satisfied, false otherwise
   */
  public boolean satisfied() {
    for (int i = 0; i < rectangle.length; i++) {
      for (int j = i + 1; j < rectangle.length; j++) {
        if (!rectangle[i].noOverlap(rectangle[j], 0)
            && !rectangle[i].noOverlap(rectangle[j], 1)
            && (strict || !(rectangle[i].isEmpty() || rectangle[j].isEmpty()))) {
          return false;
        }
      }
    }
    return true;
  }

  /**
   * Checks if the constraint cannot be satisfied, i.e., at least two rectangles must overlap.
   *
   * @return true if constraint cannot be satisfied, false otherwise
   */
  public boolean notSatisfied() {
    for (int i = 0; i < rectangle.length; i++) {
      for (int j = i + 1; j < rectangle.length; j++) {
        if (rectangle[i].doOverlap(rectangle[j])
            && (strict || rectangle[i].exists() && rectangle[j].exists())) {
          return true;
        }
      }
    }
    return false;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : nooverlap([");

    int i = 0;
    for (Rectangle r : rectangle) {
      result.append(r);
      if (i < rectangle.length - 1) {
        result.append(", ");
      }
      i++;
    }
    return result.append("], ").append(strict).append(")").toString();
  }

  /**
   * Returns the counterparts of the variables of the rectangles in the order they were given.
   *
   * @param map the counterparts of the variables of this constraint.
   * @return for each rectangle its two origins and its two lengths.
   */
  IntVar[][] rectangleVariables(VarMap map) {
    IntVar[][] vars = new IntVar[rectangle.length][];
    for (int i = 0; i < rectangle.length; i++) {
      Rectangle r = rectangle[i];
      vars[i] =
          new IntVar[] {
            map.get(r.origin[0]), map.get(r.origin[1]), map.get(r.length[0]), map.get(r.length[1])
          };
    }
    return vars;
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    if (!explainable()) {
      return false;
    }
    if (!DiffnExplanation.explain(trail, entry, rectangle, out)) {
      DiffnExplanation.bounds(trail, entry, rectangle, out);
      // a rule removes values up to a bound it computed, and the domain moves past the holes
      // beyond it, which the bounds do not explain
      int kind = trail.kind(entry);
      if (kind != AtomicTrail.NE) {
        trail.addSkippedHoles(
            entry, kind == AtomicTrail.GE ? Integer.MIN_VALUE : Integer.MAX_VALUE, out);
      }
    }
    return true;
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    if (!explainable()) {
      return false;
    }
    if (!DiffnExplanation.explainFailure(trail, rectangle, out)) {
      DiffnExplanation.bounds(trail, trail.size(), rectangle, out);
    }
    return true;
  }

  /**
   * Writes each pair of rectangles as the disjunction of the four ways they are apart, i left of,
   * right of, below or above j, each a literal equal to its inequality ({@code o_i + l_i <= o_j}
   * and so on); without strict, a rectangle of length 0 in either dimension may be anywhere. Unit
   * propagation over it is the pairwise pruning, which the explanations state. Diffn, which also
   * prunes by profiles and areas, is not encoded.
   */
  @Override
  public boolean encode(PbModel model) {
    if (getClass() != Nooverlap.class) {
      return false;
    }
    for (int i = 0; i < rectangle.length; i++) {
      for (int j = i + 1; j < rectangle.length; j++) {
        List<String> apart = new ArrayList<>();
        for (int d = 0; d < 2; d++) {
          apart.add(before(model, rectangle[i], rectangle[j], d));
          apart.add(before(model, rectangle[j], rectangle[i], d));
          if (!strict) {
            apart.add(PbModel.not(model.atLeast(rectangle[i].length[d], 1)));
            apart.add(PbModel.not(model.atLeast(rectangle[j].length[d], 1)));
          }
        }
        model.clause(apart.toArray(new String[0]));
      }
    }
    return true;
  }

  /** The most clauses written for one literal "a ends before b starts" before a linear line. */
  private static final int BEFORE_CLAUSES = 1 << 14;

  // a literal equal to a ending before b starts in dimension d, o_a + l_a <= o_b, so that a
  // solution
  // fixes it; as clauses over the order literals, for each value of o_a (or o_b) and of l_a, unit
  // propagation over it gives the bounds of the pairwise pruning, which a linear line over the
  // order
  // literals derives only one value at a time
  private static String before(PbModel model, Rectangle a, Rectangle b, int d) {
    String lit = model.auxiliary();
    IntVar oa = a.origin[d];
    IntVar la = a.length[d];
    IntVar ob = b.origin[d];
    int[] originsA = values(model.domain(oa));
    int[] lengths = values(model.domain(la));
    int[] originsB = values(model.domain(ob));
    if ((long) (originsA.length + originsB.length) * lengths.length > BEFORE_CLAUSES) {
      LinearForm f =
          new LinearForm(new IntVar[] {oa, la, ob}, new long[] {1, 1, -1}, 0, LinearForm.LE);
      model.guarded(lit, f);
      model.guarded(PbModel.not(lit), f.negated());
      return lit;
    }
    String notLit = PbModel.not(lit);
    for (int k : lengths) {
      String longEnough = PbModel.not(model.atLeast(la, k));
      String shortEnough = model.atLeast(la, k + 1);
      // lit, o_a >= v and l_a >= k: o_b >= v + k
      for (int v : originsA) {
        model.clause(
            notLit, PbModel.not(model.atLeast(oa, v)), longEnough, model.atLeast(ob, v + k));
      }
      // not lit, o_b >= w and l_a <= k: o_a >= w + 1 - k
      for (int w : originsB) {
        model.clause(
            lit, PbModel.not(model.atLeast(ob, w)), shortEnough, model.atLeast(oa, w + 1 - k));
      }
    }
    return lit;
  }

  private static int[] values(IntDomain dom) {
    int[] v = new int[dom.getSize()];
    int n = 0;
    for (ValueEnumeration e = dom.valueEnumeration(); e.hasMoreElements(); ) {
      v[n++] = e.nextElement();
    }
    return v;
  }

  // a subclass may prune by other rules, so only the classes explained here give reasons
  private boolean explainable() {
    Class<?> type = getClass();
    return type == Nooverlap.class || type == Diffn.class;
  }

  @Override
  public Nooverlap copy(VarMap map) {
    Nooverlap c = new Nooverlap(rectangleVariables(map), strict);
    c.energyCheck = energyCheck;
    return c;
  }
}
