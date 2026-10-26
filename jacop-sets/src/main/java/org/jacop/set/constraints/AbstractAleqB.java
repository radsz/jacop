/*
 * AbstractAleqB.java
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

package org.jacop.set.constraints;

import java.util.Arrays;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * Abstract base class for set lexicographic ordering constraints (AleB and AltB). Provides shared
 * fields, pruning event defaults, and negation delegation.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public abstract class AbstractAleqB extends PrimitiveConstraint {

  /** It specifies the first variable of the constraint. */
  protected final SetVar a;

  /** It specifies the second variable of the constraint. */
  protected final SetVar b;

  /** Negated constraint used for notConsistency and notSatisfied delegation. */
  PrimitiveConstraint negatedConstraint;

  /**
   * Constructs a lex ordering constraint with full initialization.
   *
   * @param idNum the atomic id counter for the constraint type
   * @param a the left-hand set variable
   * @param b the right-hand set variable
   */
  protected AbstractAleqB(AtomicInteger idNum, SetVar a, SetVar b) {
    checkInputForNullness(new String[] {"a", "b"}, new Object[] {a, b});
    numberId = idNum.incrementAndGet();
    this.a = a;
    this.b = b;
    setScope(a, b);
  }

  /**
   * Constructs a lex ordering constraint for use as a negated helper only. Does not set scope or
   * numberId.
   *
   * @param a the left-hand set variable
   * @param b the right-hand set variable
   */
  protected AbstractAleqB(SetVar a, SetVar b) {
    this.a = a;
    this.b = b;
  }

  /**
   * Performs the lexicographic comparison on two ground set domains.
   *
   * @param x the first domain
   * @param y the second domain
   * @return true if x is lexicographically ordered with respect to y
   */
  abstract boolean setLexCompare(IntDomain x, IntDomain y);

  @Override
  public void notConsistency(Store store) {
    negatedConstraint.consistency(store);
  }

  @Override
  public boolean satisfied() {
    // every value of a is at most the largest one, and every value of b at least the smallest one
    return setLexCompare(largest(a), smallest(b));
  }

  @Override
  public boolean notSatisfied() {
    return ((AbstractAleqB) negatedConstraint).satisfied();
  }

  @Override
  protected int getDefaultNestedConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  protected int getDefaultNestedNotConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  protected int getDefaultNotConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return SetDomain.ANY;
  }

  /** Reading both sets element by element in increasing order: no difference yet. */
  private static final int EQUAL = 0;

  /** The first difference is an element of a only: a is smaller iff b has a later element. */
  private static final int A_FIRST = 1;

  /** The first difference is an element of b only: a is smaller iff a has no later element. */
  private static final int B_FIRST = 2;

  /** a is smaller whatever comes next. */
  private static final int LESS = 3;

  /**
   * The automaton state after reading an element that is (x = 1) or is not (x = 0) in a, and is (y
   * = 1) or is not (y = 0) in b; -1 when a is then larger than b.
   */
  private static int next(int q, int x, int y) {
    switch (q) {
      case EQUAL:
        if (x == y) {
          return EQUAL;
        }
        return x == 1 ? A_FIRST : B_FIRST;
      case A_FIRST:
        return y == 1 ? LESS : A_FIRST;
      case B_FIRST:
        return x == 1 ? -1 : B_FIRST;
      default:
        return LESS;
    }
  }

  /**
   * The transitions of the automaton on an element that a can take with the values in bits canA and
   * b with those in canB (bit 0 = absent, bit 1 = present), for canA and canB from 1 to 3: q | x <<
   * 2 | y << 3 | next state << 4.
   */
  private static final int[][][] TRANSITIONS = new int[4][4][];

  static {
    for (int canA = 1; canA < 4; canA++) {
      for (int canB = 1; canB < 4; canB++) {
        int[] t = new int[16];
        int k = 0;
        for (int q = 0; q < 4; q++) {
          for (int x = 0; x < 2; x++) {
            for (int y = 0; y < 2; y++) {
              int r = next(q, x, y);
              if ((canA >> x & 1) != 0 && (canB >> y & 1) != 0 && r >= 0) {
                t[k++] = q | x << 2 | y << 3 | r << 4;
              }
            }
          }
        }
        TRANSITIONS[canA][canB] = Arrays.copyOf(t, k);
      }
    }
  }

  /**
   * Removes an element from the lub of s or adds it to the glb when only one value is supported.
   */
  private static void decide(Store store, SetVar s, int element, int supported, int possible) {
    if (supported == possible) {
      return;
    }
    if (supported == 1) {
      s.domain.inLubComplement(store.level, s, element);
    } else {
      s.domain.inGlb(store.level, s, element);
    }
  }

  /**
   * The counts after reading an element: shifts the bits of mask (bit ka * nb + kb for ka elements
   * counted in a and kb in b) by dx counted elements of a and dy of b. A count that would go above
   * its maximum is dropped.
   */
  private static long shift(long mask, int dx, int dy, int nb, long belowMaxB, long full) {
    if (dy == 1) {
      mask = (mask & belowMaxB) << 1;
    }
    if (dx == 1) {
      mask = (mask << nb) & full;
    }
    return mask;
  }

  /** The counts before reading an element: the inverse of shift. */
  private static long unshift(long mask, int dx, int dy, int nb, long belowMaxB) {
    if (dx == 1) {
      mask >>>= nb;
    }
    if (dy == 1) {
      mask = (mask >>> 1) & belowMaxB;
    }
    return mask;
  }

  /**
   * Enforces the order on the bounds of a and b: every element of lub(a) or lub(b) that is not yet
   * decided stays undecided only when the constraint has a solution with it in the set and one
   * without it, and the cardinalities are narrowed to those of the solutions. The order is the
   * lexicographic order of the sorted lists of elements (MiniZinc's set_le and set_lt), read as an
   * automaton over the elements of lub(a) and lub(b) in increasing order. The automaton also counts
   * the undecided elements put in a set when its cardinality restricts it, with the pairs of counts
   * of a state as the bits of a long; when the pairs do not fit, only one set is counted, or none.
   *
   * @param store the constraint store.
   * @param strict true for a {@literal <} b, false for a {@literal <=} b.
   */
  protected void propagateOrder(Store store, boolean strict) {

    boolean again;
    do {
      SetDomain da = a.domain;
      SetDomain db = b.domain;
      IntDomain aGlb = da.glb();
      IntDomain aLub = da.lub();
      IntDomain bGlb = db.glb();
      IntDomain bLub = db.lub();

      IntDomain all = aLub.union(bLub);
      int n = all.getSize();
      int[] element = new int[n];
      // values each set can take on an element: bit 0 = absent, bit 1 = present
      int[] canA = new int[n];
      int[] canB = new int[n];
      ValueEnumeration e = all.valueEnumeration();
      for (int i = 0; i < n; i++) {
        int v = e.nextElement();
        element[i] = v;
        canA[i] = aGlb.contains(v) ? 2 : (aLub.contains(v) ? 3 : 1);
        canB[i] = bGlb.contains(v) ? 2 : (bLub.contains(v) ? 3 : 1);
      }
      // the automaton stays in EQUAL over the leading elements that are decided the same way in a
      // and b
      int first = 0;
      while (first < n && canA[first] == canB[first] && canA[first] != 3) {
        first++;
      }

      // the counts are of the undecided elements put in the set: from 0 to cardMax - |glb|
      int aGlbSize = aGlb.getSize();
      int bGlbSize = bGlb.getSize();
      int aMinAdded = da.card().min() - aGlbSize;
      int aMaxAdded = Math.min(da.card().max(), aLub.getSize()) - aGlbSize;
      int bMinAdded = db.card().min() - bGlbSize;
      int bMaxAdded = Math.min(db.card().max(), bLub.getSize()) - bGlbSize;
      boolean countA =
          (aMinAdded > 0 || aMaxAdded < aLub.getSize() - aGlbSize) && aMaxAdded < Long.SIZE;
      boolean countB =
          (bMinAdded > 0 || bMaxAdded < bLub.getSize() - bGlbSize) && bMaxAdded < Long.SIZE;
      if (countA && countB && (aMaxAdded + 1) * (bMaxAdded + 1) > Long.SIZE) {
        if (aMaxAdded <= bMaxAdded) {
          countB = false;
        } else {
          countA = false;
        }
      }
      int na = countA ? aMaxAdded + 1 : 1;
      int nb = countB ? bMaxAdded + 1 : 1;
      long full = na * nb == Long.SIZE ? -1L : (1L << (na * nb)) - 1;
      long belowMaxB = 0;
      long accepted = 0;
      for (int ka = 0; ka < na; ka++) {
        for (int kb = 0; kb < nb; kb++) {
          if (kb < nb - 1) {
            belowMaxB |= 1L << (ka * nb + kb);
          }
          if ((!countA || ka >= aMinAdded) && (!countB || kb >= bMinAdded)) {
            accepted |= 1L << (ka * nb + kb);
          }
        }
      }

      // forward[(i - first) * 4 + q]: the counts reachable in state q before element i
      int layers = n - first + 1;
      long[] forward = new long[layers * 4];
      forward[EQUAL] = 1L;
      for (int i = first; i < n; i++) {
        int from = (i - first) * 4;
        // an undecided element put in the set is counted
        int addA = countA && canA[i] == 3 ? 1 : 0;
        int addB = countB && canB[i] == 3 ? 1 : 0;
        for (int t : TRANSITIONS[canA[i]][canB[i]]) {
          long m = forward[from + (t & 3)];
          if (m != 0) {
            int dx = (t >> 2 & 1) * addA;
            int dy = (t >> 3 & 1) * addB;
            forward[from + 4 + (t >> 4)] |= shift(m, dx, dy, nb, belowMaxB, full);
          }
        }
      }

      // backward[(i - first) * 4 + q]: the reachable counts in state q before element i from which
      // a solution can be completed
      long[] backward = new long[layers * 4];
      int last = (layers - 1) * 4;
      backward[last + LESS] = accepted;
      backward[last + B_FIRST] = accepted;
      if (!strict) {
        backward[last + EQUAL] = accepted;
      }
      // supported values: bit 0 = absent, bit 1 = present
      int[] supA = new int[n];
      int[] supB = new int[n];
      for (int i = n - 1; i >= first; i--) {
        int from = (i - first) * 4;
        int addA = countA && canA[i] == 3 ? 1 : 0;
        int addB = countB && canB[i] == 3 ? 1 : 0;
        for (int t : TRANSITIONS[canA[i]][canB[i]]) {
          int x = t >> 2 & 1;
          int y = t >> 3 & 1;
          long support =
              forward[from + (t & 3)]
                  & unshift(backward[from + 4 + (t >> 4)], x * addA, y * addB, nb, belowMaxB);
          if (support != 0) {
            backward[from + (t & 3)] |= support;
            supA[i] |= 1 << x;
            supB[i] |= 1 << y;
          }
        }
      }

      if ((backward[EQUAL] & 1L) == 0) {
        throw Store.failException;
      }

      for (int i = first; i < n; i++) {
        decide(store, a, element[i], supA[i], canA[i]);
        decide(store, b, element[i], supB[i], canB[i]);
      }

      if (countA || countB) {
        long counts = 0;
        for (int q = 0; q < 4; q++) {
          counts |= forward[last + q] & backward[last + q];
        }
        int aMin = IntDomain.MAX_INT;
        int aMax = -1;
        int bMin = IntDomain.MAX_INT;
        int bMax = -1;
        for (long c = counts; c != 0; c &= c - 1) {
          int bit = Long.numberOfTrailingZeros(c);
          aMin = Math.min(aMin, bit / nb);
          aMax = Math.max(aMax, bit / nb);
          bMin = Math.min(bMin, bit % nb);
          bMax = Math.max(bMax, bit % nb);
        }
        if (countA) {
          a.domain.inCardinality(store.level, a, aGlbSize + aMin, aGlbSize + aMax);
        }
        if (countB) {
          b.domain.inCardinality(store.level, b, bGlbSize + bMin, bGlbSize + bMax);
        }
      }

      // all the remaining values have a support when both cardinalities were counted; otherwise the
      // pruning may make a cardinality restrictive, so run again (the store does not re-queue a
      // constraint for its own changes)
      again =
          (!countA || !countB)
              && (a.domain.glb().getSize() != aGlbSize
                  || a.domain.lub().getSize() != aLub.getSize()
                  || b.domain.glb().getSize() != bGlbSize
                  || b.domain.lub().getSize() != bLub.getSize());
    } while (again);
  }

  /**
   * Returns the lexicographically smallest set between the glb and the lub of s: the glb with every
   * element of the lub below its largest element, since a smaller element first makes a set
   * smaller.
   */
  static IntDomain smallest(SetVar s) {
    IntDomain glb = s.domain.glb();
    IntDomain lub = s.domain.lub();
    if (glb.isEmpty()) {
      if (s.domain.card().min() > 0 && !lub.isEmpty()) {
        return new IntervalDomain(lub.min(), lub.min());
      }
      return new IntervalDomain();
    }
    return lub.intersect(IntDomain.MIN_INT, glb.max());
  }

  /**
   * Returns the lexicographically largest set between the glb and the lub of s: the glb followed by
   * the largest element of the lub when it is larger than the glb, since any other element would
   * come before a larger one of the glb.
   */
  static IntDomain largest(SetVar s) {
    IntDomain glb = s.domain.glb();
    IntDomain lub = s.domain.lub();
    if (lub.isEmpty() || s.domain.card().max() == 0) {
      return new IntervalDomain();
    }
    IntDomain result = glb.cloneLight();
    if (glb.isEmpty() || lub.max() > glb.max()) {
      result.unionAdapt(lub.max(), lub.max());
    }
    return result;
  }
}
