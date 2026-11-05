/*
 * LexChain.java
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

package org.jacop.constraints.geost;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Var;

/**
 * External constraint for geost ordering the origins of a sequence of objects lexicographically:
 * origin(o_1) &lt;=lex origin(o_2) &lt;=lex ... &lt;=lex origin(o_n), comparing coordinate 0 first.
 * The time dimension is not compared.
 *
 * <p>It breaks the symmetry between interchangeable objects (the same possible shapes, the same
 * domains, the same constraints), like SICStus's geost option lex. It is imposed inside the sweep:
 * the origins lexicographically smaller than the smallest point of the predecessor's domain, or
 * larger than the largest point of the successor's domain, are a forbidden region of an object. The
 * sweep then also removes values the bounds of a separate lex constraint keep, for example the
 * smallest x of an object when no place at that x is both free and lexicographically large enough.
 *
 * <p>Ordering objects that are not interchangeable removes solutions; that is the caller's choice.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class LexChain implements ExternalConstraint {

  /** The objects in the order of their origins. */
  final GeostObject[] objects;

  /** The internal constraint of each object of the chain, by object id. */
  Bound[] boundOf;

  List<InternalConstraint> constraints;

  /**
   * It creates a lexicographic chain over the origins of the given objects.
   *
   * @param objects the objects, in lexicographically nondecreasing order of their origins.
   */
  public LexChain(GeostObject[] objects) {
    if (objects.length < 2) {
      throw new IllegalArgumentException("LexChain needs at least two objects");
    }
    if (Arrays.stream(objects).distinct().count() != objects.length) {
      throw new IllegalArgumentException("LexChain lists an object twice");
    }
    this.objects = objects.clone();
  }

  @Override
  public Collection<InternalConstraint> genInternalConstraints(Geost geost) {
    if (constraints == null) {
      int largestId = 0;
      for (GeostObject o : objects) {
        largestId = Math.max(largestId, o.no);
      }
      boundOf = new Bound[largestId + 1];
      constraints = new ArrayList<>(objects.length);
      for (int i = 0; i < objects.length; i++) {
        Bound b =
            new Bound(
                objects[i],
                i > 0 ? objects[i - 1] : null,
                i < objects.length - 1 ? objects[i + 1] : null);
        boundOf[objects[i].no] = b;
        constraints.add(b);
      }
    }
    return constraints;
  }

  @Override
  public Collection<InternalConstraint> getObjectConstraints(GeostObject o) {
    if (o.no < boundOf.length && boundOf[o.no] != null && boundOf[o.no].object == o) {
      return List.of(boundOf[o.no]);
    }
    return List.of();
  }

  @Override
  public boolean addPrunableObjects(GeostObject o, Set<GeostObject> accumulator) {
    if (o.no >= boundOf.length || boundOf[o.no] == null || boundOf[o.no].object != o) {
      return false;
    }
    Bound b = boundOf[o.no];
    boolean changed = false;
    if (b.predecessor != null) {
      changed = accumulator.add(b.predecessor);
    }
    if (b.successor != null) {
      changed |= accumulator.add(b.successor);
    }
    return changed;
  }

  @Override
  public void onObjectUpdate(GeostObject o) {
    // the bounds read the domains of the neighbours when they are used
  }

  @Override
  public boolean isInternalConstraintApplicableTo(InternalConstraint ic, GeostObject o) {
    return ic instanceof Bound b && b.object == o && constraints.contains(ic);
  }

  @Override
  public GeostObject[] getObjectScope() {
    return objects;
  }

  @Override
  public String toString() {
    return "(lex_chain: " + Arrays.asList(objects) + ")";
  }

  /**
   * The forbidden region of one object of the chain: the origins lexicographically smaller than the
   * smallest point of its predecessor's domain or larger than the largest point of its successor's
   * domain. Other objects are not constrained by it.
   */
  static final class Bound extends InternalConstraint {

    final GeostObject object;

    final GeostObject predecessor;

    final GeostObject successor;

    /** The extreme points returned by absInfeasible: the region is not bounded. */
    private final int[] lowest;

    private final int[] highest;

    Bound(GeostObject object, GeostObject predecessor, GeostObject successor) {
      this.object = object;
      this.predecessor = predecessor;
      this.successor = successor;
      lowest = new int[object.dimension + 1];
      Arrays.fill(lowest, Integer.MIN_VALUE);
      highest = new int[object.dimension + 1];
      Arrays.fill(highest, Integer.MAX_VALUE);
    }

    @Override
    public Dbox isFeasible(
        Geost.SweepDirection min,
        LexicographicalOrder order,
        GeostObject o,
        int currentShape,
        int[] c) {
      if (o != object) {
        return null;
      }
      if (predecessor != null) {
        Dbox f = below(predecessor.coords, c);
        if (f != null) {
          return f;
        }
      }
      return successor != null ? above(successor.coords, c) : null;
    }

    /** The box of origins lexicographically smaller than the mins of bound that contains c. */
    private Dbox below(IntVar[] bound, int[] c) {
      for (int j = 0; j < bound.length; j++) {
        int l = bound[j].min();
        if (c[j] > l) {
          return null;
        }
        if (c[j] < l) {
          return box(c, j, IntDomain.MIN_INT, l);
        }
      }
      return null;
    }

    /** The box of origins lexicographically larger than the maxes of bound that contains c. */
    private Dbox above(IntVar[] bound, int[] c) {
      for (int j = 0; j < bound.length; j++) {
        int u = bound[j].max();
        if (c[j] < u) {
          return null;
        }
        if (c[j] > u) {
          return box(c, j, u + 1, IntDomain.MAX_INT + 1);
        }
      }
      return null;
    }

    /**
     * The box made of c in the dimensions before j, [from, to) in dimension j, and everything in
     * the later dimensions and in time.
     */
    private static Dbox box(int[] c, int j, int from, int to) {
      Dbox outBox = Dbox.getAllocatedInstance(c.length);
      for (int i = 0; i < c.length; i++) {
        if (i < j) {
          outBox.origin[i] = c[i];
          outBox.length[i] = 1;
        } else if (i == j) {
          outBox.origin[i] = from;
          outBox.length[i] = to - from;
        } else {
          outBox.origin[i] = IntDomain.MIN_INT;
          outBox.length[i] = IntDomain.MAX_INT + 1 - IntDomain.MIN_INT;
        }
      }
      return outBox;
    }

    @Override
    public int[] absInfeasible(Geost.SweepDirection minlex) {
      // the region is not bounded, so the constraint is never filtered out
      return minlex == Geost.SweepDirection.PRUNEMIN ? lowest : highest;
    }

    @Override
    public boolean isStatic() {
      return false;
    }

    @Override
    public boolean isSingleUse() {
      return false;
    }

    @Override
    public int cardInfeasible() {
      return 1;
    }

    @Override
    public Collection<Var> definingVariables() {
      List<Var> vars = new ArrayList<>();
      if (predecessor != null) {
        vars.addAll(Arrays.asList(predecessor.coords));
      }
      if (successor != null) {
        vars.addAll(Arrays.asList(successor.coords));
      }
      return vars;
    }

    @Override
    public String toString() {
      return "lex_bound(" + object.no + ")";
    }
  }
}
