/*
 * PartitionSet.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.constraints.Constraint;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * Channel constraint requires that array of int variables x and array of set variables y are
 * related such that (x[i] = j) {@literal <->} (i in s[j]). Indexes start form 0, both for integer
 * and set variables, by default. To define other starting index use offset definitions.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.10
 */
public class PartitionSet extends Constraint {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  final SetVar[] s;
  final int n;
  final IntDomain u;

  AunionBeqC[] union;
  List<Constraint> constraints;

  boolean firstConsistencyCheck = true;

  LinkedHashSet<Integer> variableQueue = new LinkedHashSet<>();
  final HashMap<SetVar, Integer> varMap = new HashMap<>();

  Store store;

  /**
   * It constructs a Channel constraint.
   *
   * @param s array of set variables.
   * @param universe set of all values.
   */
  public PartitionSet(SetVar[] s, IntDomain universe) {

    checkInputForNullness(new String[] {"s"}, new Object[] {s});

    numberId = idNumber.incrementAndGet();

    this.s = s;
    n = s.length;
    this.u = universe;

    for (int i = 0; i < n; i++) {
      varMap.put(s[i], i);
    }
    queueIndex = 2;

    setScope(Arrays.stream(s));
  }

  @Override
  public void consistency(Store store) throws FailException {

    if (firstConsistencyCheck) {

      for (int i = 0; i < n; i++) {
        s[i].domain.inLUB(store.level, s[i], u);
      }

      firstConsistencyCheck = false;
    }

    // check union constraint
    for (int i = 0; i < n; i++) {
      IntDomain ub = u.cloneLight();
      IntDomain lb = u.cloneLight();
      int cardMin = u.getSize();
      int cardMax = u.getSize();

      for (int j = 0; j < n; j++) {
        if (i != j) {
          ub = ub.subtract(s[j].dom().lub());
          lb = lb.subtract(s[j].dom().glb());

          cardMin -= s[j].dom().card().max();
          cardMax -= s[j].dom().card().min();
        }
      }

      s[i].dom().inLUB(store.level, s[i], lb);
      s[i].dom().inGLB(store.level, s[i], ub);

      if (cardMax < cardMin || cardMax < 0) {
        throw store.failException;
      }
      if (s[i].dom().card().max() < cardMin || s[i].dom().card().min() > cardMax) {
        throw store.failException;
      }
      if (cardMin > s[i].dom().card().min()) {
        s[i].domain.inCardinality(store.level, s[i], cardMin, Integer.MAX_VALUE);
      }
      if (cardMax < s[i].dom().card().max()) {
        s[i].dom().inCardinality(store.level, s[i], s[i].dom().card().min(), cardMax);
      }

      if (!s[i].singleton()) {
        if (s[i].dom().glb().getSize() == s[i].dom().card().max()) {
          IO.println("% 1" + s[i] + " in " + s[i].dom().glb());

          s[i].domain.inLUB(store.level, s[i], s[i].dom().glb());
        } else if (s[i].dom().lub().getSize() == s[i].dom().card().min()) {
          IO.println("% 2");

          s[i].domain.inGLB(store.level, s[i], s[i].dom().lub());
        }
      }
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return SetDomain.ANY;
  }

  AunionBeqC[] unionConstraints() {

    IntDomain empty = new IntervalDomain();
    SetVar tmp1 = new SetVar(s[0].getStore(), new BoundSetDomain(empty, u));
    Store store = s[0].getStore();
    union = new AunionBeqC[s.length - 1];
    int index = 0;
    for (int i = 1; i < s.length; i++) {
      if (i == 1) {
        union[index++] = new AunionBeqC(s[i - 1], s[i], tmp1);
      } else if (i == s.length - 1) {
        SetVar tmp3 = new SetVar(store, new BoundSetDomain(u, u));
        union[index++] = new AunionBeqC(tmp1, s[i], tmp3);
      } else {
        SetVar tmp2 = new SetVar(store, new BoundSetDomain(empty, u));
        union[index++] = new AunionBeqC(tmp1, s[i], tmp2);
        tmp1 = tmp2;
      }
    }
    return union;
  }

  List<AdisjointB> disjointConstraints() {

    Store store = s[0].getStore();
    ArrayList<AdisjointB> intersect = new ArrayList<>();
    for (int i = 0; i < s.length; i++) {
      for (int j = i + 1; j < s.length; j++) {
        intersect.add(new AdisjointB(s[i], s[j]));
      }
    }

    return intersect;
  }

  @Override
  public List<Constraint> decompose(Store store) {

    constraints = new ArrayList<>();

    AunionBeqC[] union = unionConstraints();
    List<AdisjointB> intersect = disjointConstraints();

    constraints =
        new ArrayList<>() {
          {
            addAll(Arrays.asList(union));
            addAll(intersect);
          }
        };

    return constraints;
  }

  @Override
  public void imposeDecomposition(Store store) {

    if (constraints == null) {
      constraints = decompose(store);
    }

    for (Constraint c : constraints) {
      store.impose(c, queueIndex);
    }
  }

  @Override
  public String toString() {

    return id() + " : PartitionSet(" + Arrays.asList(s) + ", " + u + ")";
  }
}
