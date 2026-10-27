/*
 * OrderLiterals.java
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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.ChannelOrder;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XgtC;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XltC;
import org.jacop.constraints.XlteqC;
import org.jacop.core.IntVar;
import org.jacop.lcg.LinearExplainable;
import org.jacop.lcg.LinearForm;

/**
 * Rule 5 for order reifications: the reified comparisons of one integer variable with constants,
 * {@code b <=> x <= c} and its {@code <}, {@code >=} and {@code >} forms, become the items of one
 * {@link ChannelOrder} on x, as Chuffed and Huub turn them into literals of x.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
final class OrderLiterals implements Rule {

  // the smallest number of reifications of one variable that become a channel
  static final int MIN_GROUP = 2;

  /**
   * The rule, which {@link Presolver#STANDARD} applies unless jacop.presolve.orderLiterals is
   * false.
   */
  static final OrderLiterals RULE = new OrderLiterals();

  private OrderLiterals() {}

  @Override
  public void apply(Rule.Context context) {
    for (Group g : groups(context.constraints())) {
      context.impose(g.channel());
      g.reifications().forEach(context::remove);
    }
  }

  private record Item(Reified r, IntVar x, IntVar b, int t, boolean atMost) {}

  /**
   * A channel and the reifications it replaces; the channel is over the same variables and is not
   * imposed. The rule imposes the channel in the parent and leaves the reifications out of the
   * child, so it does not find the group again in the next round.
   *
   * @param channel the channel.
   * @param reifications the reifications, in the order of the constraints.
   */
  record Group(ChannelOrder channel, List<Reified> reifications) {}

  /**
   * Finds the groups of order reifications of one variable with at least {@link #MIN_GROUP}
   * members.
   *
   * @param constraints the constraints to look at.
   * @return the groups, in the order of their first reification.
   */
  static List<Group> groups(List<Constraint> constraints) {
    // variables do not override equals, so this groups by identity in the order of the constraints
    Map<IntVar, List<Item>> byVariable = new LinkedHashMap<>();
    for (Constraint c : constraints) {
      Item item = item(c);
      if (item != null) {
        byVariable.computeIfAbsent(item.x(), k -> new ArrayList<>()).add(item);
      }
    }
    List<Group> groups = new ArrayList<>();
    for (Map.Entry<IntVar, List<Item>> e : byVariable.entrySet()) {
      List<Item> items = e.getValue();
      if (items.size() < MIN_GROUP) {
        continue;
      }
      int n = items.size();
      IntVar[] bs = new IntVar[n];
      int[] ts = new int[n];
      boolean[] atMost = new boolean[n];
      List<Reified> reifications = new ArrayList<>(n);
      for (int i = 0; i < n; i++) {
        Item item = items.get(i);
        bs[i] = item.b();
        ts[i] = item.t();
        atMost[i] = item.atMost();
        reifications.add(item.r());
      }
      groups.add(new Group(new ChannelOrder(e.getKey(), bs, ts, atMost), reifications));
    }
    return groups;
  }

  /** The item of {@code b <=> x op c}, or null if the constraint is not such a reification. */
  private static Item item(Constraint c) {
    if (c.getClass() != Reified.class) {
      return null;
    }
    Reified r = (Reified) c;
    Class<?> k = r.c.getClass();
    if (k != XlteqC.class && k != XltC.class && k != XgteqC.class && k != XgtC.class) {
      return null;
    }
    LinearForm f = ((LinearExplainable) r.c).linearForm();
    IntVar x = f.vars()[0];
    IntVar b = r.b;
    if (f.weights()[0] != 1 || x == b || x.singleton() || b.singleton()) {
      return null;
    }
    // x <= c, or x >= c, that is not (x <= c - 1)
    long t = f.relation() == LinearForm.LE ? f.c() : f.c() - 1;
    if (t < Integer.MIN_VALUE || t > Integer.MAX_VALUE) {
      return null;
    }
    return new Item(r, x, b, (int) t, f.relation() == LinearForm.LE);
  }
}
