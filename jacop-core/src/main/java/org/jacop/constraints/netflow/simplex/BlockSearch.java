/*
 * Danzig.java
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
package org.jacop.constraints.netflow.simplex;

/**
 * Block search pricing: the arcs are scanned cyclically in blocks of about the square root of their
 * number, and the arc with the largest violation in the first block that holds one enters (M. D.
 * Grigoriadis, "An efficient implementation of the network simplex method", Mathematical
 * Programming Study 26, 1986). A pivot then reads a block instead of every arc.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class BlockSearch implements PivotRule {

  private final NetworkSimplex network;

  // the position where the next scan starts
  private int start;

  /**
   * It creates the rule for a network.
   *
   * @param network the network whose arcs are priced
   */
  public BlockSearch(NetworkSimplex network) {
    this.network = network;
  }

  @Override
  public Arc next() {
    int m = network.numArcs;
    if (m == 0) {
      return null;
    }
    int block = Math.max(16, (int) Math.sqrt(m));
    if (start >= m) {
      start = 0;
    }
    Arc next = null;
    long minimumCost = 0;
    int i = start;
    int inBlock = 0;
    for (int scanned = 0; scanned < m; scanned++) {
      Arc arc = network.lower[i];
      long reducedCost = arc.reducedCost();
      if (minimumCost > reducedCost) {
        minimumCost = reducedCost;
        next = arc;
      }
      if (++i == m) {
        i = 0;
      }
      if (++inBlock == block) {
        if (next != null) {
          break;
        }
        inBlock = 0;
      }
    }
    start = i;
    return next;
  }

  @Override
  public void reset() {
    start = 0;
  }
}
