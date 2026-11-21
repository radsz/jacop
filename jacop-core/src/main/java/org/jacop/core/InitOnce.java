/*
 * InitOnce.java
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

package org.jacop.core;

/**
 * One-time work that a constraint does in a consistency call, usually the first one, such as
 * pruning the domains to the values its data allows. The store remembers the level at which the
 * work was done and, when that level is removed, makes the work due again, so it is redone at the
 * next call instead of being lost with the level.
 *
 * <p>A constraint keeps one instance per piece of one-time work and calls {@link #begin(Store)} at
 * the point where it would test its first-consistency flag. It needs no {@code removeLevel} code
 * for it.
 *
 * <p>The work must start from the constraint's own data as given at construction or imposition, not
 * from what an earlier run of the work computed, since that run may be undone.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class InitOnce {

  private static final int DUE = -1;

  private int level = DUE;

  /**
   * Checks whether the work is due and, if it is, records it as done at the store's current level.
   * The caller does the work right after a {@code true} result.
   *
   * @param store the store whose level the work belongs to.
   * @return true if the work is due and has to be done now.
   */
  public boolean begin(Store store) {
    if (level != DUE) {
      return false;
    }
    level = store.level;
    store.recordInitOnce(this);
    return true;
  }

  /**
   * Checks whether the work is due, without recording anything.
   *
   * @return true if the work has not been done or the level at which it was done was removed.
   */
  public boolean due() {
    return level == DUE;
  }

  /**
   * Returns the store level at which the work was done.
   *
   * @return the level, or -1 if the work is due.
   */
  public int level() {
    return level;
  }

  void rearm() {
    level = DUE;
  }

  @Override
  public String toString() {
    return level == DUE ? "InitOnce(due)" : "InitOnce(done at " + level + ")";
  }
}
