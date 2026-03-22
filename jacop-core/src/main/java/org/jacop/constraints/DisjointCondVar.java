/*
 * DisjointCondVar.java
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

package org.jacop.constraints;

import java.util.List;
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.MutableVar;
import org.jacop.core.MutableVarValue;
import org.jacop.core.Store;

/**
 * Defines a Variable for Diff2 constraints and related operations on it. It keeps current
 * recatngles for evaluation ([[R2, R3], [R1, R3], ...]
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
class DisjointCondVar implements MutableVar {

  final int index;

  final Store store;

  DisjointCondVarValue value;

  DisjointCondVar(Store store) {
    value = new DisjointCondVarValue();
    index = store.putMutableVar(this);
    this.store = store;
  }

  DisjointCondVar(Store store, RectangleWithCondition[] rectangles) {
    value = new DisjointCondVarValue(rectangles);
    index = store.putMutableVar(this);
    this.store = store;
  }

  DisjointCondVar(Store store, List<RectangleWithCondition> rectangles) {
    value = new DisjointCondVarValue();
    value.setValue(rectangles);
    index = store.putMutableVar(this);
    this.store = store;
  }

  int index() {
    return index;
  }

  public MutableVarValue previous() {
    return value.previousDisjointCondVarValue;
  }

  public void removeLevel(int removeLevel) {
    if (value.stamp == removeLevel) {
      value = value.previousDisjointCondVarValue;
    }
  }

  public void setCurrent(MutableVarValue o) {
    value = (DisjointCondVarValue) o;
  }

  int stamp() {
    return value.stamp;
  }

  @Override
  public String toString() {
    String result = "DisjointCondVar[" + index + "] = [";
    DisjointCondVarValue val = value;
    result = result + val + "]";
    return result;
  }

  public void update(MutableVarValue val) {
    if (value.stamp == store.level) {
      value.setValue(((DisjointCondVarValue) val).rects);
    } else if (value.stamp < store.level) {
      val.setStamp(store.level);
      val.setPrevious(value);
      value = (DisjointCondVarValue) val;
    }
  }

  public MutableVarValue value() {
    return value;
  }
}
