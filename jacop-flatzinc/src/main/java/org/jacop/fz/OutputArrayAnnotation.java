/*
 * OutputArrayAnnotation.java
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

package org.jacop.fz;

import java.util.ArrayList;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntDomain;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.set.core.SetVar;

/**
 * It stores information about the annotation for an output array.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class OutputArrayAnnotation {

  final String id;

  final ArrayList<IntDomain> indexes;
  Var[] array;

  /**
   * It constructs and output array annotation.
   *
   * @param name the name of the output array annotation.
   * @param indexBounds the indexes bounds.
   */
  public OutputArrayAnnotation(String name, ArrayList<IntDomain> indexBounds) {
    id = name;
    indexes = indexBounds;
  }

  /**
   * Returns the name of the output array annotation.
   *
   * @return the name
   */
  String getName() {
    return id;
  }

  /**
   * Returns the variable array.
   *
   * @return the variable array
   */
  Var[] getArray() {
    return array;
  }

  /**
   * Sets the variable array.
   *
   * @param a the variable array to set
   */
  void setArray(Var[] a) {
    array = a;
  }

  /**
   * Returns the number of index dimensions.
   *
   * @return the number of indexes
   */
  int getNumberIndexes() {
    return indexes.size();
  }

  /**
   * Returns the index domain at the specified position.
   *
   * @param i the index position
   * @return the index domain
   */
  IntDomain getIndexes(int i) {
    return indexes.get(i);
  }

  /**
   * Checks if the array contains the specified variable.
   *
   * @param x the variable to check
   * @return true if the variable is in the array, false otherwise
   */
  boolean contains(Var x) {

    for (Var v : array) {
      if (x.equals(v)) {
        return true;
      }
    }
    return false;
  }

  /** {@inheritDoc} */
  @Override
  public String toString() {

    StringBuilder s = new StringBuilder(id + " = array" + indexes.size() + "d(");
    appendIndexes(s);
    s.append("[");
    for (int i = 0; i < array.length; i++) {
      appendVarToString(s, array[i]);
      if (i < array.length - 1) {
        s.append(", ");
      }
    }
    s.append("]);");
    return s.toString();
  }

  private void appendIndexes(StringBuilder s) {
    for (IntDomain index : indexes) {
      if (index.getSize() == 0) {
        s.append("{}, ");
      } else {
        s.append(index.min()).append("..").append(index.max()).append(", ");
      }
    }
  }

  private void appendVarToString(StringBuilder s, Var v) {
    if (v instanceof BooleanVar var1) {
      appendBooleanVarToString(s, var1);
    } else if (v instanceof SetVar setVar) {
      appendSetVarToString(s, setVar);
    } else {
      s.append(v.dom().toString());
    }
  }

  private void appendBooleanVarToString(StringBuilder s, BooleanVar var1) {
    if (var1.singleton()) {
      switch (var1.value()) {
        case 0:
          s.append("false");
          break;
        case 1:
          s.append("true");
          break;
        default:
          s.append(String.valueOf(var1.dom()));
      }
    } else {
      s.append("false..true");
    }
  }

  private void appendSetVarToString(StringBuilder s, SetVar setVar) {
    if (setVar.singleton()) {
      IntDomain glb = setVar.dom().glb();
      if (glb.getSize() > 0 && glb.getSize() == glb.max() - glb.min() + 1) {
        s.append(glb.min()).append("..").append(glb.max());
      } else {
        s.append("{");
        for (ValueEnumeration e = glb.valueEnumeration(); e.hasMoreElements(); ) {
          int element = e.nextElement();
          s.append(element);
          if (e.hasMoreElements()) {
            s.append(", ");
          }
        }
        s.append("}");
      }
    } else {
      s.append(setVar.dom().toString());
    }
  }
}
