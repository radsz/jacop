/*
 * AtMost.java
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
import java.util.function.ToIntFunction;
import org.jacop.api.Copyable;
import org.jacop.api.VarMap;
import org.jacop.api.Violation;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.lcg.AtomicTrail;
import org.jacop.lcg.EntryList;
import org.jacop.lcg.Explainable;
import org.jacop.lcg.LinearForm;
import org.jacop.lcg.PbEncodable;
import org.jacop.lcg.PbModel;

/**
 * AtMost constraint implements the counting over number of occurrences of a given value in a list
 * of variables. The number of occurrences is specified by variable value.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class AtMost extends AbstractAtLeastMost
    implements Violation, Copyable<AtMost>, Explainable, PbEncodable {

  /**
   * It constructs a AtMost constraint.
   *
   * @param value value which is counted
   * @param list variables which equality to val is counted.
   * @param counter number of variables equal to val.
   */
  public AtMost(IntVar[] list, int counter, int value) {
    super(list, counter, value);
  }

  /**
   * It constructs a AtMost constraint.
   *
   * @param value value which is counted
   * @param list variables which equality to val is counted.
   * @param counter number of variables equal to val.
   */
  public AtMost(List<? extends IntVar> list, int counter, int value) {
    super(list, counter, value);
  }

  @Override
  public void consistency(final Store store) {

    int[] counts = computeCounts();
    int numberEq = counts[0];
    int numberMayBe = counts[1];
    int start = counts[2];

    if (numberEq > counter) {
      throw Store.failException;
    } else if (numberEq + numberMayBe <= counter) {
      if (!reified) {
        removeConstraint();
      }
    } else if (numberEq == counter) {
      for (int i = start; i < list.length; i++) {
        IntVar v = list[i];
        if (!v.singleton() && v.domain.contains(value)) {
          v.domain.inComplement(store.level, v, value, value);
        }
      }
      if (!reified) {
        removeConstraint();
      }
    }

    updateState(numberEq, start);
  }

  @Override
  public boolean explain(AtomicTrail trail, int entry, EntryList out) {
    return explains()
        && new CountExplanation(trail, list, value, null, 0, counter, entry).explain(entry, out);
  }

  @Override
  public boolean explainFailure(AtomicTrail trail, EntryList out) {
    return explains()
        && new CountExplanation(trail, list, value, null, 0, counter, trail.size())
            .explainFailure(out);
  }

  // imposed on its own: a reification explains its own atoms
  private boolean explains() {
    return getClass() == AtMost.class && !reified;
  }

  @Override
  public void notConsistency(final Store store) {
    // at least counter + 1 values
    int[] counts = computeCounts();
    int numberEq = counts[0];
    int numberMayBe = counts[1];
    int start = counts[2];

    if (numberMayBe + numberEq < counter + 1) {
      throw Store.failException;
    } else if (numberEq >= counter + 1) {
      if (!reified) {
        removeConstraint();
      }
    } else if (numberMayBe + numberEq == counter + 1) {
      for (int i = start; i < list.length; i++) {
        IntVar v = list[i];
        v.domain.inValue(store.level, v, value);
      }
      if (!reified) {
        removeConstraint();
      }
    }

    updateState(numberEq, start);
  }

  @Override
  public boolean satisfied() {

    int numberEq = 0;
    int numberMayBe = 0;
    for (IntVar v : list) {
      if (v.domain.contains(value)) {
        if (v.singleton()) {
          numberEq++;
        } else {
          numberMayBe++;
        }
      }
    }

    return numberEq + numberMayBe <= counter;
  }

  @Override
  public boolean notSatisfied() {
    int numberEq = 0;
    for (IntVar v : list) {
      if (v.singleton(value)) {
        numberEq++;
      }
    }

    return numberEq >= counter + 1;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());

    result.append(" : AtMost(").append(value).append(",[");
    appendArrayToString(result, list);
    result.append("], ").append(counter).append(" )");

    return result.toString();
  }

  @Override
  public AtMost copy(VarMap map) {
    return new AtMost(map.get(list), counter, value);
  }

  @Override
  public long violation(ToIntFunction<IntVar> value) {
    return Math.max(0, Violations.count(list, this.value, value) - counter);
  }

  @Override
  public boolean encode(PbModel model) {
    if (getClass() != AtMost.class) {
      return false;
    }
    PbModel.count(model, list, value, new IntVar[0], LinearForm.LE, counter);
    return true;
  }
}
