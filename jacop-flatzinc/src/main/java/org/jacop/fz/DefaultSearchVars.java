/*
 * DefaultSearchVars.java
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

import java.util.Arrays;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Var;
import org.jacop.floats.core.FloatVar;
import org.jacop.set.core.SetVar;

/**
 * The class gathers variables and array variables for default or complementary search. Two methods
 * are supported. One gathers all output variables and the second one all non-introduced variables
 * and arrays.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class DefaultSearchVars {

  final Tables dictionary;
  private final Comparator<Var> domainSizeComparator =
      (o1, o2) -> {
        int v1 = o1.getSize();
        int v2 = o2.getSize();
        return v1 - v2;
      };
  IntVar[] intVars = new IntVar[0];
  SetVar[] setVars = new SetVar[0];
  BooleanVar[] boolVars = new BooleanVar[0];
  FloatVar[] floatVars = new FloatVar[0];

  /**
   * It constructs the class for collecting default and complementary search variables.
   *
   * @param dict tables with model variables.
   */
  public DefaultSearchVars(Tables dict) {
    this.dictionary = dict;
  }

  /**
   * Collects variables from an array or collection into type-specific sets.
   *
   * @param variables the variables to collect
   * @param intVars set to add IntVar instances to
   * @param boolVars set to add BooleanVar instances to
   * @param setVars set to add SetVar instances to
   * @param floatVars set to add FloatVar instances to
   */
  private void collectVariables(
      Var[] variables,
      LinkedHashSet<IntVar> intVars,
      LinkedHashSet<BooleanVar> boolVars,
      LinkedHashSet<SetVar> setVars,
      LinkedHashSet<FloatVar> floatVars) {
    for (Var v : variables) {
      if (v instanceof BooleanVar var3) {
        if (!v.singleton()) {
          boolVars.add(var3);
        }
      } else if (v instanceof IntVar var2) {
        if (!v.singleton()) {
          intVars.add(var2);
        }
      } else if (v instanceof SetVar var1) {
        setVars.add(var1);
      } else if (v instanceof FloatVar fv) {
        floatVars.add(fv);
      }
    }
  }

  /**
   * Collects variables from a collection into type-specific sets.
   *
   * @param variables the variables to collect
   * @param intVars set to add IntVar instances to
   * @param boolVars set to add BooleanVar instances to
   * @param setVars set to add SetVar instances to
   * @param floatVars set to add FloatVar instances to
   */
  private void collectVariables(
      Iterable<Var> variables,
      LinkedHashSet<IntVar> intVars,
      LinkedHashSet<BooleanVar> boolVars,
      LinkedHashSet<SetVar> setVars,
      LinkedHashSet<FloatVar> floatVars) {
    for (Var v : variables) {
      if (v instanceof BooleanVar var3) {
        if (!v.singleton()) {
          boolVars.add(var3);
        }
      } else if (v instanceof IntVar var2) {
        if (!v.singleton()) {
          intVars.add(var2);
        }
      } else if (v instanceof SetVar var1) {
        setVars.add(var1);
      } else if (v instanceof FloatVar fv) {
        floatVars.add(fv);
      }
    }
  }

  /** Collects all output variables for search. */
  void outputVars() {

    // ==== Collect ALL OUTPUT variables ====

    LinkedHashSet<IntVar> intVarSet = new LinkedHashSet<>();
    LinkedHashSet<BooleanVar> boolVarSet = new LinkedHashSet<>();
    LinkedHashSet<SetVar> setVarSet = new LinkedHashSet<>();
    LinkedHashSet<FloatVar> floatVarSet = new LinkedHashSet<>();

    // collect output arrays
    for (int i = 0; i < dictionary.outputArray.size(); i++) {
      collectVariables(
          dictionary.outputArray.get(i).getArray(), intVarSet, boolVarSet, setVarSet, floatVarSet);
    }
    // collect output variables
    collectVariables(dictionary.outputVariables, intVarSet, boolVarSet, setVarSet, floatVarSet);

    intVars = intVarSet.toArray(new IntVar[0]);
    boolVars = boolVarSet.toArray(new BooleanVar[0]);
    setVars = setVarSet.toArray(new SetVar[0]);
    floatVars = floatVarSet.toArray(new FloatVar[0]);

    Arrays.sort(intVars, domainSizeComparator);
  }

  /**
   * It collects all variables that were identified as search variables by VariablesParameters class
   * during parsing variable definitions.
   */
  void defaultVars() {

    LinkedHashSet<IntVar> intVarSet = new LinkedHashSet<>();
    LinkedHashSet<BooleanVar> boolVarSet = new LinkedHashSet<>();
    Set<IntVar> aliasVars = collectAliasVars();

    collectIntAndBoolVarsFromArrays(intVarSet, boolVarSet, aliasVars);
    for (Var v : dictionary.defaultSearchVariables) {
      addVarToIntOrBool(intVarSet, boolVarSet, aliasVars, v);
    }
    intVars = intVarSet.toArray(new IntVar[0]);
    boolVars = boolVarSet.toArray(new BooleanVar[0]);
    Arrays.sort(intVars, domainSizeComparator);

    setVars = collectSetVars().toArray(new SetVar[0]);
    floatVars = collectFloatVars().toArray(new FloatVar[0]);
  }

  private Set<IntVar> collectAliasVars() {
    Set<IntVar> aliasVars = new LinkedHashSet<>();
    for (Map.Entry<IntVar, IntVar> e : dictionary.aliasTable.entrySet()) {
      aliasVars.add(e.getKey());
    }
    return aliasVars;
  }

  private void collectIntAndBoolVarsFromArrays(
      LinkedHashSet<IntVar> intVars, LinkedHashSet<BooleanVar> boolVars, Set<IntVar> aliasVars) {
    for (int i = 0; i < dictionary.defaultSearchArrays.size(); i++) {
      for (Var v : dictionary.defaultSearchArrays.get(i)) {
        if (!v.singleton()) {
          addVarToIntOrBool(intVars, boolVars, aliasVars, v);
        }
      }
    }
  }

  private void addVarToIntOrBool(
      LinkedHashSet<IntVar> intVars,
      LinkedHashSet<BooleanVar> boolVars,
      Set<IntVar> aliasVars,
      Var v) {
    if (v instanceof BooleanVar bv) {
      boolVars.add(bv);
    } else if (((IntVar) v).min() >= 0 && ((IntVar) v).max() <= 1 && aliasVars.contains(v)) {
      boolVars.add((BooleanVar) v);
    } else {
      intVars.add((IntVar) v);
    }
  }

  private LinkedHashSet<SetVar> collectSetVars() {
    LinkedHashSet<SetVar> setVars = new LinkedHashSet<>();
    for (int i = 0; i < dictionary.defaultSearchSetArrays.size(); i++) {
      for (Var v : dictionary.defaultSearchSetArrays.get(i)) {
        setVars.add((SetVar) v);
      }
    }
    for (Var v : dictionary.defaultSearchSetVariables) {
      setVars.add((SetVar) v);
    }
    return setVars;
  }

  private LinkedHashSet<FloatVar> collectFloatVars() {
    LinkedHashSet<FloatVar> floatVars = new LinkedHashSet<>();
    for (int i = 0; i < dictionary.defaultSearchFloatArrays.size(); i++) {
      for (Var v : dictionary.defaultSearchFloatArrays.get(i)) {
        floatVars.add((FloatVar) v);
      }
    }
    for (Var v : dictionary.defaultSearchFloatVariables) {
      floatVars.add((FloatVar) v);
    }
    return floatVars;
  }

  /**
   * Returns the integer variables for search.
   *
   * @return the integer variables
   */
  IntVar[] getIntVars() {
    return intVars;
  }

  /**
   * Returns the set variables for search.
   *
   * @return the set variables
   */
  SetVar[] getSetVars() {
    return setVars;
  }

  /**
   * Returns the boolean variables for search.
   *
   * @return the boolean variables
   */
  BooleanVar[] getBoolVars() {
    return boolVars;
  }

  /**
   * Returns the float variables for search.
   *
   * @return the float variables
   */
  FloatVar[] getFloatVars() {
    return floatVars;
  }

  /** {@inheritDoc} */
  @Override
  public String toString() {

    return "%% default int search variables = array1d(1.."
        + intVars.length
        + ", "
        + Arrays.asList(intVars)
        + ")\n"
        + "%% default boolean search variables = array1d(1.."
        + boolVars.length
        + ", "
        + Arrays.asList(boolVars)
        + ")\n"
        + "%% default set search variables = array1d(1.."
        + setVars.length
        + ", "
        + Arrays.asList(setVars)
        + ")\n"
        + "%% default float search variables = array1d(1.."
        + floatVars.length
        + ", "
        + Arrays.asList(floatVars)
        + ")\n";
  }
}
