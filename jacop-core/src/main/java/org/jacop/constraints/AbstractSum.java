/*
 * AbstractSum.java
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

import lombok.extern.slf4j.Slf4j;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;

/**
 * Abstract base class for SumInt and SumBool constraints. Provides shared relation constants,
 * relation parsing, and relation-to-string conversion.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public abstract class AbstractSum extends PrimitiveConstraint {

  /** Defines relation constants. */
  static final byte EQ = 0;

  static final byte LE = 1;
  static final byte LT = 2;
  static final byte NE = 3;
  static final byte GT = 4;
  static final byte GE = 5;

  /** Defines negated relations. */
  static final byte[] NEG_REL = {
    NE, // EQ=0,
    GT, // LE=1,
    GE, // LT=2,
    EQ, // NE=3,
    LE, // GT=4,
    LT // GE=5;
  };

  /** It specifies what relation is used by this constraint. */
  protected final byte relationType;

  /** The constraint store. */
  final Store store;

  /** It specifies a list of variables being summed. */
  final IntVar[] x;

  /** It specifies variable for the overall sum. */
  final IntVar sum;

  /** It specifies the number of variables. */
  final int l;

  /** Whether this constraint is reified. */
  boolean reified = true;

  /** Guide value for search heuristics. */
  int guideValue;

  /**
   * Constructs with pre-set fields. Subclasses must call this from their constructors.
   *
   * @param relationType the relation type byte
   * @param store the constraint store
   * @param x the variable array
   * @param sum the sum variable
   * @param l the effective list length
   */
  protected AbstractSum(byte relationType, Store store, IntVar[] x, IntVar sum, int l) {
    this.relationType = relationType;
    this.store = store;
    this.x = x;
    this.sum = sum;
    this.l = l;
  }

  /**
   * Static helper to parse a relation string before calling super().
   *
   * @param r the relation string
   * @return the byte code for the relation
   */
  protected static byte parseRelation(String r) {
    return switch (r) {
      case "==", "=" -> EQ;
      case "<" -> LT;
      case "<=", "=<" -> LE;
      case "!=" -> NE;
      case ">" -> GT;
      case ">=", "=>" -> GE;
      default -> {
        log.error("Wrong relation symbol in Sum constraint {}; assumed ==", r);
        yield EQ;
      }
    };
  }

  /**
   * Instance method for backward compatibility.
   *
   * @param r the relation string
   * @return the byte code for the relation
   */
  public byte relation(String r) {
    return parseRelation(r);
  }

  /**
   * Converts the internal relation type to its string representation.
   *
   * @return the string representation of the relation (e.g., "==", "{@literal <}", "{@literal >}").
   */
  public String rel2String() {
    return switch (relationType) {
      case EQ -> "==";
      case LT -> "<";
      case LE -> "<=";
      case NE -> "!=";
      case GT -> ">";
      case GE -> ">=";
      default -> "?";
    };
  }

  /**
   * Builds a common toString representation for sum constraints.
   *
   * @param constraintName the name of the constraint (e.g., "SumInt", "SumBool")
   * @return the formatted string
   */
  protected String toStringHelper(String constraintName) {
    StringBuilder result = new StringBuilder(id());
    result.append(" : ").append(constraintName).append("( [ ");

    for (int i = 0; i < l; i++) {
      result.append(x[i]);
      if (i < l - 1) {
        result.append(", ");
      }
    }
    result.append("], ");

    result.append(rel2String()).append(", ").append(sum).append(" )");

    return result.toString();
  }

  /**
   * Computes the guide variable for search heuristics based on regret calculation.
   *
   * @param vars the array of variables to consider
   * @param guideValueOut output array where guideValueOut[0] will be set to the computed guide
   *     value
   * @return the proposed variable (or null if none found)
   */
  public static Var computeGuideVariable(IntVar[] vars, int[] guideValueOut) {

    int regret = 1;
    Var proposedVariable = null;
    int guideVal = 0;

    for (IntVar v : vars) {

      IntDomain listDom = v.dom();

      if (v.singleton()) {
        continue;
      }

      int currentRegret = listDom.nextValue(listDom.min()) - listDom.min();

      if (currentRegret > regret) {
        regret = currentRegret;
        proposedVariable = v;
        guideVal = listDom.min();
      }

      currentRegret = listDom.max() - listDom.previousValue(listDom.max());

      if (currentRegret > regret) {
        regret = currentRegret;
        proposedVariable = v;
        guideVal = listDom.max();
      }
    }

    guideValueOut[0] = guideVal;
    return proposedVariable;
  }

  @Override
  public Var getGuideVariable() {
    int[] guideValueOut = new int[1];
    Var result = computeGuideVariable(x, guideValueOut);
    guideValue = guideValueOut[0];
    return result;
  }

  @Override
  public Constraint getGuideConstraint() {

    IntVar proposedVariable = (IntVar) getGuideVariable();
    if (proposedVariable != null) {
      return new XeqC(proposedVariable, guideValue);
    } else {
      return null;
    }
  }

  @Override
  public int getGuideValue() {
    return guideValue;
  }
}
