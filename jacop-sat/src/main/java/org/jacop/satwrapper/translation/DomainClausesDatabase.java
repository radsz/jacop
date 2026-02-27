/*
 * DomainClausesDatabase.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.satwrapper.translation;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.io.BufferedWriter;
import org.jacop.core.Store;
import org.jacop.jasat.core.clauses.AbstractClausesDatabase;
import org.jacop.jasat.core.clauses.MapClause;
import org.jacop.jasat.utils.Utils;
import org.jacop.satwrapper.SatWrapper;
import org.jacop.satwrapper.WrapperComponent;

/*
 * NOTE :
 * - there are no real clauses, only integers that are given for propagation,
 * that can be used later to get explanations
 * - those integers are the solver's trail size at the time we propagate the
 * literal, to avoid redundancy
 *
 * NOTES : future improvements could be
 * - for the solver, implement some interface to propagate many literals at once
 * (which would be more efficient than propagating one by one). Not urgent.
 */

/**
 * Clause database designed to handle efficiently CP domain constraints, with the interface of
 * boolean clauses databases.
 *
 * <p>This database must be added in the SAT solver (ideally at first position) and linked to the
 * wrapper; it can then propagate literals that have a CP semantic with respect to their meaning
 * about domains.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
public final class DomainClausesDatabase extends AbstractClausesDatabase
    implements WrapperComponent {

  // sat wrapper
  private SatWrapper wrapper;

  // for each literal propagated by this database, the asserted literal that
  // is the cause for the propagation
  private int[] propagationCauses = new int[40];

  /**
   * This is responsible for propagating literals within the SAT solver to keep domain constraints
   * coherent. It is informed by the SAT solver that some literal has been set, and propagate other
   * variable literals.
   */
  public void assertLiteral(int assertedLiteral) {

    /*
     * only do something for literals representing a variable, which have
     * not yet been examined
     */
    if (!wrapper.isVarLiteral(assertedLiteral)) {
      return;
    } else {
    }

    // get the value this literal corresponds to
    SatCpBridge domain = wrapper.boolVarToDomain(assertedLiteral);
    if (domain.isTranslated()) {
      if (ASSERTS_ENABLED
          && !(wrapper.log(this, "variable %s is ignored because translated", domain.variable))) {
        throw new IllegalStateException("Assertion failed");
      }
      return;
    }

    // delegate propagation to the range
    domain.propagate(assertedLiteral);
  }

  /**
   * Propagates the literal directly in the SAT solver.
   *
   * @param literal the literal to propagate
   * @param assertedLiteral the literal that has been the origin of the propagation
   */
  public void propagate(int literal, int assertedLiteral) {
    /*
     * The future index of the literal in the trail is used as a clause
     * index to explain the propagation. It is quite a hack, but it allows
     * to remember which literal was propagated by which fake clause.
     */

    // clause index to give as an explanation for this propagation
    int clauseIndex = trail.size();
    int clauseId = indexToUniqueId(clauseIndex);
    int varIdx = Math.abs(literal);

    if (trail.isSet(varIdx)) {
      // no need to propagate, this variable has already a value

      if (trail.values[varIdx] == -literal) {
        // this is a conflict ! build the conflict clause
        MapClause conflictClause = core.explanationClause;
        conflictClause.clear();
        conflictClause.addLiteral(-assertedLiteral);
        conflictClause.addLiteral(literal);

        // wrapper.log(this, "  failure : literal "+literal+
        //   " meaning "+wrapper.showLiteralMeaning(literal)+
        //   " is set to "+trail.values[varIdx]
        //   +" (explanation "+conflictClause+")");

        // trigger the conflict and fail
        core.triggerConflictEvent(conflictClause);
        throw Store.failException;

      } else {
        // nothing to do, literal is already set to the right value
      }
    } else {

      /*
       * trigger propagate event in the solver. All those propagated
       * literals will only be taken into account by the solver after
       * all literals in toPropagate are propagated
       */
      core.triggerPropagateEvent(literal, clauseId);

      // ignore this literal, now

      // remember which asserted literal is cause for this propagation
      if (propagationCauses.length <= varIdx) {
        propagationCauses = Utils.resize(propagationCauses, 2 * varIdx, pool);
      }
      propagationCauses[varIdx] = assertedLiteral;

      // invariant : the explanation is equal to the depth in trail stack
      if (ASSERTS_ENABLED && trail.assertionStack.array[clauseIndex] != varIdx) {
        throw new IllegalStateException("Assertion failed");
      }
      if (ASSERTS_ENABLED && trail.values[varIdx] != literal) {
        throw new IllegalStateException("Assertion failed");
      }
      if (ASSERTS_ENABLED && clauseId != trail.getExplanation(varIdx)) {
        throw new IllegalStateException("Assertion failed");
      }
    }
  }

  /** Clear everything (no more propagations or ignored literals). */
  private void clear() {
    // No-op: nothing to clear for this database.
  }

  /**
   * To get a real clause to resolve with, we seek for the clause at the origin of the propagation.
   */
  public MapClause resolutionWith(int clauseIndex, MapClause clause) {
    if (ASSERTS_ENABLED && uniqueIdToIndex(clauseIndex) != clauseIndex) {
      throw new IllegalStateException("Assertion failed");
    }

    if (ASSERTS_ENABLED
        && !(wrapper.log(this, "asked resolution with (index %d) %s", clauseIndex, clause))) {
      throw new IllegalStateException("Assertion failed");
    }

    // literal that has been propagated
    int propagatedVar = trail.assertionStack.array[clauseIndex];
    int propagatedLiteral = trail.values[propagatedVar];
    // literal that has been asserted, and propagated the previous one
    int assertedLiteral = propagationCauses[propagatedVar];

    if (ASSERTS_ENABLED
        && !(wrapper.log(
            this,
            "resolution with "
                + propagatedLiteral
                + " and "
                + (-assertedLiteral)
                + " meaning "
                + wrapper.showLiteralMeaning(propagatedLiteral)
                + " or "
                + wrapper.showLiteralMeaning(-assertedLiteral)))) {
      throw new IllegalStateException("Assertion failed");
    }

    if (ASSERTS_ENABLED
        && !((!clause.containsLiteral(assertedLiteral))
            || (!clause.containsLiteral(-propagatedLiteral)))) {
      throw new IllegalStateException("Assertion failed");
    }

    // resolve clause with [-assertedLiteral, propagatedLiteral]
    clause.partialResolveWith(-assertedLiteral);
    clause.partialResolveWith(propagatedLiteral);

    return clause;
  }

  /** {@inheritDoc} */
  public void backjump(int level) {

    // clear everything
    clear();
  }

  @Override
  public int rateThisClause(int[] clause) {
    // no clause should be added
    return CLAUSE_RATE_UNSUPPORTED;
  }

  @Override
  public int size() {
    return 0; // 0 clauses, always !
  }

  /** {@inheritDoc} */
  public int addClause(int[] clause, boolean isModel) {
    throw new AssertionError("oh noes !");
  }

  /** {@inheritDoc} */
  public void removeClause(int clauseId) {
    throw new AssertionError("oh noes !");
  }

  /** {@inheritDoc} */
  public boolean canRemove(int clauseId) {
    return false;
  }

  @Override
  public String toString(String prefix) {
    return "constraint clause database (" + wrapper.registeredVars.size() + " CP variables)";
  }

  /** {@inheritDoc} */
  public void initialize(SatWrapper wrapper) {
    this.wrapper = wrapper;
  }

  @Override
  public void toCnf(BufferedWriter output) {

    if (!wrapper.registeredVars.equals(wrapper.domainTranslator.translatedVars)) {
      throw new UnsupportedOperationException("Not supported yet.");
    }
  }
}
