/*
 * DomainClausesDatabase.java
 * <p>
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

package org.jacop.satwrapper.translation;

import java.io.BufferedWriter;
import java.io.IOException;

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
 * clause database designed to handle efficiently CP domain constraints, with
 * the interface of boolean clauses databases.
 * <p>
 * This database must be added in the SAT solver (ideally at first position)
 * and linked to the wrapper; it can then propagate literals that have
 * a CP semantic with respect to their meaning about domains.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 */
public final class DomainClausesDatabase extends AbstractClausesDatabase implements WrapperComponent {

    // sat wrapper
    private SatWrapper wrapper;

    // cache of literals we do not need to check (TODO: replace by IntSet ?)
    //private BitSet ignoreCache = new BitSet();

    // for each literal propagated by this database, the asserted literal that
    // is the cause for the propagation
    private int[] propagationCauses = new int[40];

    /**
     * this is responsible for propagating literals within the SAT solver
     * to keep domain constraints coherent. It is informed by the SAT solver
     * that some literal has been set, and propagate other variable literals.
     */
    public void assertLiteral(int assertedLiteral) {

		/*
    if (ignoreCache.get(Math.abs(assertedLiteral))) {
			// ignore some literals
			//wrapper.log(this, "  (ignored) called on literal "+assertedLiteral
			//		+" meaning "+wrapper.showLiteralMeaning(assertedLiteral));
			return;
		}
		*/
		
		/*
		 * only do something for literals representing a variable, which have
		 * not yet been examined
		 */
        if (!wrapper.isVarLiteral(assertedLiteral)) {
            //wrapper.log(this,"  (ignored) called on literal "+assertedLiteral+" meaning nothing");
            return;
        } else {
            //wrapper.log(this, "  called on literal "+assertedLiteral+" meaning "+
            //	wrapper.showLiteralMeaning(assertedLiteral));
        }

        // get the value this literal corresponds to
        SatCPBridge domain = wrapper.boolVarToDomain(assertedLiteral);
        if (domain.isTranslated()) {
            assert wrapper.log(this, "variable %s is ignored because translated", domain.variable);
            return;
        }

        // delegate propagation to the range
        domain.propagate(assertedLiteral);
    }

    /**
     * propagates the literal directly in the SAT solver
     *
     * @param literal         the literal to propagate
     * @param assertedLiteral the literal that has been the origin of the propagation
     */
    public void propagate(int literal, int assertedLiteral) {
		/*
		 * The future index of the literal in the trail is used as a clause
		 * index to explain the propagation. It is quite a hack, but it allows
		 * to remember which literal was propagated by which fake clause.
		 */

        // clause index to give as an explanation for this propagation
        int clauseIndex = trail.size(); // TODO: faster?
        int clauseId = indexToUniqueId(clauseIndex);
        int var = Math.abs(literal);

        if (trail.isSet(var)) {
            // no need to propagate, this variable has already a value

            if (trail.values[var] == -literal) {
                // this is a conflict ! build the conflict clause
                MapClause conflictClause = core.explanationClause;
                conflictClause.clear();
                conflictClause.addLiteral(-assertedLiteral);
                conflictClause.addLiteral(literal);

                //wrapper.log(this, "  failure : literal "+literal+
                //		" meaning "+wrapper.showLiteralMeaning(literal)+
                //		" is set to "+trail.values[var]
                //		+" (explanation "+conflictClause+")");

                // trigger the conflict and fail
                core.triggerConflictEvent(conflictClause);
                throw Store.failException;

            } else {
                // nothing to do, literal is already set to the right value
                ////ignoreCache.set(Math.abs(literal));
                //wrapper.log(this, "  does not propagate literal "+literal
                //		+" meaning "+wrapper.showLiteralMeaning(literal));
            }
        } else {

            //wrapper.log(this, "  propagate literal "+literal+" meaning "+
            //		wrapper.showLiteralMeaning(literal)
            //		+" at fake index "+clauseIndex);

			/* 
			 * trigger propagate event in the solver. All those propagated
			 * literals will only be taken into account by the solver after
			 * all literals in toPropagate are propagated
			 */
            core.triggerPropagateEvent(literal, clauseId);

            // ignore this literal, now
            ////ignoreCache.set(Math.abs(literal));

            // remember which asserted literal is cause for this propagation
            if (propagationCauses.length <= var)
                propagationCauses = Utils.resize(propagationCauses, 2 * var, pool);
            propagationCauses[var] = assertedLiteral;

            // invariant : the explanation is equal to the depth in trail stack
            // FIXME : check it
            assert trail.assertionStack.array[clauseIndex] == var;
            assert trail.values[var] == literal;
            assert clauseId == trail.getExplanation(var);
        }

    }

    /**
     * clear everything (no more propagations or ignored literals)
     */
    private void clear() {
        //ignoreCache.clear();
    }



    /**
     * to get a real clause to resolve with, we seek for the clause at the
     * origin of the propagation.
     */
    public MapClause resolutionWith(int clauseIndex, MapClause clause) {
        assert uniqueIdToIndex(clauseIndex) == clauseIndex;

        assert wrapper.log(this, "asked resolution with (index %d) %s", clauseIndex, clause);

        // literal that has been propagated
        int propagatedVar = trail.assertionStack.array[clauseIndex];
        int propagatedLiteral = trail.values[propagatedVar];
        // literal that has been asserted, and propagated the previous one
        int assertedLiteral = propagationCauses[propagatedVar];

        assert wrapper.log(this, "resolution with " + (propagatedLiteral) + " and " + (-assertedLiteral) + " meaning " + wrapper
            .showLiteralMeaning(propagatedLiteral) + " or " + wrapper.showLiteralMeaning(-assertedLiteral));

        assert (!clause.containsLiteral(assertedLiteral)) || (!clause.containsLiteral(-propagatedLiteral));

        // resolve clause with [-assertedLiteral, propagatedLiteral]
        //	if (! clause.removeLiteral(assertedLiteral))
        //		clause.addLiteral(- assertedLiteral);
        clause.partialResolveWith(-assertedLiteral);
        //	if (! clause.removeLiteral(- propagatedLiteral))
        //		clause.addLiteral(propagatedLiteral);
        clause.partialResolveWith(propagatedLiteral);

        return clause;
    }


    public void backjump(int level) {

        //wrapper.log(this, "backjump to level "+level);

        // clear everything
        clear();
    }

    @Override public int rateThisClause(int[] clause) {
        // no clause should be added
        return CLAUSE_RATE_UNSUPPORTED;
    }

    @Override public int size() {
        // TODO : compute the number of clauses that *would* be needed
        return 0;  // 0 clauses, always !
    }


    public int addClause(int[] clause, boolean isModel) {
        throw new AssertionError("oh noes !");
    }


    public void removeClause(int clauseId) {
        throw new AssertionError("oh noes !");
    }


    public boolean canRemove(int clauseId) {
        return false;
    }

    @Override public String toString(String prefix) {
        StringBuilder sb = new StringBuilder();
        sb.append("constraint clause database (");
        sb.append(wrapper.registeredVars.size()).append(" CP variables)");
        return sb.toString();
    }



    public void initialize(SatWrapper wrapper) {
        this.wrapper = wrapper;
    }

    @Override public void toCNF(BufferedWriter output) throws IOException {

        if (!wrapper.registeredVars.equals(wrapper.domainTranslator.translatedVars))
            throw new UnsupportedOperationException("Not supported yet.");

        // TODO, perform translation for toCNF operation only.
    }

}
