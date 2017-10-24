/*
 * DomainTranslator.java
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

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import org.jacop.core.IntVar;
import org.jacop.satwrapper.SatWrapper;
import org.jacop.satwrapper.WrapperComponent;

/**
 * A component that translates CP variables ranges to boolean clauses to
 * be added to the SAT solver
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 */
public final class DomainTranslator implements WrapperComponent {

    // wrapper
    private SatWrapper wrapper;

    // variables that have already been translated to clauses
    public Set<IntVar> translatedVars = new HashSet<IntVar>();

    /**
     * translates the variable to clauses, if not already done, and add
     * those clauses to the wrapper queue.
     *
     * @param variable the variable to translate
     *                 <p>
     *                 see Propagation via Lazy Clause Generation,
     *                 Olga Ohrimenko1 , Peter J. Stuckey , and Michael Codish
     */
    public void translate(IntVar variable) {

        if (!translatedVars.contains(variable)) {

            assert wrapper.log(this, "translation of variable %s to clauses", variable);

            translatedVars.add(variable);

            // the domain for the variable
            SatCPBridge domain = variable.satBridge;
            // the clause
            LinkedList<Integer> clause = new LinkedList<Integer>();

			/*
			 * special case: singleton
			 */
            if (variable.domain.singleton()) {
                int v = variable.domain.value();
                // [x=v]
                clause.add(domain.cpValueToBoolVar(v, true));
                wrapper.addModelClause(clause);
                clause.clear();
                // [x<=v]
                clause.add(domain.cpValueToBoolVar(v, false));
                wrapper.addModelClause(clause);
                return;
            }

			/*
			 * rule 1) ¬ [x<=d] \/ [x<=d+1]
			 */
            for (int i = domain.min; i < domain.max - 1; ++i) {
                clause.clear();
                //System.out.println(i);
                clause.add(-domain.cpValueToBoolVar(i, false));
                clause.add(domain.cpValueToBoolVar(i + 1, false));
                wrapper.addModelClause(clause);
            }
			
			/*
			 * rule 2) ¬ [x=d] \/ [x<=d]
			 */
            for (int i = domain.min; i < domain.max; ++i) {
                clause.clear();
                clause.add(-domain.cpValueToBoolVar(i, true));
                clause.add(domain.cpValueToBoolVar(i, false));
                wrapper.addModelClause(clause);
            }
			
			/*
			 * rule 3) ¬ [x=d] \/ ¬ [x<=d-1]
			 */
            for (int i = domain.min + 1; i <= domain.max; ++i) {
                clause.clear();
                clause.add(-domain.cpValueToBoolVar(i, true));
                clause.add(-domain.cpValueToBoolVar(i - 1, false));
                wrapper.addModelClause(clause);
            }
			
			/*
			 * rule 4) [x=l] \/ ¬ [x<=l]
			 */
            clause.clear();
            clause.add(domain.cpValueToBoolVar(domain.min, true));
            clause.add(-domain.cpValueToBoolVar(domain.min, false));
            wrapper.addModelClause(clause);

			/*
			 * rule 5) [x=d] \/ ¬ [x<=d] \/ [x<=d-1]
			 */
            for (int i = domain.min + 1; i < domain.max; ++i) {
                clause.clear();
                clause.add(domain.cpValueToBoolVar(i, true));
                clause.add(-domain.cpValueToBoolVar(i, false));
                clause.add(domain.cpValueToBoolVar(i - 1, false));
                wrapper.addModelClause(clause);
            }
			
			/*
			 * rule 6) [x=u] \/ [x<=u-1]
			 */
            clause.clear();
            clause.add(domain.cpValueToBoolVar(domain.max, true));
            clause.add(domain.cpValueToBoolVar(domain.max - 1, false));
            wrapper.addModelClause(clause);
        }
    }


    public void initialize(SatWrapper wrapper) {
        this.wrapper = wrapper;
    }


    @Override public String toString() {
        return String.format("DomainTranslator [%d variables]", translatedVars.size());
    }


}
