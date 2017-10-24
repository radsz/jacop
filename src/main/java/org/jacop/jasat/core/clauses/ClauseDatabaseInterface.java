/*
 * ClauseDatabaseInterface.java
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

package org.jacop.jasat.core.clauses;

import java.io.BufferedWriter;

/**
 *
 * Interface for clause databases or database stores. Any entity that 
 * contains clauses and can perform different operations on them. 
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 *
 */

public interface ClauseDatabaseInterface {

    /**
     * It adds a clause to the database. This can change the state of the solver, for
     * example if the clause is unsatisfiable in the current trail affectation,
     * the solver will get in the conflict state.
     *
     * @param clause  the clause to add
     * @param isModelClause defined if the clause is model clause
     * @return the unique ID referring to the clause
     */
    int addClause(int[] clause, boolean isModelClause);


    /**
     * It informs the ClausesDatabase that this literal is set, so that it
     * can perform unit propagation.
     *
     * @param literal  the literal that is set
     */
    void assertLiteral(int literal);

    /**
     * It removes the clause which unique ID is @param clauseId.
     * @param clauseId clause id
     */
    void removeClause(int clauseId);


    /**
     * It tells if the implementation of ClausesDatabase can remove clauses or not
     *
     * @param clauseId  the unique Id of the clause
     * @return true iff removal of clauses is possible
     */
    boolean canRemove(int clauseId);


    /**
     * It returns the clause obtained by resolution between clauseIndex and clause.
     * It will also modify in place the given SetClause (avoid allocating).
     *
     * @param clauseIndex  the unique id of the clause
     * @param clause  an explanation clause that is modified by resolution
     * @return the clause obtained by resolution
     */
    MapClause resolutionWith(int clauseIndex, MapClause clause);

    /**
     * Do everything needed to return to the given level.
     * @param level  the level to return to. Must be {@literal <} solver.getCurrentLevel().
     */
    void backjump(int level);

    /**
     * size of the database
     * @return the number of clauses in the database
     */
    int size();

    /**
     * It writes the clauses of the databases in cnf format to the specified
     * writer.
     *
     * @param output the output writer to which all the clauses will be written to.
     * @throws java.io.IOException execption from java.io package
     */
    void toCNF(BufferedWriter output) throws java.io.IOException;

}
