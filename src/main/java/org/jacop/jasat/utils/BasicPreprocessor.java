package org.jacop.jasat.utils;

import org.jacop.jasat.core.Core;
import org.jacop.jasat.core.clauses.MapClause;
import org.jacop.jasat.utils.structures.IntVec;

/**
 * a basic preprocessor. It aims at removing trivial clauses
 *
 * @author simon
 */
public class BasicPreprocessor {

    // flag to indicate the status of the currently processed clause
    private final static int UNTOUCHED = 0;
    private final static int SIMPLIFIED = 1;
    private final static int TRIVIAL = 2;


    // the core this preprocessor will add clauses to
    private Core core;

    // local clause
    private MapClause localClause = new MapClause();

    /**
     * add a clause (just parsed from a file, e.g.) to the solver, after
     * processing
     *
     * @param clause clause to be added
     */
    public void addModelClause(IntVec clause) {

        // simplify the clause. If trivial, just return
        switch (simplifyClause(clause)) {
            case UNTOUCHED:
                core.addModelClause(clause);
                break;
            case SIMPLIFIED:
                core.addModelClause(localClause.toIntArray(core.pool));
                break;
            case TRIVIAL:
                break;  // do nothing
            default:
                throw new AssertionError("should not have this value");
        }
    }

    /**
     * simplify the clause by removing duplicates and checking for
     * triviality.
     *
     * @param clause the clause to simplify
     * @return the status of the clause (see at beginning)
     */
    private int simplifyClause(IntVec clause) {
        localClause.clear();
        // state of the clause
        int state = UNTOUCHED;

        for (int i = 0; i < clause.numElem; ++i) {
            int literal = clause.array[i];

            // trivial clause
            if (localClause.containsLiteral(literal))
                state = SIMPLIFIED;
            else if (localClause.addLiteral(literal))
                return TRIVIAL;
        }

        // clause is not trivial
        return state;
    }


    public BasicPreprocessor(Core core) {
        this.core = core;
    }

}
