/*
 * SatTranslation.java
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

package org.jacop.satwrapper;

import java.util.ArrayList;
import java.util.List;

import org.jacop.core.IntVar;
import org.jacop.core.BooleanVar;
import org.jacop.core.Store;

/**
 * SatTranslation defines SAT clauses for typical logical constraints
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */
public class SatTranslation {

    public boolean debug = false;

    SatWrapper clauses;

    Store store;

    long numberClauses;

    public SatTranslation(Store store) {
        this.store = store;
        clauses = new SatWrapper();

        numberClauses = 0;
        clauses.empty = true;
    }

    public void generate_clause(IntVar[] a1, IntVar[] a2) {

        List<IntVar> a1reduced = new ArrayList<IntVar>();
        for (int i = 0; i < a1.length; i++)
            if (a1[i].min() == 1)
                return;
            else if (a1[i].max() != 0)
                a1reduced.add(a1[i]);
        List<IntVar> a2reduced = new ArrayList<IntVar>();
        for (int i = 0; i < a2.length; i++)
            if (a2[i].max() == 0)
                return;
            else if (a2[i].min() != 1)
                a2reduced.add(a2[i]);
        if (a1reduced.size() == 0 && a2reduced.size() == 0)
            throw store.failException;
        if (debug)
            System.out.println("generate clause, positive: " + a1reduced + ", negative: " + a2reduced);

        for (IntVar v : a1reduced)
            clauses.register(v);
        for (IntVar v : a2reduced)
            clauses.register(v);

        int[] a1IsOne = new int[a1reduced.size()];
        for (int i = 0; i < a1reduced.size(); ++i)
            a1IsOne[i] = clauses.cpVarToBoolVar(a1reduced.get(i), 1, true);
        int[] a2IsOne = new int[a2reduced.size()];
        for (int i = 0; i < a2reduced.size(); ++i)
            a2IsOne[i] = clauses.cpVarToBoolVar(a2reduced.get(i), 1, true);

        int[] clause = new int[a1reduced.size() + a2reduced.size()];
        for (int i = 0; i < a1reduced.size(); ++i)
            clause[i] = a1IsOne[i];
        for (int i = 0; i < a2reduced.size(); ++i)
            clause[a1reduced.size() + i] = -a2IsOne[i];
        clauses.addModelClause(clause);

        numberClauses++;

        // System.out.print(clauseToString(clause));

    }

    public void generate_clause_reif(IntVar[] a, IntVar[] b, IntVar r) {
        // ((a1 \/ ...\/ an) \/ (-b1 \/ ... \/ -bn)) <=> r
        // a1 \/ ...\/ an \/ -b1 \/ ... \/ -bn \/ -r
        // for all i: -ai \/ r
        // for all i:  bi \/ r
        IntVar[] bs = new IntVar[b.length + 1];
        for (int i = 0; i < b.length; i++)
            bs[i] = b[i];
        bs[b.length] = r;
        generate_clause(a, bs);
        for (int i = 0; i < a.length; i++)
            generate_clause(new IntVar[] {r}, new IntVar[] {a[i]});
        for (int i = 0; i < b.length; i++)
            generate_clause(new IntVar[] {b[i], r}, new IntVar[] {});
    }

    public void generate_or(IntVar[] a, IntVar c) {

        // (a1 \/ a2 \/ ... \/ an \/ -c)
        // /\
        // for all i: (-ai \/ c)
        for (int i = 0; i < a.length; i++)
            if (a[i].min() == 1) {
                c.domain.in(store.level, c, 1, 1);
                return;
            }

        generate_clause(a, new IntVar[] {c});
        for (int i = 0; i < a.length; i++)
            generate_clause(new IntVar[] {c}, new IntVar[] {a[i]});
    }

    public void generate_and(IntVar[] a, IntVar c) {

        // -a1 \/ -a2 \/ ... \/ c
        // /\
        // for all i: ai \/ -c
        for (int i = 0; i < a.length; i++)
            if (a[i].max() == 0) {
                c.domain.in(store.level, c, 0, 0);
                return;
            }

        generate_clause(new IntVar[] {c}, a);
        for (int i = 0; i < a.length; i++)
            generate_clause(new IntVar[] {a[i]}, new IntVar[] {c});

    }

    /**
     *  To represent XOR function in CNF one needs to have 2^{n-1} clauses, 
     *  where n is the size of your XOR function :(
     * Our method cuts list to 3 or 2 element parts, generates XOR for them
     * and composesd them back to the original XOR.
     * Further improvements possible, if using 4-7 decompositions.
     * @param a parameters to be xor'ed
     * @param c result
     */
    public void generate_xor(IntVar[] a, IntVar c) {

        if (a.length == 3) {
            generate_xor(a[0], a[1], a[2], c);
            return;
        } else if (a.length == 2) {
            generate_xor(a[0], a[1], c);
            return;
        } else if (a.length == 1) {
            // this case should not normally happen;
            // the only case if the user specified this case
            generate_eq(a[0], c);
            return;
        } else { // must be a.length > 3
            IntVar[] as = new IntVar[a.length - 2];
            BooleanVar t = new BooleanVar(store);
            for (int i = 3; i < a.length; i++) {
                as[i - 3] = a[i];
            }
            as[as.length - 1] = t;
            generate_xor(a[0], a[1], a[2], t);
            generate_xor(as, c);
        }
    }

    public void generate_xor(IntVar a, IntVar b, IntVar c) {
        // (a xor b) <=> c
        generate_neq_reif(a, b, c);
    }

    public void generate_xor(IntVar a, IntVar b, IntVar c, IntVar d) {
        // (a xor b xor c) <=> d
        generate_clause(new IntVar[] {a}, new IntVar[] {b, c, d});
        generate_clause(new IntVar[] {b}, new IntVar[] {a, c, d});
        generate_clause(new IntVar[] {c}, new IntVar[] {a, b, d});
        generate_clause(new IntVar[] {d}, new IntVar[] {a, b, c});

        generate_clause(new IntVar[] {b, c, d}, new IntVar[] {a});
        generate_clause(new IntVar[] {a, c, d}, new IntVar[] {b});
        generate_clause(new IntVar[] {a, b, d}, new IntVar[] {c});
        generate_clause(new IntVar[] {a, b, c}, new IntVar[] {d});
    }

    public void generate_eq(IntVar a, IntVar b) {
        // a = b
        // ===========
        // (-a \/ b) /\ ( a \/ -b)
        generate_clause(new IntVar[] {b}, new IntVar[] {a});
        generate_clause(new IntVar[] {a}, new IntVar[] {b});
    }


    public void generate_le(IntVar a, IntVar b) {
        // a =< b
        // ===========
        // -a \/ b
        generate_clause(new IntVar[] {b}, new IntVar[] {a});
    }

    public void generate_lt(IntVar a, IntVar b) {
        // a < b
        // ===========
        // -a /\ b
        generate_clause(new IntVar[] {}, new IntVar[] {a});
        generate_clause(new IntVar[] {b}, new IntVar[] {});
    }

    public void generate_eq_reif(IntVar a, IntVar b, IntVar c) {
        // a = b <=> c
        // ===========
        // (-a \/ b \/ -c) /\
        // (a \/ -b \/ -c) /\
        // (a \/ b \/ c) /\
        // (-a \/ -b \/ c)

        generate_clause(new IntVar[] {b}, new IntVar[] {a, c});
        generate_clause(new IntVar[] {a}, new IntVar[] {b, c});
        generate_clause(new IntVar[] {a, b, c}, new IntVar[] {});
        generate_clause(new IntVar[] {c}, new IntVar[] {a, b});

    }

    public void generate_neq_reif(IntVar a, IntVar b, IntVar c) {
        // a != b <=> c
        // ===========
        // (-a \/ b \/ c) /\
        // (a \/ -b \/ c) /\
        // (a \/ b \/ -c) /\
        // (-a \/ -b \/ -c)

        generate_clause(new IntVar[] {b, c}, new IntVar[] {a});
        generate_clause(new IntVar[] {a, c}, new IntVar[] {b});
        generate_clause(new IntVar[] {a, b}, new IntVar[] {c});
        generate_clause(new IntVar[] {}, new IntVar[] {a, b, c});

    }

    public void generate_le_reif(IntVar a, IntVar b, IntVar c) {
        // a =< b <=> c
        // ===========
        // (-a \/ b \/ -c) /\ (a \/ c) /\ (-b \/ c)
        generate_clause(new IntVar[] {b}, new IntVar[] {a, c});
        generate_clause(new IntVar[] {a, c}, new IntVar[] {});
        generate_clause(new IntVar[] {c}, new IntVar[] {b});
    }

    public void generate_lt_reif(IntVar a, IntVar b, IntVar c) {
        // a < b <=> c
        // ===========
        // (a \/ -b \/ c) /\ (-a \/ -c) /\ (b \/ -c)
        generate_clause(new IntVar[] {a, c}, new IntVar[] {b});
        generate_clause(new IntVar[] {}, new IntVar[] {a, c});
        generate_clause(new IntVar[] {b}, new IntVar[] {c});
    }

    public void generate_not(IntVar a, IntVar b) {
        // -a = b
        // ===========
        // (a \/ b) /\
        // (-a \/ -b)

        generate_clause(new IntVar[] {a, b}, new IntVar[] {});
        generate_clause(new IntVar[] {}, new IntVar[] {a, b});
    }


    public void generate_implication(IntVar a, IntVar b) {
        // a => b
        // ===========
        // -a \/ b

        generate_clause(new IntVar[] {b}, new IntVar[] {a});
    }

    public void generate_implication_reif(IntVar a, IntVar b, IntVar c) {
        // (a => b) <=> c
        // ===========
        // (-a \/ b \/ -c) /\
        // (a \/ c) /\
        // (-b \/ c) 

        generate_clause(new IntVar[] {b}, new IntVar[] {a, c});
        generate_clause(new IntVar[] {a, c}, new IntVar[] {});
        generate_clause(new IntVar[] {c}, new IntVar[] {b});
    }

    public void generate_allZero_reif(IntVar[] as, IntVar c) {
        // allZero(a) <=> c
        // - (a[0] \/ .. \/ a[n]) <=> c
        // ===========
        // /\_i (-a[i] \/ -c) /\ (a[0] \/ .. a[n] \/ c)

        // if any as[i] == 1 => c == 0
        for (int i = 0; i < as.length; i++)
            if (as[i].min() == 1) {
                c.domain.in(store.level, c, 0, 0);
                return;
            }

        IntVar[] v = new IntVar[as.length + 1];
        for (int i = 0; i < as.length; i++) {
            v[i] = as[i];
            generate_clause(new IntVar[] {}, new IntVar[] {as[i], c});
        }
        v[as.length] = c;
        generate_clause(v, new IntVar[] {});
    }

    /* 
    // Not efficient with SimpleCpVarDomain bridge implementation; needs LazyCpVarDomain (not yet implemented)
    public void generate_eqC_reif(IntVar x, int c, IntVar b) {
	// Assumes that both x and b are not ground and
	// c is still in the domain of x
	// (x = c) <=> b
	// ===========
	// ( -(x = c)) \/ b=1) /\ ( (x = c) \/ - b=1)
	System.out.println("generate_eqC_reif("+x+", "+c+", "+b+")");

	// clauses.register(x,false);
	// clauses.register(b,false);
	clauses.register(x);
	clauses.register(b);

	int xLiteral = clauses.cpVarToBoolVar(x, c, true);
	int bLiteral = clauses.cpVarToBoolVar(b, 1, true);

	int[] clause = new int[2];
	clause[0] = - xLiteral; 
	clause[1] = bLiteral; 
	clauses.addModelClause(clause);

	clause = new int[2];
	clause[0] = xLiteral; 
	clause[1] = - bLiteral; 
	clauses.addModelClause(clause);
	
	numberClauses += 2;
    }

    public void generate_neC_reif(IntVar x, int c, IntVar b) {
	// Assumes that both x and b are not ground and
	// c is still in the domain of x
	// (x != c) <=> b
	// ===========
	// ( -(x = c)) \/ b=0) /\ ( (x = c) \/ - b=0)
	
	clauses.register(x);
	clauses.register(b);

	int xLiteral = clauses.cpVarToBoolVar(x, c, true);
	int bLiteral = clauses.cpVarToBoolVar(b, 0, true);

	int[] clause = new int[2];
	clause[0] = - xLiteral; 
	clause[1] = bLiteral; 
	clauses.addModelClause(clause);

	clause = new int[2];
	clause[0] = xLiteral; 
	clause[1] = - bLiteral; 
	clauses.addModelClause(clause);

	numberClauses += 2;
    }

    // inefficient propagation for large domains by SimpleCpVarDomain
    // and LazyCpVarDomain is not yet implemented
    public void generate_geC_reif(IntVar x, int c, IntVar b) {
	// Assumes that both x and b are not ground and
	// c is still in the domain of x
	// (x >= c) <=> b
	// ===========
	// (x >= c) => b \/ (x >= c) <= b
	// ( -(x >= c)) \/ b=1) /\ ( (x >= c) \/ - b=1)
	// ( (x <= c-1) \/ b=1) /\ ( - (x <= c-1) \/ - b=1)
	
	clauses.register(x);
	clauses.register(b);

	int xLiteral = clauses.cpVarToBoolVar(x, c-1, false);
	int bLiteral = clauses.cpVarToBoolVar(b, 1, true);

	int[] clause = new int[2];
	clause[0] = xLiteral; 
	clause[1] = bLiteral; 
	clauses.addModelClause(clause);

	clause = new int[2];
	clause[0] = - xLiteral; 
	clause[1] = - bLiteral; 
	clauses.addModelClause(clause);

	numberClauses += 2;
    }

    public void generate_inSet_reif(IntVar x, org.jacop.core.IntDomain d, IntVar b) {
	// x = d1 \/ d = d2 \/ ... \/ x = dn <=> b
	// ===========
	// (x = d1 \/ d = d2 \/ ... \/ x = dn \/ -b) /\
	// (-(x =d1) \/ b) /\ ( -(x = d2) \/ b) /\ ... /\ ( -(x = dn) \/ b)

	clauses.register(x);
	clauses.register(b);

	int n = d.getSize();
	int[] xLiterals = new int[n];
	org.jacop.core.ValueEnumeration values = d.valueEnumeration();
	int j=0;
	while (values.hasMoreElements())
	    xLiterals[j] = clauses.cpVarToBoolVar(x, values.nextElement(), true);
	int bLiteral = clauses.cpVarToBoolVar(b, 1, true);

	int[] clause = new int[n+1];
	for (int i = 0; i < n; i++) 
	    clause[i] = xLiterals[i];
	clause[n-1] = - bLiteral; 
	clauses.addModelClause(clause);

	numberClauses++;

	for (int i = 0; i < n; i++) {
	    clause = new int[2];
	    clause[0] = - xLiterals[i]; 
	    clause[1] = bLiteral; 
	    clauses.addModelClause(clause);

	    numberClauses++;
	}
    }
    */

    public void impose() {

        store.countConstraint();

        store.impose(clauses);

    }

    public long numberClauses() {
        return numberClauses;
    }


    String clauseToString(int[] clause) {

        StringBuffer buffer = new StringBuffer();

        for (int i = 0; i < clause.length; i++)
            buffer.append(clause[i] + " ");

        buffer.append("\n");
        return buffer.toString();
    }
}
