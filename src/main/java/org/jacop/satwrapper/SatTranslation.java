/**
 *  SatTranslation.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

package org.jacop.satwrapper;

import java.util.ArrayList;
 
import org.jacop.core.IntVar;
import org.jacop.core.Store;


/**
 * SatTranslation defines SAT clauses for typical logical constraints
 *
 * @author Krzysztof Kuchcinski
 * @version 4.2.1
 */
public class SatTranslation {

    final boolean debug = false;

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

	ArrayList<IntVar> a1reduced = new ArrayList<IntVar>();
	for (int i = 0; i < a1.length; i++) 
	    if (a1[i].min() == 1)
		return;
	    else if (a1[i].max() != 0)
		a1reduced.add(a1[i]);
	ArrayList<IntVar> a2reduced = new ArrayList<IntVar>();
	for (int i = 0; i < a2.length; i++) 
	    if (a2[i].max() == 0)
		return;
	    else if (a2[i].min() != 1)
		a2reduced.add(a2[i]);
	if (a1reduced.size() == 0 && a2reduced.size() == 0 )
	    throw store.failException;
	if (debug)
	    System.out.println("generate clause, positive: "+ a1reduced+ ", negative: "+a2reduced);

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
	    clause[a1reduced.size() + i] = - a2IsOne[i];
	clauses.addModelClause(clause);

	numberClauses++;
    }

    public void generate_clause_reif(IntVar[] a, IntVar[] b, IntVar r) {
	// ((a1 \/ ...\/ an) \/ (-b1 \/ ... \/ -bn)) <=> r
	// a1 \/ ...\/ an \/ -b1 \/ ... \/ -bn \/ -r
	// for all i: -ai \/ r
	// for all i:  bi \/ r
	IntVar[] bs = new IntVar[b.length+1];
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
	generate_clause(a, new IntVar[] {c});
	for (int i = 0; i < a.length; i++) 
	    generate_clause(new IntVar[] {c}, new IntVar[] {a[i]});
    }


    public void generate_and(IntVar[] a, IntVar c) {

	// -a1 \/ -a2 \/ ... \/ c
	// /\
	// for all i: ai \/ -c

	generate_clause(new IntVar[] {c}, a);
	for (int i = 0; i < a.length; i++) 
	    generate_clause(new IntVar[] {a[i]}, new IntVar[] {c});

    }
    
    public void generate_xor(IntVar[] a, IntVar c) {

	// for all i: ai \/_{for all j!=i}: -aj \/ -c
	// for all i: -ai \/_{for all j!=i}: aj \/ c
	int k = 0;
	IntVar[] as = new IntVar[a.length];
	for (int i = 0; i < a.length; i++) {
	    for (int j = 0; j < a.length; j++)
		if (i != j) 
		    as[k++] = a[i];
	    as[a.length] = c;
	    generate_clause(new IntVar[] {a[i]}, as);
	    generate_clause(as, new IntVar[] {a[i]});
	}
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

	generate_clause(new IntVar[] {b,c}, new IntVar[] {a});
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


    public void impose() {

	store.countConstraint();

	store.impose(clauses);

    }

    public long numberClauses() {
	return numberClauses;
    }
}
