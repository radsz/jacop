/*
 * Lex.java
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

package org.jacop.set.constraints;

import java.util.concurrent.atomic.AtomicInteger;

import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.IntDomain;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;

/**
 * It creates a {@literal <=} b constraint on two set variables. The
 * set variables are constrained to be lexicographically ordered.
 *
 * For example, 
 * {}{@literal <=}lex {}
 * {}{@literal <=}lex {1}
 * {1, 2}{@literal <=}lex {1, 2}
 * {1, 3}{@literal <=}lex {2}
 * {1}{@literal <=} {2}
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek 
 * @version 4.5
 */

public class AleB extends PrimitiveConstraint {

    static AtomicInteger idNumber = new AtomicInteger(0);

    /**
     * It specifies the first variable of the constraint
     */
    public SetVar a;

    /**
     * It specifies the second variable of the constraint
     */
    public SetVar b;

    /**
     * Negated constraint
     */
    AltB aGTb;

    /**
     * It constructs an Lexical ordering constraint to restrict the domain of the variables a and b.
     *
     * @param a variable that is restricted to be less than b with lexical order.
     * @param b variable that is restricted to be greater than a with lexical order.
     */
    public AleB(SetVar a, SetVar b) {

        checkInputForNullness(new String[]{"a", "b"}, new Object[]{a, b});

        numberId = idNumber.incrementAndGet();

        this.a = a;
        this.b = b;
	aGTb = new AltB(b,a, true);
	
        setScope(a, b);

    }

    /**
     * It constructs an Lexical ordering to be used in negated
     * constrained. Not to be used for imposing constraints.
     *
     * @param a variable that is restricted to be less than b with lexical order.
     * @param b variable that is restricted to be greater than a with lexical order.
     * @param negated used to distinguish constructors only.
     */
    AleB(SetVar a, SetVar b, boolean negated) {

        this.a = a;
        this.b = b;
    }

    @Override public void consistency(Store store) {

        if (a.domain.card().min() > 0)
            b.domain.inLUB(store.level, b, new IntervalDomain(a.domain.lub().min(), IntDomain.MaxInt));
	else
	    return;  // any b with cardinalirty > 0 is fine since a = {}

	// case for ground domains; check for <= domains
	if (a.domain.singleton() && b.domain.singleton())
	    if (! setLexLE(a.domain.glb(), b.domain.glb()))
		throw store.failException;

	
	if (b.domain.glb().getSize() > 0) {
	    ValueEnumeration aLubEnum = a.domain.lub().valueEnumeration();
	    ValueEnumeration bGlbEnum = b.domain.glb().valueEnumeration();	
	    int be = bGlbEnum.nextElement();
	    int ae = Integer.MIN_VALUE;
	    do {
		if (aLubEnum.hasMoreElements()) {
		    ae = aLubEnum.nextElement();

		    if (ae == be) {
			if (bGlbEnum.hasMoreElements()) {
			    be = bGlbEnum.nextElement();
			    if (! aLubEnum.hasMoreElements())
				return; // b has more elements than a 
			}
			else 
			    break;
		    }
		    else if (ae < be) {
			return; // b already greater
		    }
		    else { // ae > be
			throw store.failException;
		    }
		}
		else // b has more elements and up to now all exqual
		    return;
	    } while (true);
	}
    }

    boolean setLexLE(IntDomain x, IntDomain y) {
	
    	if (x.getSize() == 0 && y.getSize() >= 0)
    	    return true;
	
    	ValueEnumeration xe = x.valueEnumeration();
    	ValueEnumeration ye = y.valueEnumeration();

    	boolean le = false;

    	while (xe.hasMoreElements() && ye.hasMoreElements()) {
    	    int xv = xe.nextElement();
    	    int yv = ye.nextElement();

    	    if (xv < yv)
    		return true;
    	    else if (xv > yv)
    		return false;
	    
    	}
    	if (! xe.hasMoreElements())
    	    return true;
	
    	return le;
    }

    @Override public void notConsistency(Store store) {
	aGTb.consistency(store);
    }
    
    @Override public boolean satisfied() {
    	if (a.domain.singleton() && b.domain.singleton())
	    if (setLexLE(a.domain.glb(), b.domain.glb()))
		return true;
	return false;
    }

    @Override public boolean notSatisfied() {
	return aGTb.satisfied();
    }
    

    @Override protected int getDefaultNestedConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override protected int getDefaultNestedNotConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override protected int getDefaultNotConsistencyPruningEvent() {
        return IntDomain.ANY;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return SetDomain.ANY;
    }


    @Override public void impose(Store store) {

        super.impose(store);

    }

    @Override public String toString() {

        StringBuffer result = new StringBuffer();
        result.append(id() +" : AleB(");
        result.append(a).append(", ").append(b);
        result.append(")");
        return result.toString();

    }

}
