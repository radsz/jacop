/**
 *  LeastDiff.java 
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

package org.jacop.examples.fd;

import java.util.ArrayList;

import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.SumWeight;
import org.jacop.constraints.XgtY;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * Simple least Diff problem.
 *
 * Minimize the difference ABCDE - FGHIJ 
 *                     where A..J is all different in the range 0..9.
 *
 * The solution is: 50123 - 49876 = 247
 * 
 * JaCoP Model by Hakan Kjellerstrand (hakank@bonetmail.com)
 * Also see http://www.hakank.org/JaCoP/
 * 
 * @author Hakan Kjellerstrand and Radoslaw Szymanek
 *
 */

public class LeastDiff extends ExampleFD {
     
    @Override
	public void model() {
        
    	// Creating constraint store . 
        // This object contains information about all the constraints and variables.    
        store = new Store();
        
        // Creating Variables (finite domain variables). 
        // There are as many variables as there are letters/digits.
        IntVar a = new IntVar(store, "a", 0, 9);
        IntVar b = new IntVar(store, "b", 0, 9);
        IntVar c = new IntVar(store, "c", 0, 9);
        IntVar d = new IntVar(store, "d", 0, 9);
        IntVar e = new IntVar(store, "e", 0, 9);
        IntVar f = new IntVar(store, "f", 0, 9);
        IntVar g = new IntVar(store, "g", 0, 9);
        IntVar h = new IntVar(store, "h", 0, 9);
        IntVar i = new IntVar(store, "i", 0, 9);
        IntVar j = new IntVar(store, "j", 0, 9);
        
        cost = new IntVar(store, "diff", 0, 99999);    
        
        // Creating arrays for FDVs
        IntVar digits[] = { a,b,c,d,e,f,g,h,i,j };
        IntVar abcde[]  = { a,b,c,d,e };
        IntVar fghij[]  = { f,g,h,i,j };
        
        // Creating and imposing constraints
        
        // Imposing inequalities constraints between letters
        // Only one global constraint to make sure that all digits are different.
        store.impose(new Alldifferent(digits));
        
        int[] weights5 = { 10000, 1000, 100, 10, 1 };
        IntVar value_abcde = new IntVar(store, "v_abcde", 0, 99999);
        IntVar value_fghij = new IntVar(store, "v_fghij", 0, 99999);
        
        // Constraints for getting value for words
        store.impose(new SumWeight (abcde, weights5, value_abcde));
        store.impose(new SumWeight (fghij, weights5, value_fghij));
        
        // abcde > fghij
        store.impose(new XgtY (value_abcde, value_fghij));
        
        
        // Main equation of the problem:
        //    diff = abcde - fghij
        //  -> 
        //    diff + fghij = abcde
        // It would be niced with a constraint XminusYeqZ(...), though
        store.impose(new XplusYeqZ (cost, value_fghij, value_abcde));
    
        vars = new ArrayList<IntVar>();
        for (IntVar v : digits) vars.add(v);
        
    }

    
    /**
     * It executes the program which solves this simple optimization problem.
     * @param args
     */
    public static void main(String args[]) {

    	LeastDiff example = new LeastDiff();
    	
    	example.model();
    	
    	example.searchSmallestDomain(true);
    	
    }
    
} 
