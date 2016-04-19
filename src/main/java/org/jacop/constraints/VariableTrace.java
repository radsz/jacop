/**
 *  VariableTrace.java 
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


package org.jacop.constraints;

import org.jacop.core.Var;
import org.jacop.core.Store;
import org.jacop.core.IntDomain;

import java.util.ArrayList;

/**
 * VariableTrace is a daemon that prints information on variables whenever they are changed.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.4
 */

public class VariableTrace extends Constraint {
  
  static int idNumber = 1;
	
  Var[] vars;
  Store store;
  
  /**
   * It constructs trace daemon for variable v
   * @param v variable to be traced
   */
  public VariableTrace(Var v) {
    numberId = idNumber++;
    
    vars = new Var[1];
    vars[0] = v;
  }

  /**
   * It constructs trace daemon for variables vs
   * @param v variables to be traced
   */
  public VariableTrace(Var[] vs) {
    numberId = idNumber++;
    
    vars = new Var[vs.length];
    for (int i = 0; i < vs.length; i++) {
      vars[i] = vs[i];
    }
  }

  /**
   * It constructs trace daemon for variables vs
   * @param v variables to be traced
   */
  public VariableTrace(ArrayList<Var> vs) {
    numberId = idNumber++;
    
    vars = new Var[vs.size()];
    for (int i = 0; i < vs.size(); i++) {
      vars[i] = vs.get(i);
    }
  }

  public ArrayList<Var> arguments() {
    ArrayList<Var> Variables = new ArrayList<Var>(vars.length);

    Variables.addAll(java.util.Arrays.asList(vars));

    return Variables;
  }

  public void impose(Store store) {

    this.store = store;

    store.registerRemoveLevelLateListener(this);

    for (Var v : vars) {
      v.putModelConstraint(this, getConsistencyPruningEvent(v));
      // we do not want to print initial values
      // queueVariable(store.level, v); 
    }

    store.countConstraint();
  }
  
  public void consistency(Store store) {
  }

  public int getConsistencyPruningEvent(Var var) {
    // If consistency function mode
    if (consistencyPruningEvents != null) {
      Integer possibleEvent = consistencyPruningEvents.get(var);
      if (possibleEvent != null)
	return possibleEvent;
    }
    return IntDomain.ANY;
  }

  public void queueVariable(int level, Var var) {

    System.out.println("Var: "+ var + ", level: " + level + ", constraint: "+ store.currentConstraint);

  }

  @Override
  public void removeLevelLate(int level) {

    System.out.print("Restore level: " + level + ", vars: ");

    for (Var v : vars) {
      System.out.print(v + " ");
    }
    System.out.println();
  }

  public void removeConstraint() {
  }

  public boolean satisfied() {
    return false;
  }

  @Override
  public String toString() {

    StringBuffer result = new StringBuffer( id() );

    result.append(" : variableTrace([");

    for (int i = 0; i < vars.length; i++) {
      result.append(vars[i]);
      if (i < vars.length - 1)
	result.append(", ");
    }
    result.append("])");
		
    return result.toString();
    
  }

  public void increaseWeight() {
  }
  
}
