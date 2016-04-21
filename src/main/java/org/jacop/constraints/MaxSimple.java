/**
 *  MaxSimple.java 
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

import java.util.ArrayList;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.core.TimeStamp;

/**
 * MaxSimple constraint implements the Maximum/2 constraint. It provides the maximum
 * variable from all variables on the list. 
 * 
 * max(x1, x2) = max.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.4
 */

public class MaxSimple extends Constraint {

  static int counter = 1;

  /**
   * It specifies a variables between which a maximum value is being searched for.
   */
  public IntVar x1, x2;

  /**
   * It specifies variable max which stores the maximum value present in the list. 
   */
  public IntVar max;
  
  /**
   * It specifies the arguments required to be saved by an XML format as well as 
   * the constructor being called to recreate an object from an XML format.
   */
  public static String[] xmlAttributes = {"x1", "x2", "max"};
  
  /**
   * It constructs max constraint.
   * @param max variable denoting the maximum value
   * @param x1 first variable for which a  maximum value is imposed.
   * @param x2 second variable for which a  maximum value is imposed.
   */
  public MaxSimple(IntVar x1, IntVar x2, IntVar max) {

    assert ( x1 != null ) : "First variable is null";
    assert ( x2 != null ) : "Second variable is null";
    assert ( max != null ) : "Min variable is null";

    this.numberId = counter++;
    this.numberArgs = (short) (3);
    this.max = max;
    this.x1 = x1;
    this.x2 = x2;

    this.queueIndex = 1;

  }


  @Override
  public ArrayList<Var> arguments() {

    ArrayList<Var> variables = new ArrayList<Var>(3);

    variables.add(max);
    variables.add(x1);
    variables.add(x2);
    return variables;
  }

  @Override
  public void consistency(Store store) {
		
    do {

      int maxMax = max.max();

      x1.domain.inMax(store.level, x1, maxMax);
      x2.domain.inMax(store.level, x2, maxMax);
      
      store.propagationHasOccurred = false;
      
      int minValue = (x1.min() > x2.min()) ? x1.min() : x2.min();
      int maxValue = (x1.max() > x2.max()) ? x1.max() : x2.max();

      max.domain.in(store.level, max, minValue, maxValue);

    } while (store.propagationHasOccurred);
		
  }

  @Override
  public int getConsistencyPruningEvent(Var var) {

    // If consistency function mode
    if (consistencyPruningEvents != null) {
      Integer possibleEvent = consistencyPruningEvents.get(var);
      if (possibleEvent != null)
	return possibleEvent;
    }
    return IntDomain.BOUND;
  }

  // registers the constraint in the constraint store
  @Override
  public void impose(Store store) {


    max.putModelConstraint(this, getConsistencyPruningEvent(max));
    x1.putModelConstraint(this, getConsistencyPruningEvent(x1));
    x2.putModelConstraint(this, getConsistencyPruningEvent(x2));

    store.addChanged(this);
    store.countConstraint();

  }

  @Override
  public void removeConstraint() {
    max.removeConstraint(this);
    x1.removeConstraint(this);
    x2.removeConstraint(this);
  }

  @Override
  public boolean satisfied() {

    int MAX = max.min();
    boolean sat = x1.max() <= MAX && x2.max() <= MAX;
    
    return sat;
  }

  @Override
  public String toString() {
		
    StringBuffer result = new StringBuffer( id() );
		
    result.append(" : maxSimple(" + x1 + ", " + x1 + ", " + max + ")");

    return result.toString();
  }

  @Override
  public void increaseWeight() {
    if (increaseWeight) {
      max.weight++;
      x1.weight++;
      x2.weight++;
    }
  }
}
