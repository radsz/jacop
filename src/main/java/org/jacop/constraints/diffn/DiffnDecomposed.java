/**
 *  Diffn.java 
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


package org.jacop.constraints.diffn;

import java.util.ArrayList;

import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Min;
import org.jacop.constraints.Max;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.cumulative.CumulativeBasic;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.core.IntVar;
import org.jacop.core.IntDomain;

/**
 * Diffn constraint assures that any two rectangles from a vector of rectangles
 * does not overlap in at least one direction. It is a simple implementation which
 * does not use sophisticated techniques for efficient backtracking.
 * 
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

public class DiffnDecomposed extends DecomposedConstraint {

  static int idNumber = 1;

  int numberArgs;

  ArrayList<Constraint> constraints = null;
  
  ArrayList<Var> auxVar = new ArrayList<Var>();
  
  IntVar[] x;
  IntVar[] y;
  IntVar[] lx;
  IntVar[] ly;
  
  /**
   * It specifies a diff constraint. 
   * @param rectangles list of rectangles which can not overlap in at least one dimension.
   */
  public DiffnDecomposed(IntVar[][] rectangle) {
    
    assert (rectangle != null) : "Rectangles list is null";

    queueIndex = 2;
    idNumber++;

    x = new IntVar[rectangle.length];
    y = new IntVar[rectangle.length];
    lx = new IntVar[rectangle.length];
    ly = new IntVar[rectangle.length];
    
    for (int i = 0; i < rectangle.length; i++) {
      assert (rectangle[i] != null) : i + "-th rectangle in the list is null";
      assert (rectangle[i].length != 4) : "The rectangle has to have exactly two dimensions";

      x[i] = rectangle[i][0];
      y[i] = rectangle[i][1];
      lx[i] = rectangle[i][2];
      ly[i] = rectangle[i][3];
    }
  }

  /**
   * It constructs a diff constraint.
   * @param origin1 list of variables denoting origin of the rectangle in the first dimension.
   * @param origin2 list of variables denoting origin of the rectangle in the second dimension.
   * @param length1 list of variables denoting length of the rectangle in the first dimension.
   * @param length2 list of variables denoting length of the rectangle in the second dimension.
   */

  public DiffnDecomposed(IntVar[] origin1, IntVar[] origin2, IntVar[] length1, IntVar[] length2) {

    assert (origin1 != null) : "x list is null";
    assert (origin2 != null) : "y list is null";
    assert (length1 != null) : "lx list is null";
    assert (length2 != null) : "ly list is null";

    int size = origin1.length;
    if (size == origin1.length && size == origin2.length && size == length1.length && size == length2.length) {
			
      this.queueIndex = 2;
		
      idNumber++;
      this.numberArgs = (short) (size * 4);

      x = new IntVar[origin1.length];
      y = new IntVar[origin2.length];
      lx = new IntVar[length1.length];
      ly = new IntVar[length2.length];
      
      System.arraycopy(origin1, 0, x, 0, size);
      System.arraycopy(origin2, 0, y, 0, size);
      System.arraycopy(length1, 0, lx, 0, size);
      System.arraycopy(length2, 0, ly, 0, size);
    }
    else {
      String s = "\nNot equal sizes of Variable vectors in Nooverlap";
      throw new IllegalArgumentException(s);
    }

  }
	
  /**
   * It specifies a diffn constraint. 
   * @param rectangles list of rectangles which can not overlap in at least one dimension.
   */
  public DiffnDecomposed(ArrayList<? extends ArrayList<? extends IntVar>> rectangle) {

    assert (rectangle != null) : "Rectangles list is null";

    this.queueIndex = 2;
    idNumber++;

    x = new IntVar[rectangle.size()];
    y = new IntVar[rectangle.size()];
    lx = new IntVar[rectangle.size()];
    ly = new IntVar[rectangle.size()];
    
    for (int i = 0; i < rectangle.size(); i++) {
      assert (rectangle.get(i) != null) : i + "-th rectangle in the list is null";
      assert (rectangle.get(i).size() != 4) : "The rectangle has to have exactly two dimensions";

      x[i] = rectangle.get(i).get(0);
      y[i] = rectangle.get(i).get(1);
      lx[i] = rectangle.get(i).get(2);
      ly[i] = rectangle.get(i).get(3);
    }    
  }

	
  /**
   * It constructs a diff constraint.
   * @param x list of variables denoting origin of the rectangle in the first dimension.
   * @param y list of variables denoting origin of the rectangle in the second dimension.
   * @param lx list of variables denoting length of the rectangle in the first dimension.
   * @param ly list of variables denoting length of the rectangle in the second dimension.
   */
  public DiffnDecomposed(ArrayList<? extends IntVar> x,
	       ArrayList<? extends IntVar> y,
	       ArrayList<? extends IntVar> lx,
	       ArrayList<? extends IntVar> ly) {

    this(x.toArray(new IntVar[x.size()]), 
	 y.toArray(new IntVar[y.size()]), 
	 lx.toArray(new IntVar[lx.size()]), 
	 ly.toArray(new IntVar[ly.size()]));
  }  

  /**
   * It gives the id string of a constraint.
   * @return string id of the constraint.
   */
  String id() {
    return this.getClass().getSimpleName() + idNumber;
  }

  /**
   * It imposes DiffnDecomposed in a given store.
   * @param store the constraint store to which the constraint is imposed to.
   */
  public void imposeDecomposition(Store store) {

    if (constraints == null)
      decompose(store);

    for (Constraint c : constraints) 
      store.impose(c, queueIndex);
    
  }

  public ArrayList<Constraint> decompose(Store store) {
    constraints = new ArrayList<Constraint>();

    constraints.add(new org.jacop.constraints.diffn.Nooverlap(x, y, lx, ly));
    
    // add cumulative in x direction
    IntVar[] ey = new IntVar[y.length];
    int yMin = IntDomain.MaxInt, yMax = IntDomain.MinInt;
    for (int i = 0; i < x.length; i++) {
      yMin = Math.min(yMin, y[i].min());
      yMax = Math.max(yMax, y[i].max()+ly[i].max());
      ey[i] = new IntVar(store, y[i].min()+ly[i].min(), y[i].max()+ly[i].max());
      constraints.add(new XplusYeqZ(y[i], ly[i], ey[i]));
      auxVar.add(ey[i]);
    }

    IntVar byMin = new IntVar(store, yMin, yMax);
    IntVar byMax = new IntVar(store, yMin, yMax);
    IntVar by = new IntVar(store, 0, yMax - yMin);
    auxVar.add(byMin);
    auxVar.add(byMax);
    auxVar.add(by);
    constraints.add(new Max(ey, byMax));
    constraints.add(new Min(y, byMin));
    constraints.add(new XplusYeqZ(byMin, by, byMax));
    CumulativeBasic ccx = new CumulativeBasic(x, lx, ly, by);
    constraints.add(ccx);

    // add cumulative in y direction
    IntVar[] ex = new IntVar[x.length];
    int xMin = IntDomain.MaxInt, xMax = IntDomain.MinInt;
    for (int i = 0; i < x.length; i++) {
      xMin = Math.min(xMin, x[i].min());
      xMax = Math.max(xMax, x[i].max()+lx[i].max());
      ex[i] = new IntVar(store, x[i].min()+lx[i].min(), x[i].max()+lx[i].max());
      constraints.add(new XplusYeqZ(x[i], lx[i], ex[i]));
      auxVar.add(ex[i]);
    }

    IntVar bxMin = new IntVar(store, "bxMin", xMin, xMax);
    IntVar bxMax = new IntVar(store, "bxMax", xMin, xMax);
    IntVar bx = new IntVar(store, 0, xMax - xMin);
    auxVar.add(bxMin);
    auxVar.add(bxMax);
    auxVar.add(bx);
    constraints.add(new Max(ex, bxMax));
    constraints.add(new Min(x, bxMin));    
    constraints.add(new XplusYeqZ(bxMin, bx, bxMax));
    CumulativeBasic ccy = new CumulativeBasic(y, ly, lx, bx);
    constraints.add(ccy);

    return constraints;
  }
	
  public ArrayList<Var> auxiliaryVariables() {
    return auxVar;
  }

  @Override
  public String toString() {

    StringBuffer result = new StringBuffer( id() );
		
    result.append(" : DiffnDecomposed(");

    for (int i = 0; i < x.length; i++) {
      result.append("[");
      result.append(x[i]);
      result.append(y[i]);
      result.append(lx[i]);
      result.append(ly[i]);
      result.append("]");
      if (i < x.length - 1)
	result.append(", ");
    }
    return result.append(")").toString();
  }
}
