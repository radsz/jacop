/**
 *  OperationConstraints.java 
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
package org.jacop.fz.constraints;

import org.jacop.fz.*;

import org.jacop.core.Store;
import org.jacop.core.IntVar;

import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.XmulYeqZ;
import org.jacop.constraints.XmulYeqC;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.AndBoolSimple;
import org.jacop.constraints.XdivYeqZ;
import org.jacop.constraints.XmodYeqZ;
import org.jacop.constraints.MinSimple;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.MaxSimple;
import org.jacop.constraints.AbsXeqY;
import org.jacop.constraints.XexpYeqZ;
import org.jacop.floats.constraints.XeqP;

import org.jacop.satwrapper.SatTranslation;

/**
 * 
 * Generation of linear constraints in flatzinc
 * 
 * @author Krzysztof Kuchcinski 
 *
 */
class OperationConstraints extends Support implements ParserTreeConstants {

    public OperationConstraints(Store store, Tables d, SatTranslation sat) {
    super(store, d, sat);
  }

  static void gen_int_min(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

    IntVar v1 = getVariable(p1);
    IntVar v2 = getVariable(p2);
    IntVar v3 = getVariable(p3);

    if (  v1.singleton() && v2.singleton() ) {
      int min = java.lang.Math.min(v1.value(), v2.value());
      v3.domain.in(store.level, v3, min, min);
    }
    else if (v1.singleton() && v1.value() <= v2.min() ) {
      int min = v1.value();
      v3.domain.in(store.level, v3, min, min);
    }
    else if (v2.singleton() && v2.value() <= v1.min() ) {
      int min = v2.value();
      v3.domain.in(store.level, v3, min, min);
    } 
    else if (v1.min() >= v2.max() )
      pose(new XeqY(v2, v3));
    else if (v2.min() >= v1.max() )
      pose(new XeqY(v1, v3));
    else if (v1 == v2)
      pose(new XeqY(v1, v3));
    else
      pose(new MinSimple(v1, v2, v3));
  }

  static void gen_int_max(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

    IntVar v1 = getVariable(p1);
    IntVar v2 = getVariable(p2);
    IntVar v3 = getVariable(p3);

    if (  v1.singleton() && v2.singleton() ) {
      int max = java.lang.Math.max(v1.value(), v2.value());
      v3.domain.in(store.level, v3, max, max);
    }
    else if (v1.singleton() && v1.value() >= v2.max() ) {
      int max = v1.value();
      v3.domain.in(store.level, v3, max, max);
    }
    else if (v2.singleton() && v2.value() >= v1.max() ) {
      int max = v2.value();
      v3.domain.in(store.level, v3, max, max);
    } 
    else if (v1.min() >= v2.max() )
      pose(new XeqY(v1, v3));
    else if (v2.min() >= v1.max() )
      pose(new XeqY(v2, v3));
    else if (v1 == v2)
      pose(new XeqY(v1, v3));
    else
      pose(new MaxSimple(v1, v2, v3));
  }

  static void gen_int_mod(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

    IntVar v1 = getVariable(p1);
    IntVar v2 = getVariable(p2);
    IntVar v3 = getVariable(p3);

    pose(new XmodYeqZ(v1, v2, v3));
  }

  static void gen_int_div(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

    IntVar v1 = getVariable(p1);
    IntVar v2 = getVariable(p2);
    IntVar v3 = getVariable(p3);

    pose(new XdivYeqZ(v1, v2, v3));
  }

  static void gen_int_abs(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

    IntVar v1 = getVariable(p1);
    IntVar v2 = getVariable(p2);

    if (boundsConsistency)
      pose(new AbsXeqY(v1, v2));
    else
      pose(new AbsXeqY(v1, v2, true));
  }

  static void gen_int_times(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

    if (p1.getType() == 0) {// p1 int
      int c = getInt(p1);
      if (c == 1)
	pose(new XeqY(getVariable(p2), getVariable(p3)));
      else
	pose(new XmulCeqZ(getVariable(p2), c, getVariable(p3)));
    }
    else if (p2.getType() == 0) {// p2 int
      int c = getInt(p2);
      if (c == 1)
	pose(new XeqY(getVariable(p1), getVariable(p3)));
      else
	pose(new XmulCeqZ(getVariable(p1), getInt(p2), getVariable(p3)));
    }
    else if (p3.getType() == 0) {// p3 int
      pose(new XmulYeqC(getVariable(p1), getVariable(p2), getInt(p3)));
    }
    else {
      IntVar v1 = getVariable(p1), v2 = getVariable(p2), v3 = getVariable(p3);
      if (v1.min() >= 0 && v1.max() <= 1 && v2.min() >= 0 && v2.max() <= 1 && v3.min() >= 0 && v3.max() <= 1) 
	pose(new AndBoolSimple(v1, v2, v3));
      else if ( (v1.singleton() && v1.value() == 0) || (v2.singleton() && v2.value() == 0))
	v3.domain.in(store.level, v3, 0,0);
      else
	pose(new XmulYeqZ(v1, v2, v3));
    }
  }

  static void gen_int_plus(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

    if (p1.getType() == 0) {// p1 int
      pose(new XplusCeqZ(getVariable(p2), getInt(p1), getVariable(p3)));
    }
    else if (p2.getType() == 0) {// p2 int
      pose(new XplusCeqZ(getVariable(p1), getInt(p2), getVariable(p3)));
    }
    else if (p3.getType() == 0) {// p3 int
      pose(new XplusYeqC(getVariable(p1), getVariable(p2), getInt(p3)));
    }
    else
      pose(new XplusYeqZ(getVariable(p1), getVariable(p2), getVariable(p3)));
  }

  static void gen_int2float(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

    pose(new XeqP(getVariable(p1), getFloatVariable(p2)));
  }

  static void gen_int_pow(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);

    IntVar v1 = getVariable(p1);
    IntVar v2 = getVariable(p2);
    IntVar v3 = getVariable(p3);

    pose(new XexpYeqZ(v1, v2, v3));
  }
}
