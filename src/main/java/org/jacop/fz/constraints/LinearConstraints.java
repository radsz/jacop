/**
 *  LinearConstraints.java 
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

import org.jacop.core.Store;
import org.jacop.core.IntVar;

import org.jacop.fz.*;

import org.jacop.constraints.Reified;
import org.jacop.constraints.SumBool;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.LinearInt;
import org.jacop.constraints.LinearIntDom;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.XplusClteqZ;
import org.jacop.constraints.XplusYeqZ;
import org.jacop.constraints.XplusYeqC;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XplusYlteqZ;
import org.jacop.constraints.Not;
import org.jacop.constraints.OrBoolVector;
  
import org.jacop.satwrapper.SatTranslation;
import org.jacop.core.FailException;

/**
 * 
 * Generation of linear constraints in flatzinc
 * 
 * @author Krzysztof Kuchcinski 
 *
 */
class LinearConstraints extends Support implements ParserTreeConstants {

  public LinearConstraints(Store store, Tables d, SatTranslation sat) {
    super(store, d, sat);
  }

  static void gen_bool_lin_eq(SimpleNode node) {

    int[] p1 = getIntArray((SimpleNode)node.jjtGetChild(0));
    IntVar[] p2 = getVarArray((SimpleNode)node.jjtGetChild(1));
    IntVar par3 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

    // If a linear term contains only constants and can be evaluated 
    // check if satisfied and do not generate constraint
    if (par3.min() == par3.max() && allConstants(p2)) {
      int el=0, s=0;
      while (el < p2.length) {
	s += p2[el].min()*p1[el];
	el++;
      }
      if (s == par3.min())
	return;
      else
	throw store.failException;
    }

    if (allWeightsOne(p1))
      pose(new SumBool(store, p2, "==", par3));
    else {
      store.impose(new LinearInt(store, p2, p1, "==", par3));
    }
  }

  static void gen_int_lin_eq(SimpleNode node) {
    int_lin_relation(eq, node);
  }

  static void gen_int_lin_eq_reif(SimpleNode node) {
    int_lin_relation_reif(eq, node);
  }

  static void gen_int_lin_ne(SimpleNode node) {
    int_lin_relation(ne, node);
  }

  static void gen_int_lin_ne_reif(SimpleNode node) {
    int_lin_relation_reif(ne, node);
  }

  static void gen_int_lin_lt(SimpleNode node) {
    int_lin_relation(lt, node);
  }

  static void gen_int_lin_lt_reif(SimpleNode node) {
    int_lin_relation_reif(lt, node);
  }

  static void gen_int_lin_le(SimpleNode node) {
    int_lin_relation(le, node);
  }

  static void gen_int_lin_le_reif(SimpleNode node) {
    int_lin_relation_reif(le, node);
  }

  static void int_lin_relation_reif(int operation, SimpleNode node) throws FailException {

    int[] p1 = getIntArray((SimpleNode)node.jjtGetChild(0));
    IntVar[] p2 = getVarArray((SimpleNode)node.jjtGetChild(1));
    int p3 = getInt((ASTScalarFlatExpr)node.jjtGetChild(2));

    // If a linear term contains only constants and can be evaluated 
    // check if satisfied and do not generate constraint
    boolean p2Fixed = allConstants(p2);
    int s=0;
    if (p2Fixed) {
      int el=0;
      while (el < p2.length) {
	s += p2[el].min()*p1[el];
	el++;
      }
    }

    IntVar p4 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(3));

    IntVar t;
    switch (operation) {
    case eq :

      if (p2Fixed) {
	if (s == p3)
	  p4.domain.in(store.level, p4, 1, 1);
	else
	  p4.domain.in(store.level, p4, 0, 0);
	return;
      }
		
      if (p1.length == 1) {
	if (p1[0] == 1)
	  pose(new Reified(new XeqC(p2[0], p3), p4));
	else
	  pose(new Reified(new XmulCeqZ(p2[0], p1[0], dictionary.getConstant(p3)), p4));
      }
      else if (p1.length == 2 && p1[0] == 1 && p1[1] == -1) {
	pose(new Reified(new XplusCeqZ(p2[1], p3, p2[0]), p4));
      }
      else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1) {
	pose(new Reified(new XplusCeqZ(p2[0], p3, p2[1]), p4));
      } 
      else if (p1.length == 2 && p1[0] == 1 && p1[1] == 1) {
	pose(new Reified(new XplusYeqC(p2[0], p2[1], p3), p4));
      } 
      else if (p1.length == 2 && p1[0] == -1 && p1[1] == -1) {
	pose(new Reified(new XplusYeqC(p2[0], p2[1], -p3), p4));
      } 
      else {
	int pos = sumPossible(p1, p3);
	if (pos > -1) {
	  IntVar[] vect = new IntVar[p1.length-1];
	  int n = 0;
	  for (int i=0; i<p2.length; i++)
	    if (i != pos)
	      vect[n++] = p2[i];
	  if (boolSum(vect))
	    pose(new Reified(new SumBool(store, vect, "==", p2[pos]), p4));
	  else
	    pose(new Reified(new SumInt(store, vect, "==", p2[pos]), p4));
	} else
	  if (allWeightsOne(p1)) {
	    IntVar v = dictionary.getConstant(p3);
	    if (boolSum(p2))
	      pose(new Reified(new SumBool(store, p2, "==", v), p4));
	    else
	      pose(new Reified(new SumInt(store, p2, "==", v), p4));
	  }
	  else if (allWeightsMinusOne(p1)) {
	    IntVar v = dictionary.getConstant(-p3);
	    if (boolSum(p2))
	      pose(new Reified(new SumBool(store, p2, "==", v), p4));
	    else
	      pose(new Reified(new SumInt(store, p2, "==", v), p4));
	  } else {
	    pose(new Reified(new LinearInt(store, p2, p1, "==", p3), p4));
	  }
      }
      break;
    case ne :
      if (p1.length == 2 && p1[0] == 1 && p1[1] == -1) {
	if (p3 == 0)
	  pose(new Reified(new XneqY(p2[0], p2[1]), p4));
	else
	  pose(new Reified(new Not(new XplusCeqZ(p2[1], p3, p2[0])), p4));
      }
      else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1) {
	if (p3 == 0)
	  pose(new Reified(new XneqY(p2[0], p2[1]), p4));
	else
	  pose(new Reified(new Not(new XplusCeqZ(p2[0], p3, p2[1])), p4));
      } 
      else if (p1.length == 2 && p1[0] == 1 && p1[1] == 1) {
	pose(new Reified(new Not(new XplusYeqC(p2[0], p2[1], p3)), p4));
      } 
      else if (p1.length == 2 && p1[0] == -1 && p1[1] == -1) {
	pose(new Reified(new Not(new XplusYeqC(p2[0], p2[1], -p3)), p4));
      } 
      else if (allWeightsOne(p1)) {
	if (p1.length == 1)
	  if (p2[0].domain.isIntersecting(p3,p3))
	    pose(new Reified(new XneqC(p2[0], p3), p4));
	  else
	    p4.domain.in(store.level, p4, 1,1);
	else {
	  t = dictionary.getConstant(p3); // new IntVar(store, p3, p3);
	  if (boolSum(p2))
	    pose(new Reified(new SumBool(store, p2, "!=", t), p4));
	  else
	    pose(new Reified(new SumInt(store, p2, "!=", t), p4));
	}
      }
      else if (allWeightsMinusOne(p1)) {
	if (p1.length == 1) 
	  if (p2[0].domain.isIntersecting(-p3,-p3))
	    pose(new Reified(new XneqC(p2[0], -p3), p4));
	  else
	    p4.domain.in(store.level, p4, 1,1);
	else {
	  t = dictionary.getConstant(-p3); // new IntVar(store, -p3, -p3);
	  if (boolSum(p2))
	    pose(new Reified(new SumBool(store, p2, "!=", t), p4));
	  else
	    pose(new Reified(new SumInt(store, p2, "!=", t), p4));
	}
      }
      else 
	pose(new Reified(new LinearInt(store, p2, p1, "!=", p3), p4));
      break;
    case lt :
      pose(new Reified(new LinearInt(store, p2, p1, "<", p3), p4));
      break;
      // gt not present in the newest flatzinc version
      // case gt :
      // 	t = new IntVar(store, IntDomain.MinInt, IntDomain.MaxInt);
      // 	pose(new SumWeight(p2, p1, t));
      // 	pose(new Reified(new XgtC(t, p3), p4));
      // 	break;
    case le :
      if (p1.length == 2 && p1[0] == 1 && p1[1] == -1)
	if (p3 == 0)
	  pose(new Reified(new org.jacop.constraints.XlteqY(p2[0], p2[1]), p4));
	else
	  pose(new Reified(new org.jacop.constraints.XplusClteqZ(p2[0], -p3, p2[1]), p4));
      else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1)
	if (p3 == 0)
	  pose(new Reified(new org.jacop.constraints.XlteqY(p2[1], p2[0]), p4));
	else
	  pose(new Reified(new org.jacop.constraints.XplusClteqZ(p2[1], -p3, p2[0]), p4));
      else if (p1.length == 1 && p1[0] == 1) 
	pose(new Reified(new org.jacop.constraints.XlteqC(p2[0], p3), p4));
      else if (p1.length == 1 && p1[0] == -1) 
	pose(new Reified(new org.jacop.constraints.XgteqC(p2[0], -p3), p4));
      else if (allWeightsOne(p1)) {
	t = dictionary.getConstant(p3); //new IntVar(store, p3, p3);
	if (boolSum(p2))
	  if (p3 == 0) 
	    // all p2's zero <=> p4
	    if (Options.useSat())
	      sat.generate_allZero_reif(unique(p2), p4);
	    else
	      pose(new Not(new OrBoolVector(p2, p4)));
	  else
	    pose(new Reified(new SumBool(store, p2, "<=", t), p4));
	else
	  pose(new Reified(new SumInt(store, p2, "<=", t), p4));
      }
      else if (allWeightsMinusOne(p1)) {
	t = dictionary.getConstant(-p3); //new IntVar(store, -p3, -p3);
	if (boolSum(p2))
	  pose(new Reified(new SumBool(store, p2, ">=", t), p4));
	else
	  pose(new Reified(new SumInt(store, p2, ">=", t), p4));		    
      }
      else {
	int posLe = sumLePossible(p1, p3);
	int posGe = sumGePossible(p1, p3);
	if (posLe > -1) {
	  IntVar[] vect = new IntVar[p1.length-1];
	  int n = 0;
	  for (int i=0; i<p2.length; i++)
	    if (i != posLe)
	      vect[n++] = p2[i];
	  if (boolSum(vect))
	    pose(new Reified(new SumBool(store, vect, "<=", p2[posLe]), p4));
	  else if (vect.length == 2)
	    pose(new Reified(new XplusYlteqZ(vect[0], vect[1], p2[posLe]), p4));
	  else
	    pose(new Reified(new SumInt(store, vect, "<=", p2[posLe]), p4));
	}
	else if (posGe > -1) {
	  IntVar[] vect = new IntVar[p1.length-1];
	  int n = 0;
	  for (int i=0; i<p2.length; i++)
	    if (i != posGe)
	      vect[n++] = p2[i];
	  if (boolSum(vect))
	    pose(new Reified(new SumBool(store, vect, ">=", p2[posGe]), p4));
	  else
	    pose(new Reified(new SumInt(store, vect, ">=", p2[posGe]), p4));
	}
	else {
	  pose(new Reified(new LinearInt(store,p2, p1, "<=", p3), p4));
	}
      }
      break;
    default:
      System.err.println("%% ERROR: Constraint in linear not supported.");
      System.exit(0);
    }
  }

  static void int_lin_relation(int operation, SimpleNode node) throws FailException {

    int[] p1 = getIntArray((SimpleNode)node.jjtGetChild(0));
    IntVar[] p2 = getVarArray((SimpleNode)node.jjtGetChild(1));
    int p3 = getInt((ASTScalarFlatExpr)node.jjtGetChild(2));

    // If a linear term contains only constants and can be evaluated 
    // check if satisfied and do not generate constraint
    boolean p2Fixed = allConstants(p2);
    int s=0;
    if (p2Fixed) {
      int el=0;
      while (el < p2.length) {
	s += p2[el].min()*p1[el];
	el++;
      }
    }

    IntVar t;
    switch (operation) {
    case eq :

      if (p2Fixed)
	if (s == p3)
	  return;
	else
	  throw store.failException;

      if (p1.length == 1) {
	pose(new XmulCeqZ(p2[0], p1[0], dictionary.getConstant(p3))); // new IntVar(store, p3, p3)));
      }
      else if (p1.length == 2 && p1[0] == 1 && p1[1] == -1) {
	if (p3 != 0)
	  pose(new XplusCeqZ(p2[1], p3, p2[0]));
	else
	  pose(new XeqY(p2[1], p2[0]));
      }
      else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1) {
	if (p3 != 0) {
	  pose(new XplusCeqZ(p2[0], p3, p2[1]));
	}
	else
	  pose(new XeqY(p2[0], p2[1]));
      }
      else if (p1.length == 2 && p1[0] == 1 && p1[1] == 1) {
	pose(new XplusYeqC(p2[0], p2[1], p3));
      } 
      else if (p1.length == 2 && p1[0] == -1 && p1[1] == -1) {
	if (p3 == 0)
	  pose(new XplusYeqC(p2[0], p2[1], p3));
	else
	  pose(new XplusYeqC(p2[0], p2[1], -p3));
      }
      else if (domainConsistency && !Options.getBoundConsistency()){// && (maxDomain(p2) <= 4 || p2.length <= 2) ) { // heuristic rule to select domain consistency since 
	// its complexity is O(d^n), d <= 4 or n <= 2 ;)
	// We do not impose linear constraint with domain consistency if 
	// the cases are covered by four cases above.

	pose(new LinearIntDom(store, p2, p1, "==", p3)); //SumWeightDom(p2, p1, p3));
      }
      else if ((p3 == 0 && p1.length == 3)
	       && ((p1[0] == -1 && p1[1] == -1 && p1[2] == 1) || (p1[0] == 1 && p1[1] == 1 && p1[2] == -1)))
	pose(new XplusYeqZ(p2[0], p2[1], p2[2]));
      else if (p3 == 0 && p1.length == 2 && p1[0] == 1) {
	pose(new XmulCeqZ(p2[1], -p1[1], p2[0]));
      }
      else if (p3 == 0 && p1.length == 2 && p1[1] == 1) {
	pose(new XmulCeqZ(p2[0], -p1[0], p2[1]));
      }
      else if ((p3 == 0 && p1.length == 3)
	       && ((p1[0] == 1 && p1[1] == -1 && p1[2] == -1) || (p1[0] == -1 && p1[1] == 1 && p1[2] == 1))) {
	if (paramZero(p2[1]))
	  pose(new XeqY(p2[2], p2[0]));
	else if (paramZero(p2[2]))
	  pose(new XeqY(p2[1], p2[0]));
	else
	  pose(new XplusYeqZ(p2[1], p2[2], p2[0]));    
      }
      else {
	int pos = sumPossible(p1, p3);
	if (pos > -1) {
	  IntVar[] vect = new IntVar[p1.length-1];
	  int n = 0;
	  for (int i=0; i<p2.length; i++)
	    if (i != pos)
	      vect[n++] = p2[i];

	  if (boolSum(vect))
	    pose(new SumBool(store, vect, "==", p2[pos]));
	  else
	    if (vect.length == 2)
	      pose(new XplusYeqZ(vect[0], vect[1], p2[pos]));
	    else
	      pose(new SumInt(store, vect, "==", p2[pos]));
	} else
	  if (allWeightsOne(p1)) {
	    IntVar v = dictionary.getConstant(p3);
	    if (boolSum(p2))
	      pose(new SumBool(store, p2, "==", v));
	    else
	      pose(new SumInt(store, p2, "==", v));
	  }
	  else if (allWeightsMinusOne(p1)) {
	    IntVar v = dictionary.getConstant(-p3);
	    if (boolSum(p2))
	      pose(new SumBool(store, p2, "==", v));
	    else
	      pose(new SumInt(store, p2, "==", v));
	  }
	  else {
	    pose(new LinearInt(store, p2, p1, "==", p3));
	  }
      }
      break;
    case ne :

      if (p2Fixed)
	if (s != p3)
	  return;
	else
	  throw store.failException;

      if (p1.length == 1 && p1[0] == 1)
	p2[0].domain.inComplement(store.level, p2[0], p3);
      else if (p1.length == 1 && p1[0] == -1)
	p2[0].domain.inComplement(store.level, p2[0], -p3);
      else if (p1.length == 2 && p3 == 0 && ( (p1[0] == 1 && p1[1] == -1) || (p1[0] == -1 && p1[1] == 1) ))
	if (p2[0].max() < p2[1].min() || p2[0].min() > p2[1].max())
	  return;
	else
	  pose(new XneqY(p2[0], p2[1]));
      else {
	int pos = sumPossible(p1, p3);
	if (pos > -1) {
	  IntVar[] vect = new IntVar[p1.length-1];
	  int n = 0;
	  for (int i=0; i<p2.length; i++)
	    if (i != pos)
	      vect[n++] = p2[i];
	  if (boolSum(vect))
	    pose(new SumBool(store, vect, "!=", p2[pos]));
	  else
	    pose(new SumInt(store, vect, "!=", p2[pos]));
	}
	else {
	  if (boolSum(p2) && allWeightsOne(p1))
	    pose(new SumBool(store, p2, "!=", dictionary.getConstant(p3)));
	  else
	    pose(new LinearInt(store, p2, p1, "!=", p3));
	}
      }
      break;
    case lt :

      if (p2Fixed)
	if (s < p3)
	  return;
	else
	  throw store.failException;

      if (p1.length == 2 && p1[0] == 1 && p1[1] == -1 && p3 == 0)
	pose(new XltY(p2[0], p2[1]));
      else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1 && p3 == 0)
	pose(new XltY(p2[1], p2[0]));
      else {
	int posLe = sumLePossible(p1, p3);
	int posGe = sumGePossible(p1, p3);
	if (posLe > -1) {
	  IntVar[] vect = new IntVar[p1.length-1];
	  int n = 0;
	  for (int i=0; i<p2.length; i++)
	    if (i != posLe)
	      vect[n++] = p2[i];
	  if (boolSum(vect))
	    pose(new SumBool(store, vect, "<", p2[posLe]));
	  else
	    pose(new SumInt(store, vect, "<", p2[posLe]));
	}
	else if (posGe > -1) {
	  IntVar[] vect = new IntVar[p1.length-1];
	  int n = 0;
	  for (int i=0; i<p2.length; i++)
	    if (i != posGe)
	      vect[n++] = p2[i];
	  if (boolSum(vect))
	    pose(new SumBool(store, vect, ">", p2[posGe]));
	  else
	    pose(new SumInt(store, vect, ">", p2[posGe]));
	}
	else {
	  // pose(new Linear(store, p2, p1, "<", p3));
	  pose(new LinearInt(store, p2, p1, "<", p3));
	}
      }
      break;
    case le :

      if (p2Fixed)
	if (s <= p3)
	  return;
	else
	  throw store.failException;

      if (p1.length == 1) {

	if (p1[0] < 0) {
	  int rhsValue = (int)( Math.round( Math.ceil ( ((float)(p3/p1[0])) )));

	  p2[0].domain.inMin(store.level, p2[0], rhsValue);
	  if (debug)
	    System.out.println ("Pruned variable " + p2[0] + " to be >= " + rhsValue);
	  // pose(new XgteqC(p2[0], rhsValue));
	}
	else { // weight > 0
	  int rhsValue = (int)( Math.round( Math.floor ( ((float)(p3/p1[0])) )));

	  p2[0].domain.inMax(store.level, p2[0], rhsValue);

	  if (debug)
	    System.out.println ("Pruned variable " + p2[0] + " to be <= " + rhsValue);
	  // pose(new XlteqC(p2[0], rhsValue));
	}
      }
      else if (p1.length == 2 && p1[0] == 1 && p1[1] == -1 && p3 == 0)
	pose(new XlteqY(p2[0], p2[1]));
      else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1 && p3 == 0)
	pose(new XlteqY(p2[1], p2[0]));
      else if (p1.length == 2 && p1[0] == 1 && p1[1] == -1)
	if (p3 == 0)
	  pose(new XlteqY(p2[0], p2[1]) );
	else
	  pose(new XplusClteqZ(p2[0], -p3, p2[1]) );
      else if (p1.length == 2 && p1[0] == -1 && p1[1] == 1)
	if (p3 == 0)
	  pose(new XlteqY(p2[1], p2[0]) );
	else
	  pose(new XplusClteqZ(p2[1], -p3, p2[0]) );

      else if (allWeightsOne(p1)) {
	t = dictionary.getConstant(p3); //new IntVar(store, p3, p3);
	if (boolSum(p2))
	  pose(new SumBool(store, p2, "<=", t));		    
	else
	  pose(new SumInt(store, p2, "<=", t));		    
      }
      else if (allWeightsMinusOne(p1)) {
	t = dictionary.getConstant(-p3); //new IntVar(store, -p3, -p3);
	if (boolSum(p2))
	  pose(new SumBool(store, p2, ">=", t));
	else
	  pose(new SumInt(store, p2, ">=", t));		    
      }
      else {
	int posLe = sumLePossible(p1, p3);
	int posGe = sumGePossible(p1, p3);
	if (posLe > -1) {
	  IntVar[] vect = new IntVar[p1.length-1];
	  int n = 0;
	  for (int i=0; i<p2.length; i++)
	    if (i != posLe)
	      vect[n++] = p2[i];
	  if (boolSum(vect))
	    pose(new SumBool(store, vect, "<=", p2[posLe]));
	  else if (vect.length == 2)
	    pose(new XplusYlteqZ(vect[0], vect[1], p2[posLe]));
	  else
	    pose(new SumInt(store, vect, "<=", p2[posLe]));
	}
	else if (posGe > -1) {
	  IntVar[] vect = new IntVar[p1.length-1];
	  int n = 0;
	  for (int i=0; i<p2.length; i++)
	    if (i != posGe)
	      vect[n++] = p2[i];
	  if (boolSum(vect))
	    pose(new SumBool(store, vect, ">=", p2[posGe]));
	  else
	    pose(new SumInt(store, vect, ">=", p2[posGe]));
	}
	else {
	  pose(new LinearInt(store, p2, p1, "<=", p3));
	}
      }
      break;
    default:
      System.err.println("%% ERROR: Constraint linear not supported.");
      System.exit(0);
    }
  }

  static boolean allConstants(IntVar[] p) {
    boolean sat = true;
    int k = 0;
    while (sat && k < p.length) {
      sat = (p[k].min() == p[k].max());
      k++;
    }
    return sat;
  }

  static boolean allWeightsOne(int[] w) {
    //boolean allOne=true;
    for (int i=0; i<w.length; i++)
      if (w[i] != 1)
	return false;
    return true;
  }
  
  static boolean allWeightsMinusOne(int[] w) {
    //boolean allOne=true;
    for (int i=0; i<w.length; i++)
      if (w[i] != -1)
	return false;
    return true;
  }

  static boolean boolSum(IntVar[] vs) {
    for (IntVar v : vs) 
      if (v.min() < 0 || v.max() > 1)
	return false;
    return true;
  }  

  static int sumPossible(int[] ws, int result) {
    if (result == 0) {
      int one = 0, minusOne = 0;
      int lastOnePosition = -1, lastMinusOnePosition = -1;
      //boolean sum = true;
      for (int i=0; i<ws.length; i++)
	if (ws[i] == 1) {
	  one++;
	  lastOnePosition = i;
	}
	else if (ws[i] == -1) {
	  minusOne++;
	  lastMinusOnePosition = i;
	}

      if (one == 1 && minusOne == ws.length - 1)
	return lastOnePosition;
      else if (minusOne == 1 && one == ws.length - 1)
	return lastMinusOnePosition;
      else
	return -1;
    }
    else
      return -1;
  }

  static int sumLePossible(int[] ws, int result) {
    if (result == 0) {
      int one = 0, minusOne = 0;
      int lastOnePosition = -1, lastMinusOnePosition = -1;
      //boolean sum = true;
      for (int i=0; i<ws.length; i++)
	if (ws[i] == 1) {
	  one++;
	  lastOnePosition = i;
	}
	else if (ws[i] == -1) {
	  minusOne++;
	  lastMinusOnePosition = i;
	}

      if (minusOne == 1 && one == ws.length - 1)
	return lastMinusOnePosition;
      else
	return -1;
    }
    else
      return -1;
  }

  static int sumGePossible(int[] ws, int result) {
    if (result == 0) {
      int one = 0, minusOne = 0;
      int lastOnePosition = -1, lastMinusOnePosition = -1;
      //boolean sum = true;
      for (int i=0; i<ws.length; i++)
	if (ws[i] == 1) {
	  one++;
	  lastOnePosition = i;
	}
	else if (ws[i] == -1) {
	  minusOne++;
	  lastMinusOnePosition = i;
	}

      if (one == 1 && minusOne == ws.length - 1)
	return lastOnePosition;
      else
	return -1;
    }
    else
      return -1;
  }

  static boolean paramZero(IntVar v) {
    return v.singleton() && v.value() == 0;
  }
}
