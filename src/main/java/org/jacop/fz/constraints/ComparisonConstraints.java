/**
 *  ComparisonConstraints.java 
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

import java.util.ArrayList;

import org.jacop.core.Store;
import org.jacop.core.IntVar;
import org.jacop.core.IntDomain;

import org.jacop.fz.*;

import org.jacop.constraints.Constraint;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XltY;
import org.jacop.constraints.XltC;
import org.jacop.constraints.XeqY;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XneqY;
import org.jacop.constraints.XneqC;
import org.jacop.constraints.Reified;
import org.jacop.constraints.XgtC;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XgtY;
import org.jacop.constraints.XgteqY;
import org.jacop.constraints.XlteqC;

import org.jacop.satwrapper.SatTranslation;


/**
 * 
 * Generation of comparison constraints in flatzinc
 * 
 * @author Krzysztof Kuchcinski 
 *
 */
class ComparisonConstraints extends Support implements ParserTreeConstants {

  static boolean reified;

  public ComparisonConstraints(Store store, Tables d, SatTranslation sat) {
    super(store, d, sat);
  }

  // =========== bool =================
  static void gen_bool_eq(SimpleNode node) {

    if (Options.useSat()) {
      IntVar a = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
      IntVar b = getVariable((ASTScalarFlatExpr)node.jjtGetChild(1));

      sat.generate_eq(a, b);
      return;
    }
    reified = false;
    int_comparison(eq, node);
  }
  
  static void gen_bool_eq_reif(SimpleNode node) {

    if (Options.useSat()) {

      IntVar v1 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
      IntVar v2 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(1));
      IntVar v3 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));
			
      sat.generate_eq_reif(v1, v2, v3);

      return;
    }
    
    reified = true;
    int_comparison(eq, node);
  }
  
  static void gen_bool_ne(SimpleNode node) {
    if (Options.useSat()) {

      IntVar a = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
      IntVar b = getVariable((ASTScalarFlatExpr)node.jjtGetChild(1));
      
      sat.generate_not(a, b);
      return;
    }

    reified = false;
    int_comparison(ne, node);
  }
  
  static void gen_bool_ne_reif(SimpleNode node) {

    if (Options.useSat()) {

      IntVar v1 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
      IntVar v2 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(1));
      IntVar v3 = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));
			
      sat.generate_neq_reif(v1, v2, v3);
      return;
    }
    
    reified = true;
    int_comparison(ne, node);
  }
  
  static void gen_bool_le(SimpleNode node) {

    if (Options.useSat()) {

      IntVar a = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
      IntVar b = getVariable((ASTScalarFlatExpr)node.jjtGetChild(1));

      sat.generate_le(a, b);
      return;
    }
    
    reified = false;
    int_comparison(le, node);
  }
  
  static void gen_bool_le_reif(SimpleNode node) {

    if (Options.useSat()) {

      IntVar a = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
      IntVar b = getVariable((ASTScalarFlatExpr)node.jjtGetChild(1));
      IntVar c = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

      sat.generate_le_reif(a, b, c);
      return;
    }
    
    reified = true;
    int_comparison(le, node);
  }
  
  static void gen_bool_lt(SimpleNode node) {

    if (Options.useSat()) {

      IntVar a = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
      IntVar b = getVariable((ASTScalarFlatExpr)node.jjtGetChild(1));

      sat.generate_lt(a, b);
      return;
    }
    
    reified = false;
    int_comparison(lt, node);
  }
  
  static void gen_bool_lt_reif(SimpleNode node) {

    if (Options.useSat()) {

      IntVar a = getVariable((ASTScalarFlatExpr)node.jjtGetChild(0));
      IntVar b = getVariable((ASTScalarFlatExpr)node.jjtGetChild(1));
      IntVar c = getVariable((ASTScalarFlatExpr)node.jjtGetChild(2));

      sat.generate_lt_reif(a, b, c);
    }
    
    reified = true;
    int_comparison(lt, node);
  }

  // =========== int =================
  static void gen_int_eq(SimpleNode node) {
    reified = false;
    int_comparison(eq, node);
  }
  
  static void gen_int_eq_reif(SimpleNode node) {
    reified = true;
    int_comparison(eq, node);
  }
  
  static void gen_int_ne(SimpleNode node) {
    reified = false;
    int_comparison(ne, node);
  }
  
  static void gen_int_ne_reif(SimpleNode node) {
    reified = true;
    int_comparison(ne, node);
  }
  
  static void gen_int_le(SimpleNode node) {
    reified = false;
    int_comparison(le, node);
  }
  
  static void gen_int_le_reif(SimpleNode node) {
    reified = true;
    int_comparison(le, node);
  }
  
  static void gen_int_lt(SimpleNode node) {
    reified = false;
    int_comparison(lt, node);
  }
  
  static void gen_int_lt_reif(SimpleNode node) {
    reified = true;
    int_comparison(lt, node);
  }
  
  static void int_comparison(int operation, SimpleNode node) {

    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr)node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr)node.jjtGetChild(1);

    if (reified) { // reified constraint
      PrimitiveConstraint c = null;
      ASTScalarFlatExpr p3 = (ASTScalarFlatExpr)node.jjtGetChild(2);
      IntVar v3 = getVariable(p3);

      if (p2.getType() == 0 || p2.getType() == 1) { // var rel int or bool
	IntVar v1 = getVariable(p1);

	int i2 = getInt(p2);
	switch (operation) {

	case eq :
	  if (!v1.domain.contains(i2)) {
	    v3.domain.in(store.level, v3, 0, 0);
	    return;
	  }
	  else if (v1.min() == i2 && v1.singleton() ) {
	    v3.domain.in(store.level, v3, 1, 1);
	    return;
	  } else if (v3.max() == 0) {
	    v1.domain.inComplement(store.level, v1, i2);
	    return;
	  }
	  else if (v3.min() == 1) {
	    v1.domain.in(store.level, v1, i2, i2);
	    return;
	  }
	  else
	    // if (Options.useSat()) {  // it can be moved to SAT solver but it is slow in the current implementation
	    //     sat.generate_eqC_reif(v1, i2, v3);
	    //     return;
	    // }
	    // else
	    c = new XeqC(v1, i2);
	  break;

	case ne :
	  if (v1.min() > i2 || v1.max() < i2) {
	    v3.domain.in(store.level, v3, 1, 1);
	    return;
	  }
	  else if (v1.min() == i2 && v1.singleton() ) {
	    v3.domain.in(store.level, v3, 0, 0);
	    return;
	  } else if (v3.max() == 0) {
	    v1.domain.in(store.level, v1, i2, i2);
	    return;
	  }
	  else if (v3.min() == 1) {
	    v1.domain.inComplement(store.level, v1, i2);
	    return;
	  }
	  else
	    // if (Options.useSat()) {  // it can be moved to SAT solver but it is slow in the current implementation
	    //     sat.generate_neC_reif(v1, i2, v3);
	    //     return;
	    // }
	    // else
	    c = new XneqC(v1, i2);
	  break;
	case lt :
	  if (v1.max() < i2) {
	    v3.domain.in(store.level, v3, 1, 1);
	    return;
	  }
	  else if (v1.min() >= i2 ) {
	    v3.domain.in(store.level, v3, 0, 0);
	    return;
	  }
	  else
	    c = new XltC(v1, i2);
	  break;
	case gt :
	  if (v1.min() > i2) {
	    v3.domain.in(store.level, v3, 1, 1);
	    return;
	  }
	  else if (v1.max() <= i2 ) {
	    v3.domain.in(store.level, v3, 0, 0);
	    return;
	  }
	  else
	    c = new XgtC(v1, i2);
	  break;
	case le :
	  if (v1.max() <= i2) {
	    v3.domain.in(store.level, v3, 1, 1);
	    return;
	  }
	  else if (v1.min() > i2 ) {
	    v3.domain.in(store.level, v3, 0, 0);
	    return;
	  }
	  else
	    c = new XlteqC(v1, i2);
	  break;
	case ge :
	  if (v1.min() >= i2) {
	    v3.domain.in(store.level, v3, 1, 1);
	    return;
	  }
	  else if (v1.max() < i2 ) {
	    v3.domain.in(store.level, v3, 0, 0);
	    return;
	  }
	  else
	    c = new XgteqC(v1, i2);
	  break;
	}
      } else if (p1.getType() == 0 || p1.getType() == 1) { // int rel var or bool
	IntVar v2 = getVariable(p2);
	int i1 = getInt(p1);

	switch (operation) {

	case eq :
	  if (!v2.domain.contains(i1)) { //v2.min() > i1 || v2.max() < i1) {
	    v3.domain.in(store.level, v3, 0, 0);
	    return;
	  }
	  else if (v2.min() == i1 && v2.singleton() ) {
	    v3.domain.in(store.level, v3, 1, 1);
	    return;
	  }
	  else if (v3.max() == 0) {
	    v2.domain.inComplement(store.level, v2, i1);
	    return;
	  }
	  else if (v3.min() == 1) {
	    v2.domain.in(store.level, v2, i1, i1);
	    return;
	  }
	  else
	    c = new XeqC(v2, i1);
	  break;

	case ne :
	  if (v2.min() > i1 || v2.max() < i1) {
	    v3.domain.in(store.level, v3, 1, 1);
	    return;
	  }
	  else if (v2.min() == i1 && v2.singleton() ) {
	    v3.domain.in(store.level, v3, 0, 0);
	    return;
	  }
	  else
	    c = new XneqC(v2, i1);
	  break;
	case lt :
	  if (i1 < v2.min()) {
	    v3.domain.in(store.level, v3, 1, 1);
	    return;
	  }
	  else if (i1 >= v2.max() ) {
	    v3.domain.in(store.level, v3, 0, 0);
	    return;
	  }
	  else
	    c = new XgtC(v2, i1);
	  break;
	case gt :
	  if (i1 > v2.max()) {
	    v3.domain.in(store.level, v3, 1, 1);
	    return;
	  }
	  else if (i1 <= v2.min() ) {
	    v3.domain.in(store.level, v3, 0, 0);
	    return;
	  }
	  else
	    c = new XltC(v2, i1);
	  break;
	case le :
	  if (i1 <= v2.min()) {
	    v3.domain.in(store.level, v3, 1, 1);
	    return;
	  }
	  else if (i1 > v2.max() ) {
	    v3.domain.in(store.level, v3, 0, 0);
	    return;
	  }
	  else
	    // if (Options.useSat()) {  // it can be moved to SAT solver but it is slow in the current implementation
	    //     sat.generate_geC_reif(v2, i1, v3);
	    //     return;
	    // }
	    // else
	    c = new XgteqC(v2, i1);
	  break;
	case ge :
	  if (i1 > v2.max()) {
	    v3.domain.in(store.level, v3, 1, 1);
	    return;
	  }
	  else if (i1 < v2.min() ) {
	    v3.domain.in(store.level, v3, 0, 0);
	    return;
	  }
	  else
	    c = new XlteqC(v2, i1);
	  break;
	}
      } else { // var rel var
	IntVar v1 = getVariable(p1);
	IntVar v2 = getVariable(p2);

	switch (operation) {
	case eq :
	  c = new XeqY(v1, v2);

	  // if (v3.singleton())
	  // 	if (v3.min() == 1) 
	  // 	    if (v1.singleton()) {
	  // 		v2.domain.in(store.level, v2, v1.domain);
	  // 		return;
	  // 	    }
	  // 	    else {
	  // 		pose(c);
	  // 		return;
	  // 	    }
	  // 	else { // v3.max() == 0
	  // 	    if (v1.singleton()) {
	  // 		v2.domain.inComplement(store.level, v2, v1.min());
	  // 		return;
	  // 	    }
	  // 	    else {
	  // 		pose(c);
	  // 		return;
	  // 	    }
	  // 	}

	  break;
	case ne :
	  c = new XneqY(v1, v2);
	  break;
	case lt :
	  c = new XltY(v1, v2);
	  break;
	case gt :
	  c = new XgtY(v1, v2);
	  break;
	case le :
	  c = new XlteqY(v1, v2);
	  break;
	case ge :
	  c = new XgteqY(v1, v2);
	  break;
	}
      }

      Constraint cr = new Reified(c, v3);
      pose(cr);
    }
    else  { // not reified constraints

      if (p1.getType() == 0 || p1.getType() == 1) { // first parameter int or bool
	if (p2.getType() == 0 || p2.getType() == 1) { // first parameter int/bool & second parameter int/bool
	  int i1 = getInt(p1);
	  int i2 = getInt(p2);
	  switch (operation) {
	  case eq :
	    if (i1 != i2) throw Store.failException;
	    break;
	  case ne :
	    if (i1 == i2) throw Store.failException;
	    break;
	  case lt :
	    if (i1 >= i2) throw Store.failException;
	    break;
	  case gt :
	    if (i1 <= i2) throw Store.failException;
	    break;
	  case le :
	    if (i1 > i2) throw Store.failException;
	    break;
	  case ge :
	    if (i1 < i2) throw Store.failException;
	    break;
	  }
	} 
	else { // first parameter int/bool & second parameter var

	  int i1 = getInt(p1);
	  IntVar v2 = getVariable(p2);

	  switch (operation) {
	  case eq :
	    v2.domain.in(store.level, v2, i1, i1);
	    break;
	  case ne :
	    v2.domain.inComplement(store.level, v2, i1);
	    break;
	  case lt :
	    v2.domain.in(store.level, v2, i1+1, IntDomain.MaxInt);
	    break;
	  case gt :
	    v2.domain.in(store.level, v2, IntDomain.MinInt, i1-1);
	    break;
	  case le :
	    v2.domain.in(store.level, v2, i1, IntDomain.MaxInt);
	    break;
	  case ge :
	    v2.domain.in(store.level, v2, IntDomain.MinInt, i1);
	    break;
	  }
	}
      }
      else { // first parameter var
	if (p2.getType() == 0 || p2.getType() == 1) { // first parameter var & second parameter int

	  IntVar v1 = getVariable(p1);
	  int i2 = getInt(p2);

	  switch (operation) {
	  case eq :
	    v1.domain.in(store.level, v1, i2, i2);
	    break;
	  case ne :
	    v1.domain.inComplement(store.level, v1, i2);
	    break;
	  case lt :
	    v1.domain.in(store.level, v1, IntDomain.MinInt, i2-1);
	    break;
	  case gt :
	    v1.domain.in(store.level, v1, i2+1, IntDomain.MaxInt);
	    break;
	  case le :
	    v1.domain.in(store.level, v1, IntDomain.MinInt, i2);
	    break;
	  case ge :
	    v1.domain.in(store.level, v1, i2, IntDomain.MaxInt);
	    break;
	  }

	} 
	else { // first parameter var & second parameter var

	  PrimitiveConstraint c = null;
	  IntVar v1 = getVariable(p1);
	  IntVar v2 = getVariable(p2);

	  switch (operation) {
	  case eq :
	    c = new XeqY(v1, v2);
	    break;
	  case ne :
	    c = new XneqY(v1, v2);
	    break;
	  case lt :
	    c = new XltY(v1, v2);
	    break;
	  case gt :
	    c = new XgtY(v1, v2);
	    break;
	  case le :
	    c = new XlteqY(v1, v2);
	    break;
	  case ge :
	    c = new XgteqY(v1, v2);
	    break;
	  }
	  pose(c);
	}
      }
    }
  }
}
