/**
 *  InternalConstraint.java 
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
package org.jacop.constraints.geost;

import java.util.Collection;

import org.jacop.core.Var;

/**
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 *
 * This interface defines the functionality required by a constraint in order
 * to be used by Geost's sweeping algorithm.
 * 
 * The different methods defined by this interface are likely to be called
 * often during a single call to the consistency function, and should therefore 
 * be as efficient as possible.
 * 
 * Comments about implementation details. 
 * 
 * 
 */

public abstract class InternalConstraint {
	
	/**
	 * The ordering of constraints requires to maintain a reverse mapping.
	 */
	int constraintListIndex;
	
	/**
	 * In order to avoid the cost of repeated calls to isInternalConstraintApplicable,
	 * we need 3 different states.
	 * 
	 */
	enum Applicability {
		UNDEFINED, // no check done yet
		APPLICABLE, // check done, constraint applicable
		NOT_APPLICABLE, //check done, constraint not applicable	
	}
	
	/**
	 * the current applicability of the constraint.
	 */
	Applicability applicability;
	
	/**
	 * It provides the largest or smallest point contained in the forbidden area represented by this
	 * constraint. This point must be larger or equal (resp. smaller or equal) to the lexicographically
	 * largest (resp. smallest) point included in the forbidden area, whatever the lexical order is. 
	 * 
	 * TODO, is this function potentially still useful? If not remove, if yes then adapt the description about 
	 * event point series. What is it used now for? I will keep it as it may be used later on, but for sure 
	 * the code implementing those functions is not tested much or requires some cleaning.
	 * 
	 * This allows to build an event point series that stays consistent whatever the lexical order is,
	 * and whatever the object to place is (some shifting is applied to take the object's shape into
	 * account)
	 * 
	 * The dimension of the point returned is k+1, where k is the object dimension. The
	 * last dimension is time.
	 * 
	 * @param minlex defines whether the maximal or minimal point should be returned
	 * @return the infeasible point's coordinates. If constraint cannot generate outbox then it returns null.
	 */
	public abstract int[] AbsInfeasible(Geost.SweepDirection minlex);
	
	
	/**
	 * It provides information about the constraint future. If a constraint will always generate the same
	 * outboxes deeper in the tree, it should return false, so that jumps in the event point series
	 * can be done.
	 * 
	 * TODO the description above suggests that it should be called isDynamic as it returns false if the 
	 * constraint outboxes stay the same. 
	 * 
	 * (not taking placed object into account; i.e. absInfeasible will always return the same points) 
	 * 
	 * @return TODO, proper description after fixing the above todo. 
	 */
	public abstract boolean isStatic();
	
	/**
	 * In some cases, a constraint is used only once per sweep direction on a path
	 * from root to leaf in the search tree. In that case, the constraint can be ignored if
	 * it was seen at some point.
	 * 
	 * TODO, what is the example of such constraint?
	 * 
	 * Use this function to provide the information to Geost.
	 * 
	 * @return TODO. Is this function used at all? It seems that all implementations return false and nowhere in geost it is used.
	 */
	public abstract boolean isSingleUse();
	
	/**
	 * It determines whether the given point is a feasible origin of object o, considering
	 * this constraint only. If it is not, returns a DBox corresponding to the largest infeasible domain,
	 * considering a sweep which uses the given ordering.
	 * 
	 * The boundaries of the forbidden area must have the following properties:
	 * the lower extremum has to be infeasible, but the upper extremum has to be feasible
	 * (with respect to this constraint only).
	 * 
	 * The dimension of the DBox returned is k+1, where k is the object dimension. The
	 * last dimension is time.
	 * 
	 * @param min the direction of the sweep
	 * @param order the order to be used
	 * @param o the object the constraint is applied to
	 * @param currentShape the shape id that is currently considered for o
	 * @param c the current position of the sweep.
	 * @return a DBox representing the forbidden region
	 */
	public abstract DBox isFeasible(Geost.SweepDirection min, 
									LexicographicalOrder order, 
									GeostObject o, 
									int currentShape, 
									int[] c);

	/**
	 * It provides an approximation of the number of infeasible points enforced by this constraint only.
	 * The information provided by this function cannot be accurate, since no object is passed as an argument,
	 * but some consistent approximation should exist. For instance, in the case of a forbidden area,
	 * the returned value can be the number of points included in the area.
	 * 
	 * This information is used as a heuristic in the sweeping algorithm to decide which constraint to use, 
	 * so that the constraints that cover the largest space are used first.
	 * 
	 * @return an approximation of the number of infeasible points enforced by this constraint only.
	 */
	public abstract int cardInfeasible();
	
	/**
	 * It provides a collection, possibly empty, of variables which define this constraint. This information
	 * is used to build a reverse index that allows to update the absolute infeasible points of a constraint
	 * when a variable changes.
	 * 
	 * @return the collection containing variables that define that constraint.
	 */
	public abstract Collection<Var> definingVariables();
}
