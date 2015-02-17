/**
 *  SimpleMatrixSelect.java 
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

package org.jacop.search;

import java.util.ArrayList;
import java.util.IdentityHashMap;

import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.Var;

/**
 * SimpleMatrixSelect selects first a row in the matrix based on metric of the 
 * variable at pivotPosition. As soon as a row is choosen, variables starting
 * from the beginning of the row which are not assigned yet are selected.  
 * The row selection is done with the help of variable comparators. Two comparators
 * can be employed main and tiebreaking one. If two are not sufficient to differentiate
 * two rows than the lexigraphical ordering is used. 
 * 
 * Default values: pivotPosition = 0,
 * mainComparator = InputOrder, tieBreakingComparator = InputOrder.
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 * @param <T> type of variable being used in the Search.
 */

public class SimpleMatrixSelect<T extends Var> implements SelectChoicePoint<T> {

	///@todo implement subListSize functionality or remove it from the description.
	static final boolean debugAll = false;

	/**
	 * It decides if input order tiebreaking is used. If input tiebreaking 
	 * is not used than the current arrangement of row, variables within rows
	 * decides on the priority. The arrangement of the rows, variables within 
	 * rows depends on the search history. Setting it to false makes the
	 * final tiebreaking a mixture of input-order/search history influenced 
	 * tie breaking. It is faster to compute tiebreaking and it may give 
	 * interesting search history based tiebreaking.
	 */
	public boolean inputOrderTieBreaking = true;

	ComparatorVariable<T> mainComparator = null;

	/**
	 * It specifies the pivot position (first element has index 0).
	 */
	public int pivotPosition;

//	int subListSize;

	ComparatorVariable<T> tieBreakingComparator = null;

	int primaryIndex = 0;

	int secondaryIndex = 0;

	Indomain<T> valueOrdering;

	/**
	 * It stores the original positions of variables to be used for input order
	 * tie-breaking.
	 */

	public IdentityHashMap<T, Integer> position = new IdentityHashMap<T, Integer>();

	/**
	 * It stores variables which need to be labelled.
	 */
	public ArrayList<ArrayList<T>> searchVariables = new ArrayList<ArrayList<T>>();

	/**
	 * This constructor uses default values for all parameters. The size of the
	 * sublist is equal to two. The pivot position points to the first element.
	 * The tiebreaking delete used is DeleteMostConstrainedStatic.
	 * @param vars variables to choose from.
	 * @param indomain value ordering heuristic used to choose a value for a given variable.
	 */

	public SimpleMatrixSelect(T[][] vars, Indomain<T> indomain) {
		this(vars, null, null, indomain, 0);
	}

	/**
	 * It constructs a MatrixSelection variable ordering.
	 * @param vars matrix of variables to be selected from.
	 * @param mainComparator the variable comparator to choose the proper vector.
	 * @param indomain variable ordering value to be used to determine value for a given variable.
	 */
	public SimpleMatrixSelect(T[][] vars,
							  ComparatorVariable<T> mainComparator, 
							  Indomain<T> indomain) {
		this(vars, mainComparator, null, indomain, 0);
	}

	/**
	 * It constructs a MatrixSelection variable ordering.
	 * @param vars matrix of variables to be selected from.
	 * @param mainComparator the variable comparator to choose the proper vector.
	 * @param tieBreakingComparator the variable comparator used if the main comparator can not distinguish between vectors.
	 * @param indomain variable ordering value to be used to determine value for a given variable.
	 */
	public SimpleMatrixSelect(T[][] vars,
			ComparatorVariable<T> mainComparator,
			ComparatorVariable<T> tieBreakingComparator, Indomain<T> indomain) {
		this(vars, mainComparator, tieBreakingComparator, indomain, 0);
	}
	
	/**
	 * This constructor allows to specify all parameters for the selection mechanism. Specifying
	 * mainComparator or tieBreaking to value null do not use that functionality of the selection 
	 * mechanims.
	 * @param vars variables from which the base of the choice point is choosen.
	 * @param mainComparator the main variable comparator used to compare variables.
	 * @param tieBreakingComparator the secondary variable comparator used to break ties.
	 * @param indomain the value ordering heuristic used to assign value to a chosen variable.
	 * @param pivotPosition the position of the variable which is used to rank the rows.
	 */

	public SimpleMatrixSelect(T[][] vars,
			ComparatorVariable<T> mainComparator,
			ComparatorVariable<T> tieBreakingComparator, 
			Indomain<T> indomain,
			int pivotPosition) {

		assert (pivotPosition >= 0) : "Pivot position must be equal or greater 0";
		
		this.mainComparator = mainComparator;
		this.tieBreakingComparator = tieBreakingComparator;
		this.pivotPosition = pivotPosition;
		valueOrdering = indomain;

		int no = 0;

		for (int i = 0; i < vars.length; i++) {

			ArrayList<T> current = new ArrayList<T>();

			assert (vars[i].length > pivotPosition);

			for (int j = 0; j < vars[i].length; j++) {
				current.add(vars[i][j]);
				if (!position.containsKey(vars[i][j]))
					position.put(vars[i][j], no++);
			}

			searchVariables.add(current);
		}

	}

	/**
	 * It returns the variable which is the base on the next choice point. Only
	 * if choice is of an X = C type. This function returns null if all
	 * variables have a value assigned or a choice point based on other type of
	 * constraint is being selected. The parameter index is the last value which
	 * have been return by this SelectChoicePoint object which has not been
	 * backtracked upon yet.
	 */

	//@todo is this specialtiebreaking (lexdynamic actually employed)?
			
	public T getChoiceVariable(int firstVariable) {

		assert (searchVariables.size() > firstVariable) : "The position of the first entity to check is larger than the array size";
		
		int finalIndex = searchVariables.size();

		/// Input order if no main comparator.
		if (mainComparator == null) {

			while (firstVariable < finalIndex) {

				ArrayList<T> row = searchVariables.get(firstVariable);
				
				for (int i = 0; i < row.size(); i++)
					if (!row.get(i).singleton()) {
						primaryIndex = firstVariable;
						secondaryIndex = i;
						return row.get(i);
					}

				firstVariable++;
			}

			return null;
		}

		T currentVariable = searchVariables.get(firstVariable).get(
				pivotPosition);

		// make sure that firstVariable points at row which contains not only singletons.
		if (currentVariable.singleton()) {
			
			while (firstVariable < finalIndex) {
				
				ArrayList<T> row = searchVariables.get(firstVariable);
				
				boolean allGrounded = true;
				
				for (int i = row.size() - 1; i >= 0 && allGrounded; i--)
					if (!row.get(i).singleton())
						allGrounded = false;
				
				if (allGrounded) {
					
					firstVariable++;
					
					if (firstVariable == finalIndex) {
						return null;
					}
					
					currentVariable = searchVariables.get(firstVariable).get(
							pivotPosition);
					
					if (!currentVariable.singleton()) {
						break;
					}
					
				} else {
					// row does not consists of singletons only, pivotVariable is a singleton.
					break;
				}
			}
		}

		float optimalMetric = mainComparator.metric(currentVariable);
		int optimalPosition = firstVariable;

		int comparison = 0;

		T v = null;

		for (int currentPosition = firstVariable + 1; currentPosition < finalIndex; currentPosition++) {

			v = searchVariables.get(currentPosition).get(pivotPosition);

			// if later some singletons rows are encountered they are moved to the left (firstVariable position).
			if (v.singleton()) {
				
				ArrayList<T> row = searchVariables.get(currentPosition);
				
				boolean allGrounded = true;
				
				for (int i = row.size() - 1; i >= 0 && allGrounded; i--)
					if (!row.get(i).singleton())
						allGrounded = false;
						
				if (allGrounded) {
					// switch rows.
					searchVariables.set(currentPosition, searchVariables
							.get(firstVariable));
					searchVariables.set(firstVariable, row);
					if (optimalPosition == firstVariable)
						optimalPosition = currentPosition;
					firstVariable++;
					// work with next row, that one was composed of singletons only.
					continue;
				} 
			}

			// row contains not only singletons, even is variable at pivot position is a singleton.
			
			comparison = mainComparator.compare(optimalMetric, v);

			if (comparison < 0) {
				optimalPosition = currentPosition;
				optimalMetric = mainComparator.metric(v);
			} else {
				
				if (comparison == 0)
					
					if (tieBreakingComparator != null) {

						int comp = tieBreakingComparator.compare(
									searchVariables.get(optimalPosition).get(
											pivotPosition), v);

						if (comp < 0)
							optimalPosition = currentPosition;
						else if (comp == 0 && inputOrderTieBreaking) {
							// Employs input order tie breaking

							int position1 = position.get(searchVariables.get(
									optimalPosition).get(pivotPosition));
							int position2 = position.get(searchVariables.get(
									currentPosition).get(pivotPosition));

							if (position2 < position1) {
								optimalPosition = currentPosition;
								// Variable with currentPosition had a smaller
								// initial position within search variables
							}
						}
					} else {

						// If not InputOrderTieBreaking then dynamicLex as
						// specified by search object is used

						if (inputOrderTieBreaking) {
							// Employs input order tie breaking
							int position1 = position.get(searchVariables.get(
									optimalPosition).get(pivotPosition));
							int position2 = position.get(searchVariables.get(
									currentPosition).get(pivotPosition));

							if (position2 < position1) {
								optimalPosition = currentPosition;
								// Variable with currentPosition had a smaller
								// initial position within search variables
							}
						}

					}
			}

		}

		if (optimalPosition != firstVariable) {
			ArrayList<T> row = searchVariables.get(optimalPosition);
			// switch rows.
			searchVariables.set(optimalPosition, searchVariables
					.get(firstVariable));
			searchVariables.set(firstVariable, row);
			optimalPosition = firstVariable;
		}

		primaryIndex = optimalPosition;
		ArrayList<T> row = searchVariables.get(primaryIndex);
		for (int i = 0; i < row.size(); i++)
			if (!row.get(i).singleton()) {
				secondaryIndex = i;
				break;
			}
		
		return searchVariables.get(primaryIndex).get(secondaryIndex);

	}

	/**
	 * It returns a value which is the base of the next choice point. Only if
	 * choice is of an X = C type.
	 */

	public int getChoiceValue() {

		assert (primaryIndex >= 0);
		assert (primaryIndex < searchVariables.size());

		return valueOrdering.indomain(searchVariables.get(primaryIndex).get(
				secondaryIndex));

	}

	/**
	 * It always returns null as choice point is obtained by getChoiceVariable
	 * and getChoiceValue.
	 */

	public PrimitiveConstraint getChoiceConstraint(int index) {

		return null;

	}

	/**
	 * It returns the variables for which assignment in the solution is given.
	 */

	public IdentityHashMap<T, Integer> getVariablesMapping() {

		return position;

	}

	/**
	 * It returns the current index. Supplying this value in the next invocation
	 * of select will make search for next variable faster without comprimising
	 * efficiency.
	 */

	public int getIndex() {
		return primaryIndex;
	}

	/**
	 * It returns the position of the pivot variable.
	 * @return the position of the pivot variable.
	 */
	public int getPivotPosition() {
		return pivotPosition;
	}

	/**
	 * It uses cheap method of breaking the ties. It is based on input
	 * order influenced by the search history.
	 */
	public void setDynamicLexTieBreaking() {
		inputOrderTieBreaking = false;
	}

	/**
	 * It chooses input order tiebreaking if the supplied comparators 
	 * can not distinguish between matrix rows.
	 */
	public void setInputOrderTieBreaking() {
		inputOrderTieBreaking = true;
	}


	public String toString() {
	    return ""+searchVariables+"\n";
	}
}
