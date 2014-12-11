/**
 *  ExtensionalSupportMDD.java 
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
import org.jacop.core.TimeStamp;
import org.jacop.core.Var;
import org.jacop.util.IndexDomainView;
import org.jacop.util.MDD;
import org.jacop.util.SparseSet;


/**
 * Extensional constraint assures that one of the tuples is enforced in the
 * relation.
 * 
 * This implementation uses technique developed/improved by Roland Yap and his student.
 * Paper presented at CP2008. We would like to thank Roland for answering our detailed
 * questions about the implementation. It is a slightly improved version to what was
 * presented at the conference.
 * 
 * This constraint uses a lot of memory, despite using an MDD. However, if the constraint
 * is imposed multiple times (50+) its overall usage of memory maybe advantageous. Always
 * test against STR version.
 * 
 * @author Radoslaw Szymanek
 * @version 2.3
 */

public class ExtensionalSupportMDD extends Constraint {

	/**
	 * It specifies if the debugging information is printed.
	 */
	public static final boolean debugAll = false;

	static int IdNumber = 1;

	TimeStamp<Integer> G_no_size;

	SparseSet G_no;

	/**
	 * It specifies a multiple value decision diagram used by this constraint. 
	 */
	public MDD mdd;

	SparseSet G_yes;

	IndexDomainView [] views;

	// Only temporary for storing table of tuples.
	int[][] table;
	IntVar[] vars;

	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"mdd"};

	/**
	 * It creates an extensional constraint.
	 * @param diagram multiple-valued decision diagram describing allowed tuples.
	 */
	public ExtensionalSupportMDD(MDD diagram) {

		queueIndex = 1;

		this.mdd = diagram;
		this.views = diagram.views;

		G_no = new SparseSet(diagram.freePosition);

		numberId = IdNumber++;

	}

	@Override
	public void impose(Store store) {

		if (this.mdd == null) {
			this.mdd = new MDD(vars, table);
			this.views = mdd.views;

			this.G_no = new SparseSet(mdd.freePosition);
			this.table = null;
			this.vars = null;
		}

		store.registerRemoveLevelListener(this);

		for (int i = 0; i < mdd.vars.length; i++)
			mdd.vars[i].putConstraint(this);

		this.G_no_size = new TimeStamp<Integer>(store, 0);

		store.addChanged(this);
		store.countConstraint();

		store.raiseLevelBeforeConsistency = true;

		if (mdd.freePosition > store.sparseSetSize)
			store.sparseSetSize = mdd.freePosition;

	} 

	/**
	 * It constructs extensional support constraint. Please note
	 * that parameters will be stored internally as references
	 * until the impose of the constraint takes place. 
	 * Changing parameters after constructing the constraint and 
	 * before its imposition will change the constraint too. 
	 *
	 * @param vars the variables in the scope of the constraint.
	 * @param table list of tuples which are allowed.
	 */
	public ExtensionalSupportMDD(IntVar [] vars, int [][] table) {

		queueIndex = 1;

		this.table = table;
		this.vars = vars;

		numberId = IdNumber++;

	}



	// data structures to support for a given variable
	// signaling what value index is supported.

	@Override
	public void consistency(Store s) {

		G_yes = s.sparseSet;

		G_yes.clear();

		G_no.setSize(G_no_size.value());

		//TODO initialize notSupportedIndexesYes to 0..domainLimits	
		for (int i = 0; i < views.length; i++)
			views[i].intializeSupportSweep();

		seekSupport(0, 0);

		for (int i = 0; i < views.length; i++)
			views[i].removeUnSupportedValues(s);

		G_no_size.update(G_no.members);

	}

	/**
	 * It checks if the node at a given level of MDD has a support.
	 * @param nodeId the position of the node in the MDD.
	 * @param level number of variable associated with the node.
	 * @return true if node is supported by current domains of variables.
	 */
	public boolean seekSupport(int nodeId, int level) {

		if (G_yes.isMember(nodeId))
			return true;

		if (G_no.isMember(nodeId))
			return false;


		boolean result = false;

		// optimization possible if variable level-th did not change

		for (int i = 0; i < mdd.domainLimits[level] ; i++) {
			int shift = nodeId + i;
			if (mdd.diagram[shift] != MDD.NOEDGE)
				if ( views[level].contains( i ) )
					if (mdd.diagram[shift] == MDD.TERMINAL ||
							seekSupport(mdd.diagram[shift], level+1)) {

						// ith-value has a support
						// returns true is new support was found
						// it always checks the preliminary finish condition 
						// at least once if new support was found.
						if (!views[level].setSupport(i) || !result) {

							result = true;

							//TODO check if allIndexesSupported needs updating
							// if it needs updating check the break condition below.
							// break if for all following levels variables
							// have all values been signaled as already supported
							// notSupportYet is empty for all variables level..vars.length

							int j = level;
							for (;j < views.length && views[j].isSupported(); j++);
							if (j == views.length)
								break;

						}

					}
		}

		if (result) 
			G_yes.addMember(nodeId);
		else
			G_no.addMember(nodeId);

		return result;

	}

	@Override
	public int getConsistencyPruningEvent(Var var) {
		//		 If consistency function mode
		if (consistencyPruningEvents != null) {
			Integer possibleEvent = consistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		return IntDomain.ANY;
	}

	@Override
	public ArrayList<Var> arguments() {
		ArrayList<Var> result = new ArrayList<Var>();

		for (Var v : mdd.vars)
			result.add(v);

		return result;
	}


	@Override
	public void increaseWeight() {
		for (Var v : mdd.vars)
			v.weight++;
	}

	@Override
	public void removeConstraint() {
		for (Var var : mdd.vars)
			var.removeConstraint(this);
	}


	@Override
	public boolean satisfied() {
		return mdd.checkIfAllowed();
	}


	@Override
	public String toString() {

		StringBuffer result = new StringBuffer(id());

		result.append(" : extensionalSupportMDD( ");

		for (int i = 0; i < mdd.vars.length; i++)
			result.append( mdd.vars[i] ).append(" ");

		result.append(")").append("size = ").append( mdd.freePosition).append(")\n");

		return result.toString();
	}

}
