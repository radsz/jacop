/**
 *  Cumulative.java 
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


package org.jacop.constraints.cumulative;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.lang.Integer;

import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.core.IntDomain;
import java.util.Set;
import java.util.LinkedHashSet;

/**
 * Cumulative implements the scheduling constraint using 
 *
 * edge-finding algorithms based on 
 *
 * Petr Vilim, "Edge Finding Filtering Algorithm for Discrete Cumulative Resources in O(kn log n)",
 * Principles and Practice of Constraint Programming - CP 2009 Volume 5732 of the series Lecture
 * Notes in Computer Science pp 802-816.
 *
 * and 
 *
 * Joseph Scott, "Filtering Algorithms for Discrete Cumulative Resources", MSc thesis, Uppsala
 * University, Department of Information Technology, 2010, no IT 10 048,
 * @see <a href="http://urn.kb.se/resolve?urn=urn:nbn:se:uu:diva-132172">http://urn.kb.se/resolve?urn=urn:nbn:se:uu:diva-132172</a>
 * 
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

public class Cumulative extends CumulativeBasic {

  static final boolean debug = false;

  TaskView[] taskReversed;
  
  /**
   * It creates a cumulative constraint.
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   */
  public Cumulative(IntVar[] starts,
		    IntVar[] durations,
		    IntVar[] resources,
		    IntVar limit) {

    super(starts, durations, resources, limit);

    taskReversed = new TaskReversedView[starts.length];
    for (int i = 0; i < starts.length; i++) 
      taskReversed[i] = new TaskReversedView(new Task(starts[i], durations[i], resources[i]));

    for (int i = 0; i < starts.length; i++) {
      taskReversed[i].index = i;
    }
    
    // check for possible overflows
    if (limit != null)
      for (Task t : taskNormal) {
	mul((t.start.max()+t.dur.max()), limit.max());
      }
  }

  /**
   * It creates a cumulative constraint.
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   */
  public Cumulative(ArrayList<? extends IntVar> starts,
		    ArrayList<? extends IntVar> durations, 
		    ArrayList<? extends IntVar> resources,
		    IntVar limit) {

    this(starts.toArray(new IntVar[starts.size()]), 
	 durations.toArray(new IntVar[durations.size()]), 
	 resources.toArray(new IntVar[resources.size()]),
	 limit);
		
  }

  @Override
  public void impose(Store store) {

    super.impose(store);
    for (Task t : taskNormal) {
      t.store = store;
    }
    for (Task t : taskReversed) {
      t.store = store;
    }
  }

  @Override
  public void consistency(Store store) {

    do {

      store.propagationHasOccurred = false;

      profileProp();
      
      if (store.propagationHasOccurred == false)
	edgeFind();
      
    } while (store.propagationHasOccurred);
  }

  /*
  void overloadCheck() {

    TaskView[] estList = new TaskNormalView[taskNormal.length];
    System.arraycopy(taskNormal, 0, estList, 0, estList.length);
    Arrays.sort(estList, new TaskIncESTComparator<TaskView>());
    // System.out.println(java.util.Arrays.asList(estList));

    ThetaLambdaTree tree = new ThetaLambdaTree(limit);
    tree.buildTree(estList);
    tree.clearTree();

    TaskView[] lctList = new TaskNormalView[taskNormal.length];
    for (int i = 0; i < taskNormal.length; i++)
      lctList[i] = new TaskNormalView(taskNormal[i]);
    Arrays.sort(lctList, new TaskIncLCTComparator<TaskView>());
    System.out.println(java.util.Arrays.asList(lctList));

    
    int C = limit.max();
    for (int j = 0; j < lctList.length; j++) {
      tree.enableNode(lctList[j].treeIndex, lctList[j].res.min());

      // System.out.println("j = " + j +", lctList[j].treeIndex = "+lctList[j].treeIndex+", tree.rootNode().env "+ tree.rootNode().env +", lctList[j].lct() = " + lctList[j].lct() + ", C = "+ C);

      if (tree.rootNode().env > C * lctList[j].lct()) {
  	// System.out.println("FAIL");

      	throw store.failException;
      }
    }
  }
  */

  void edgeFind() {

    edgeFind(taskNormal);
    edgeFind(taskReversed);

  }

  void edgeFind(TaskView[] tn) {

    // tasks sorted in non-decreasing order of est
    TaskView[] estList = filterZeroTasks(tn); // new TaskView[taskNormal.length];
    // System.arraycopy(tn, 0, estList, 0, estList.length);
    if (estList == null)
      return;

    Arrays.sort(estList, new TaskIncESTComparator<TaskView>());

    ThetaLambdaTree tree = new ThetaLambdaTree(limit);
    tree.buildTree(estList);

    // tasks sorted in non-increasing order of lct
    TaskView[] lctList = new TaskView[estList.length];
    System.arraycopy(estList, 0, lctList, 0, estList.length);
    Arrays.sort(lctList, new TaskDecLCTComparator<TaskView>());    

    int[] auxOrderListInv = new int[lctList.length];
    for (int i = 0; i < lctList.length; i++) {
      auxOrderListInv[lctList[i].index] = i;
    }
    
    // ========== Detect Order ============
    int[] prec = detectOrder(tree, lctList, auxOrderListInv, limit.max());
    // System.out.println("*** prec = " + intArrayToString(prec));

    // write ThetaLambdaTree as dot file for visualization
    // tree.printTree("tree_init");
    
    // ========== Adjust Bounds ============
    adjustBounds(tree, lctList, prec, limit.max());

  }

  int[] detectOrder(ThetaLambdaTree tree, TaskView[] t, int[] lctInvOrder, int C) {

    int n = t.length;
    int[] prec = new int[n];
    for (int i = 0; i < n; i++) 
      prec[t[i].index] = t[i].ect(); // originally Integer.MIN_VALUE; can be changed to this

    for (int j = 0; j < n; j++) {
      if (tree.rootNode().env > C * t[j].lct()) {
      	throw store.failException;
      }

      while (tree.rootNode().envLambda > C * t[j].lct()) {
    	int i = tree.rootNode().responsibleEnvLambda;
    	prec[tree.get(i).task.index] = Math.max(prec[tree.get(i).task.index], t[j].lct());
    	tree.removeFromLambda(i);
      }
      tree.moveToLambda(t[j].treeIndex);
    }

    int[] lctPrec = new int[prec.length];
    for (int i = 0; i < prec.length; i++) {
      lctPrec[lctInvOrder[i]] = prec[i];
    }

    return lctPrec;
  }

  void adjustBounds(ThetaLambdaTree tree, TaskView[] t, int[] prec, int cap) {

    int n = t.length;
    Set<Integer> capacities = new LinkedHashSet<Integer>();
    for (int i = 0; i < n; i++) {
      capacities.add(t[i].res.min());
    }

    // System.out.println("capacities = " + capacities);
    
    int[] capMap = new int[n];
    int capIndex = 0;
    for (int ci : capacities) {
      for (int i = 0; i < n; i++) {
      	if (t[i].res.min() == ci)
      	  capMap[t[i].index] = capIndex;
      }
      capIndex++;
    }

    int[][] update = new int[capacities.size()][n];
    
    int capi=0;
    for (int ci : capacities) {
      
      tree.clearTree();

      int upd = Integer.MIN_VALUE;

      for (int l = n-1; l >= 0; l--) { // by non-decreasing of lct
		  
	tree.enableNode(t[l].treeIndex, ci);
	// tree.printTree("tree_task_"+t[l].index);

	int envlc = tree.calcEnvlc(t[l].lct(), ci);
	int diff;
	if (envlc == Integer.MIN_VALUE) {
	  diff = Integer.MIN_VALUE;
	}
	else {
	  long tmp = envlc - (cap -ci)*t[l].lct();
	  diff = (int)( Math.round( Math.ceil((double)tmp/(double)ci)));
	}	
	upd = Math.max(upd, diff);
	update[capi][l] = upd;
      }
      capi++;
    }
    
    Integer[] precTaskOrder = new Integer[n];
    for (int i = n-1; i >= 0; i--)
      precTaskOrder[i] = i; 
    Arrays.sort(precTaskOrder, new PrecComparator<Integer>(prec));

    int j = 0;
    outer: for (int i = 0; i < n; i++) {

      TaskView taskI = t[precTaskOrder[i]];
      int precI = prec[precTaskOrder[i]];
      
      // first skip all task j that are lct after prec
      
      if (taskI.res.min() == 0) continue;

      while (j < n && t[j].lct() > precI) {
        j++;
      }
      if (j < n) {

	// update est[i] if possible
	int nj = j;
	inner: while (nj < n && t[nj].lct() == precI)  {
	  if (t[nj].lct() < taskI.lct()) {
	    taskI.updateEdgeFind(update[capMap[taskI.index]][nj]);
	    break inner;
	  }
	  nj++;
	}
      }
      else
	break outer;
    }
  }

  TaskView[] filterZeroTasks(TaskView[] ts) {
     
    ArrayList<TaskView> nonZeroTasks = new ArrayList<TaskView>();
    int k = 0;
    for (int i = 0; i < ts.length; i++) 
      if (ts[i].res.min() != 0 && ts[i].dur.min() != 0) {
	nonZeroTasks.add(ts[i]);
	ts[i].index = k++;
      }
    int l = nonZeroTasks.size();
    if (l == 0)
      return null;
    TaskView[] t = new TaskView[l];
    System.arraycopy(nonZeroTasks.toArray(new TaskView[l]), 0, t, 0, l);
    return t;
  }
  

  
  @Override
  public boolean satisfied() {

    Task T;
    boolean sat = true;

    // expensive checking
    if (limit.singleton()) {
      int i = 0;
      while (sat && i < taskNormal.length) {
	T = taskNormal[i];
	i++;
	sat = sat && T.start.singleton() && T.dur.singleton()
	  && T.res.singleton();
      }
      return sat;
    } else
      return false;
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
  
  @Override
  public String toString() {

    StringBuffer result = new StringBuffer( id() );

    result.append(" : cumulative([ ");
    for (int i = 0; i < taskNormal.length - 1; i++)
      result.append(taskNormal[i]).append(", ");

    result.append(taskNormal[taskNormal.length - 1]);

    result.append(" ]").append(", limit = ").append(limit).append(" )");

    return result.toString();

  }

  class TaskIncESTComparator<T extends TaskView> implements Comparator<T> {

    TaskIncESTComparator() {
    }

    public int compare(T o1, T o2) {
      return (o1.est() == o2.est()) ? (o1.lct() - o2.lct()) : (o1.est() - o2.est());
    }
  }

  class TaskDecLCTComparator<T extends TaskView> implements Comparator<T> {

    TaskDecLCTComparator() {
    }

    public int compare(T o1, T o2) {
      return (o2.lct() == o1.lct()) ? (o2.est() - o1.est()) : (o2.lct() - o1.lct()); 
    }
  }

  class PrecComparator<T extends Integer> implements Comparator<T> {
    int[] prec;
    
    PrecComparator(int[] prec) {
      this.prec = prec;
    }

    public int compare(T o1, T o2) {
      return (prec[o2.intValue()] - prec[o1.intValue()]);
    }
  }

}
