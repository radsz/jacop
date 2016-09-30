/**
 *  CumulativeUnary.java 
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

import org.jacop.constraints.Constraint;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.core.IntDomain;
import java.util.Set;
import java.util.LinkedHashSet;

/**
 * CumulativeUnary implements the scheduling constraint for unary resources using
 *
 * overload, not-first-not-last and detectable algorithms based on 
 *
 * Petr Vilim, "O(n log n) Filtering Algorithms for Unary Resource Constraints", Proceedings of
 * CP-AI-OR 2004,
 *
 * 
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */

public class CumulativeUnary extends Cumulative {

  static final boolean debug = false;

  boolean doProfile = false;
  
  /**
   * It creates a cumulative constraint.
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   */
  public CumulativeUnary(IntVar[] starts,
			 IntVar[] durations,
			 IntVar[] resources,
			 IntVar limit) {

    super(starts, durations, resources, limit);
    queueIndex = 1;
  }
  
  /**
   * It creates a cumulative constraint.
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   * @param doProfile defines whether to do profile-based propagation (true) or not (false); default is false
   */
  public CumulativeUnary(IntVar[] starts,
			 IntVar[] durations,
			 IntVar[] resources,
			 IntVar limit,
			 boolean doProfile) {

    super(starts, durations, resources, limit);
    this.doProfile = doProfile;
  }
  
  /**
   * It creates a cumulative constraint.
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   */
  public CumulativeUnary(ArrayList<? extends IntVar> starts,
			 ArrayList<? extends IntVar> durations, 
			 ArrayList<? extends IntVar> resources,
			 IntVar limit) {

    this(starts.toArray(new IntVar[starts.size()]), 
	 durations.toArray(new IntVar[durations.size()]), 
	 resources.toArray(new IntVar[resources.size()]),
	 limit);		
  }

  /**
   * It creates a cumulative constraint.
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   * @param doProfile defines whether to do profile-based propagation (true) or not (false); default is false
   */
  public CumulativeUnary(ArrayList<? extends IntVar> starts,
			 ArrayList<? extends IntVar> durations, 
			 ArrayList<? extends IntVar> resources,
			 IntVar limit,
			 boolean doProfile) {

    this(starts.toArray(new IntVar[starts.size()]), 
	 durations.toArray(new IntVar[durations.size()]), 
	 resources.toArray(new IntVar[resources.size()]),
	 limit, doProfile);
  }

  @Override
  public void consistency(Store store) {
    
    TaskView[] tn = nonZeros(taskNormal);
    if (tn == null)
      return;
    TaskView[] tr = nonZeros(taskReversed);

    do {

      store.propagationHasOccurred = false;

      if (doProfile)
	profileProp();
      else
	overload(tn);

      detectable(tn, tr);
      notFirstNotLast(tn, tr);
      edgeFind(tn, tr);
      
    } while (store.propagationHasOccurred);
  }

  TaskView[] nonZeros(TaskView[] ts) {
     
    ArrayList<TaskView> nonZeroTasks = new ArrayList<TaskView>();
    for (int i = 0; i < ts.length; i++) 
      if (ts[i].res.min() != 0)
	nonZeroTasks.add(ts[i]);
    int l = nonZeroTasks.size();
    if (l == 0)
      return null;
    TaskView[] t = new TaskView[l];
    System.arraycopy(nonZeroTasks.toArray(new TaskView[l]), 0, t, 0, l);
    return t;
  }
  
  void overload(TaskView[] ts) {

    TaskView[] t = new TaskView[ts.length];
    System.arraycopy(ts, 0, t, 0, ts.length);
    // tasks sorted in ascending order of EST for Theta tree
    Arrays.sort(t, new TaskIncESTComparator<TaskView>());

    ThetaTree tree = new ThetaTree();
    tree.initTree(t);
    //tree.printTree("tree_init");

    // tasks sorted in ascending order of lct
    Arrays.sort(t, new TaskIncLCTComparator<TaskView>());
    
    for (int i = 0; i < t.length; i++) {
      tree.enableNode(t[i].treeIndex);
      if (tree.get(tree.root()).ect > t[i].lct())
	throw store.failException;
    }
  }  

  void notFirstNotLast(TaskView[] tn, TaskView[] tr) {

    notFirstNotLastPhase(tn, taskNormal);
    notFirstNotLastPhase(tr, taskReversed);

  }
  
  void notFirstNotLastPhase(TaskView[] tc, TaskView[] ts) {

    TaskView[] t = new TaskView[tc.length];
    System.arraycopy(tc, 0, t, 0, tc.length);
    // tasks sorted in ascending order of EST for Theta tree
    Arrays.sort(t, new TaskIncESTComparator<TaskView>());

    ThetaTree tree = new ThetaTree();
    tree.initTree(t);
    // tree.printTree("tree_init");
    
    // tasks sorted in ascending order of lct
    Arrays.sort(t, new TaskIncLCTComparator<TaskView>());

    // tasks sorted in ascending order of lct - p (lst)
    TaskView[] q = new TaskView[t.length];
    System.arraycopy(t, 0, q, 0, t.length);
    Arrays.sort(q, new TaskIncLSTComparator<TaskView>());
    
    notLast(tree, t, q, ts);
  }

  void notLast(ThetaTree tree, TaskView[] t, TaskView[] q, TaskView[] to) {

    int n = t.length;    
    int[] updateLCT = new int[n];
    for (int i = 0; i < n; i++)
      updateLCT[i] = t[i].lct();

    int indexQ = 0;
    for (int i = 0; i < n; i++) {
      int j = -1;

      while (indexQ < n && t[i].lct() > q[indexQ].lst()) {
	
        if (tree.ect(t[i].treeIndex) > t[i].lst())
	  updateLCT[i] = Math.min(q[indexQ-1].lst(), updateLCT[i]);

	j = to[q[indexQ].index].treeIndex;
	tree.enableNode(j);
	indexQ++;
      }

      if (j >= 0 && tree.ect(t[i].treeIndex) > t[i].lst()) {
	updateLCT[i] = Math.min(q[indexQ-1].lst(), updateLCT[i]);
	// updateLCT[i] = Math.min(to[tree.get(j).task.index].lst(), updateLCT[i]);
      }
    }
    
    for (int i = 0; i < n; i++) {
      t[i].updateNotFirstNotLast(updateLCT[i]);
    }
  }


  void detectable(TaskView[] tn, TaskView[] tr) {
    detectablePhase(tn, taskNormal);
    detectablePhase(tr, taskReversed);
  }
  

  void detectablePhase(TaskView[] tc, TaskView[] ts) {

    TaskView[] t = new TaskView[tc.length];
    System.arraycopy(tc, 0, t, 0, tc.length);
    // tasks sorted in ascending order of EST for Theta tree
    Arrays.sort(t, new TaskIncESTComparator<TaskView>());

    ThetaTree tree = new ThetaTree();
    tree.initTree(t);
    // tree.printTree("tree_init");
    
    // tasks sorted in ascending order of lct
    Arrays.sort(t, new TaskIncECTComparator<TaskView>());

    // tasks sorted in ascending order of lct - p (lst)
    TaskView[] q = new TaskView[t.length];
    System.arraycopy(t, 0, q, 0, t.length);
    Arrays.sort(q, new TaskIncLSTComparator<TaskView>());
    
    detectable(tree, t, q, ts);

  }

  void detectable(ThetaTree tree, TaskView[] t, TaskView[] q, TaskView[] to) {

    int n = t.length;    
    int[] updateEST = new int[n];

    int indexQ = 0;
    for (int i = 0; i < n; i++) {
      int j = -1;

      while (indexQ < n && t[i].ect() > q[indexQ].lst()) {
	j = to[q[indexQ].index].treeIndex;
	tree.enableNode(j);
	indexQ++;
      }
      updateEST[i] = tree.ect(t[i].treeIndex);
    }

    for (int i = 0; i < n; i++) {
      t[i].updateDetectable(updateEST[i]);
    }
    
  }

  void edgeFind(TaskView[] tn, TaskView[] tr) {

    edgeFindPhase(tn, taskNormal);
    edgeFindPhase(tr, taskReversed);

  }

  void edgeFindPhase(TaskView[] tc, TaskView[] tn) {

    // tasks sorted in non-decreasing order of est
    TaskView[] estList = new TaskView[tc.length];
    System.arraycopy(tc, 0, estList, 0, tc.length);
    Arrays.sort(estList, new TaskIncESTComparator<TaskView>());

    ThetaLambdaUnaryTree tree = new ThetaLambdaUnaryTree();
    tree.buildTree(estList);
    
    // tasks sorted in non-increasing order of lct
    TaskView[] lctList = new TaskView[estList.length];
    System.arraycopy(estList, 0, lctList, 0, estList.length);
    Arrays.sort(lctList, new TaskDecLCTComparator<TaskView>());    

    int n = lctList.length;
    TaskView t = lctList[0];
    for ( int i=0; i < n-1; i++) {
      if (tree.ect() > t.lct())
        throw store.failException;

      tree.moveToLambda(t.treeIndex);
      t = lctList[i+1];
      
      while (tree.ectLambda() > t.lct()) {	
        int j = tree.rootNode().responsibleEctLambda;
    	tn[tree.get(j).task.index].updateEdgeFind(tree.ect());
        tree.removeFromLambda(j);
      }
    }
  }

  
  @Override
  public String toString() {

    StringBuffer result = new StringBuffer( id() );

    result.append(" : cumulativeUnary([ ");
    for (int i = 0; i < taskNormal.length - 1; i++)
      result.append(taskNormal[i]).append(", ");

    result.append(taskNormal[taskNormal.length - 1]);

    result.append(" ]").append(", limit = ").append(limit).append(" )");

    return result.toString();

  }

  class TaskIncLCTComparator<T extends TaskView> implements Comparator<T> {

    TaskIncLCTComparator() {
    }

    public int compare(T o1, T o2) {
      return (o1.lct() == o2.lct()) ? (o1.est() - o2.est()) : (o1.lct() - o2.lct()); 
    }
  }

  class TaskIncLSTComparator<T extends TaskView> implements Comparator<T> {

    TaskIncLSTComparator() {
    }

    public int compare(T o1, T o2) {
      return (o1.lst() == o2.lst()) ? (o1.est() - o2.est()) : (o1.lst() - o2.lst()); 
    }
  }

  class TaskIncECTComparator<T extends TaskView> implements Comparator<T> {

    TaskIncECTComparator() {
    }

    public int compare(T o1, T o2) {
      return (o1.ect() == o2.ect()) ? (o1.est() - o2.est()) : (o1.ect() - o2.ect());
    }
  }


}

