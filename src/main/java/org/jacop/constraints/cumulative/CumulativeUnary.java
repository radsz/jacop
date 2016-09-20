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

  /**
   * It creates a cumulative constraint.
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   * @param doEdgeFinding true if edge finding algorithm should be used.
   * @param doProfile specifies if the profiles should be computed in order to reduce limit variable.
   */
  public CumulativeUnary(IntVar[] starts,
			 IntVar[] durations,
			 IntVar[] resources,
			 IntVar limit) {

    super(starts, durations, resources, limit);
    super.setLimit = false;
    
    if (limit.max() > 1)
      throw new IllegalArgumentException( "\nCumulativeUnary constraint assumes  limit == 1 and found " + limit);
  }
  
  public CumulativeUnary(IntVar[] starts,
			 IntVar[] durations,
			 IntVar[] resources,
			 IntVar limit,
			 boolean doProfile,
			 boolean setLimit) {
    
    this(starts, durations, resources, limit);
    super.doProfile = doProfile;
    super.setLimit = setLimit;
  }

  
  public CumulativeUnary(IntVar[] starts,
			 IntVar[] durations,
			 IntVar[] resources,
			 IntVar limit,
			 boolean doProfile) {
    
    this(starts, durations, resources, limit);
    super.doProfile = doProfile;
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

  @Override
  public void consistency(Store store) {

    do {

      store.propagationHasOccurred = false;

      if (doProfile)
	profileProp();

      overload(taskNormal);
      notFirstNotLast();
      edgeFind();
      detectable();
      
    } while (store.propagationHasOccurred);
  }

  void overload(TaskView[] ts) {
    ArrayList<TaskView> nonZeroTasks = new ArrayList<TaskView>();
    for (int i = 0; i < ts.length; i++) 
      if (ts[i].res.min() != 0)
	nonZeroTasks.add(ts[i]);
    if (nonZeroTasks.size() == 0)
      return;
    
    TaskView[] t = new TaskView[nonZeroTasks.size()];
    System.arraycopy(nonZeroTasks.toArray(new TaskView[nonZeroTasks.size()]), 0, t, 0, nonZeroTasks.size());
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

  void notFirstNotLast() {

    notFirstNotLast(taskNormal);
    notFirstNotLast(taskReversed);

  }
  
  void notFirstNotLast(TaskView[] ts) {
    ArrayList<TaskView> nonZeroTasks = new ArrayList<TaskView>();
    for (int i = 0; i < ts.length; i++) 
      if (ts[i].res.min() != 0)
	nonZeroTasks.add(ts[i]);
    if (nonZeroTasks.size() == 0)
      return;
    
    TaskView[] t = new TaskView[nonZeroTasks.size()];
    System.arraycopy(nonZeroTasks.toArray(new TaskView[nonZeroTasks.size()]), 0, t, 0, nonZeroTasks.size());
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
    
    notLast(tree, t, q);
  }

  void notLast(ThetaTree tree, TaskView[] t, TaskView[] q) {

    int n = t.length;
    int[] taskToTreeMap = new int[taskNormal.length];
    for (int i = 0; i < n; i++) {
      taskToTreeMap[t[i].index] = t[i].treeIndex;
    }
    
    int[] updateLCT = new int[n];
    for (int i = 0; i < n; i++)
      updateLCT[i] = t[i].lct();

    int indexQ = 0;
    for (int i = 0; i < n; i++) {
      int j = -1;

      while (indexQ < n && t[i].lct() > q[indexQ].lst()) { //q[indexQ].lct() - q[indexQ].dur.max()) {
	
        if (indexQ >= 0 && tree.ect(t[i].treeIndex) > t[i].lst())
	  updateLCT[i] = Math.min(q[indexQ-1].lst(), updateLCT[i]);

	j = taskToTreeMap[q[indexQ].index];

	tree.enableNode(j);

	indexQ++;
      }

      if (indexQ > 0 && tree.ect(t[i].treeIndex) > t[i].lst()) {
	updateLCT[i] = Math.min(q[indexQ-1].lst(), updateLCT[i]);
      }
    }
    
    for (int i = 0; i < n; i++) {
      t[i].updateNotFirstNotLast(updateLCT[i]);
    }
  }


  void detectable() {
    detectable(taskNormal);
    detectable(taskReversed);
  }
  

  void detectable(TaskView[] ts) {
    
    ArrayList<TaskView> nonZeroTasks = new ArrayList<TaskView>();
    for (int i = 0; i < ts.length; i++) 
      if (ts[i].res.min() != 0)
	nonZeroTasks.add(ts[i]);
    if (nonZeroTasks.size() == 0)
      return;
    
    TaskView[] t = new TaskView[nonZeroTasks.size()];
    System.arraycopy(nonZeroTasks.toArray(new TaskView[nonZeroTasks.size()]), 0, t, 0, nonZeroTasks.size());
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
    
    detectable(tree, t, q);

  }

  void detectable(ThetaTree tree, TaskView[] t, TaskView[]q) {

    int n = t.length;
    int[] taskToTreeMap = new int[taskNormal.length];
    for (int i = 0; i < n; i++) {
      taskToTreeMap[t[i].index] = t[i].treeIndex;
    }
    
    int[] updateEST = new int[n];

    int indexQ = 0;
    for (int i = 0; i < n; i++) {
      int j = -1;

      while (indexQ < n && t[i].ect() > q[indexQ].lst()) {
	
	j = taskToTreeMap[q[indexQ].index];

	tree.enableNode(j);

	indexQ++;
      }
      updateEST[i] = Math.max(t[i].est(), tree.ect(t[i].treeIndex));
    }

    // System.out.println("updateEST = " + intArrayToString(updateEST));

    for (int i = 0; i < n; i++) {
      t[i].updateDetectable(updateEST[i]);
    }
    
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

