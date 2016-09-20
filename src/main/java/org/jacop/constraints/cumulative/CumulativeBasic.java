/**
 *  CumulativeBasic.java 
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
import java.util.TreeSet;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.constraints.Constraint;

import org.jacop.constraints.Profile;
import org.jacop.constraints.ProfileItem;
  
/**
 * CumulativeBasic implements the cumulative/4 constraint using edge-finding
 * algorithm and profile information on the resource use.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.4
 */

public class CumulativeBasic extends Constraint {
  
  static int idNumber = 1;

  static final boolean debug = false, debugNarr = false;

  Store store;
  
  /**
   * It contains information about maximal profile contributed by tasks.
   */
  public Profile maxProfile = null;

  /**
   * It contains information about minimal profile contributed by regions
   * for certain occupied by tasks.
   */
  public Profile minProfile = null;

  Profiles cumulativeProfiles = new Profiles();

  // tasks with normal view
  TaskView[] taskNormal;

  /**
   * It specifies if the profiles should be computed to propagate 
   * onto limit variable.
   */
  public boolean doProfile = true;

  /**
   * It specifies if the data from profiles should be used to propagate 
   * onto limit variable.
   */
  public boolean setLimit = false;

  /**
   * It specifies the limit of the profile of cumulative use of resources.
   */
  public IntVar limit;
	
  /**

   * It specifies/stores start variables for each corresponding task. 
   */
  public IntVar[] starts;
	
  /**
   * It specifies/stores duration variables for each corresponding task. 
   */
  public IntVar[] durations;
	
  /**
   * It specifies/stores resource variable for each corresponding task. 
   */
  public IntVar[] resources;
		
  /**
   * It specifies the arguments required to be saved by an XML format as well as 
   * the constructor being called to recreate an object from an XML format.
   */
  public static String[] xmlAttributes = {"starts", "durations", "resources", "limit", "doEdgeFinding", "doProfile"};

  /**
   * It creates a cumulative constraint.
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   * @param doEdgeFinding true if edge finding algorithm should be used.
   * @param doProfile specifies if the profiles should be computed in order to reduce limit variable.
   */
  public CumulativeBasic(IntVar[] starts,
			  IntVar[] durations,
			  IntVar[] resources,
			  IntVar limit,
			  boolean doProfile) {
		
    assert ( starts != null ) : "Variable in starts list is null";
    assert ( durations != null ) : "Variable in durations list is null";
    assert ( resources != null ) : "Variable in resource list is null";
    assert ( limit != null ) : "Variable limit is null";
    assert (starts.length == durations.length) : "Starts and durations list have different length";
    assert (resources.length == durations.length) : "Resources and durations list have different length";
		
    this.numberArgs = (short) (numberArgs * 3 + 1);
    this.queueIndex = 2;
    this.numberId = idNumber++;

    if (starts.length == durations.length && durations.length == resources.length) {
			
      this.taskNormal = new TaskNormalView[starts.length];
      this.starts = new IntVar[starts.length];
      this.durations = new IntVar[durations.length];
      this.resources = new IntVar[resources.length];

      for (int i = 0; i < starts.length; i++) {
				
	assert (starts[i] != null) : i + "-th variable in starts list is null"; 
	assert (durations[i] != null) : i + "-th variable in durations list is null"; 
	assert (resources[i] != null) : i + "-th variable in resources list is null"; 
	assert (durations[i].min() >= 0 ) : i + "-th duration is specified as possibly negative";
	assert (resources[i].min() >= 0 ) : i + "-th resource consumption is specified as possibly negative";
				
	if ( durations[i].min() >= 0 && resources[i].min() >= 0) {
	  taskNormal[i] = new TaskNormalView( new Task(starts[i], durations[i], resources[i]) );
	  this.starts[i] = starts[i];
	  this.durations[i] = durations[i];
	  this.resources[i] = resources[i];
	} else throw new IllegalArgumentException("\nDurations and resources must be >= 0 in cumulative");
			
      }
			
      if (limit.min() >= 0) {
	this.limit = limit;
	numberArgs++;
      } else {
	throw new IllegalArgumentException( "\nResource limit must be >= 0 in cumulative" );
      }
    } else {
      throw new IllegalArgumentException( "\nNot equal sizes of Variable vectors in cumulative" );
    }
		
    this.doProfile = doProfile;
	
  }
	
  /**
   * It creates a cumulative constraint.
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   * @param doEdgeFinding true if edge finding algorithm should be used.
   * @param doProfile specifies if the profiles should be computed in order to reduce limit variable.
   * @param setLimit specifies if limit variable will be prunded.
   */
  public CumulativeBasic(IntVar[] starts,
			   IntVar[] durations,
			   IntVar[] resources,
			   IntVar limit, 
			   boolean doProfile,
			   boolean setLimit) {

    this(starts, durations, resources, limit, doProfile);
    this.setLimit = setLimit;

  }

  /**
   * It creates a cumulative constraint.
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   */
  public CumulativeBasic(ArrayList<? extends IntVar> starts,
			   ArrayList<? extends IntVar> durations, 
			   ArrayList<? extends IntVar> resources,
			   IntVar limit) {

    this(starts.toArray(new IntVar[starts.size()]), 
	 durations.toArray(new IntVar[durations.size()]), 
	 resources.toArray(new IntVar[resources.size()]),
	 limit,
	 true, 
	 true);
		
  }
	
  /**
   * It creates a cumulative constraint.
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   * @param edgeFinding true if edge finding algorithm should be used.
   * @param profile specifies if the profiles should be computed in order to reduce limit variable.
   */


  public CumulativeBasic(ArrayList<? extends IntVar> starts,
			   ArrayList<? extends IntVar> durations, 
			   ArrayList<? extends IntVar> resources,
			   IntVar limit, 
			   boolean profile) {

    this(starts.toArray(new IntVar[starts.size()]), 
	 durations.toArray(new IntVar[durations.size()]), 
	 resources.toArray(new IntVar[resources.size()]), 
	 limit, 
	 profile);
  }

  /**
   * It creates a cumulative constraint.
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   */
  public CumulativeBasic(IntVar[] starts, 
			   IntVar[] durations,
			   IntVar[] resources,
			   IntVar limit) {

    this(starts, durations, resources, limit, true, true);
  }

  /**
   * It creates a cumulative constraint.
   * @param starts variables denoting starts of the tasks.
   * @param durations variables denoting durations of the tasks.
   * @param resources variables denoting resource usage of the tasks.
   * @param limit the overall limit of resources which has to be used.
   * @param edgeFinding true if edge finding algorithm should be used.
   */


  @Override
  public ArrayList<Var> arguments() {

    ArrayList<Var> variables = new ArrayList<Var>(1);

    for (TaskView t : taskNormal)
      variables.add(t.start);
    for (TaskView t : taskNormal)
      variables.add(t.dur);
    for (TaskView t : taskNormal)
      variables.add(t.res);
    variables.add(limit);
    return variables;
  }

  @Override
  public void consistency(Store store) {

    do {
	
      store.propagationHasOccurred = false;
			
      if (doProfile) 
	profileProp();
		
    } while (store.propagationHasOccurred);
		
    minProfile = null;
    maxProfile = null;
  }

  void profileProp() {

    cumulativeProfiles.make(taskNormal, setLimit);
				
    minProfile = cumulativeProfiles.minProfile();
    if (setLimit)
      maxProfile = cumulativeProfiles.maxProfile();
				
    if (debug)
      System.out.println("\n--------------------------------------"
			 + "\nMinProfile for "
			 + id()
			 + " :"
			 + minProfile
			 + "\nMaxProfile for "
			 + id()
			 + " :"
			 + maxProfile
			 + "\n--------------------------------------");

    if (setLimit) 
      limit.domain.in(store.level, limit, minProfile.max(), maxProfile.max());
    else
      if (limit.max() < minProfile.max())
	throw store.failException;
      
    updateTasksRes(store);				
    profileCheckTasks(store);

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
  public void impose(Store store) {

    for (TaskView T : taskNormal) {
      T.start.putModelConstraint(this, getConsistencyPruningEvent(T.start));
      T.dur.putModelConstraint(this, getConsistencyPruningEvent(T.dur));
      T.res.putModelConstraint(this, getConsistencyPruningEvent(T.res));
    }

    limit.putModelConstraint(this, getConsistencyPruningEvent(limit));

    store.addChanged(this);
    store.countConstraint();

    this.store = store;
  }

  void profileCheckInterval(Store store, IntVar Start, IntVar Duration,
			    Interval i, IntVar Resources, int mustUseMin, int mustUseMax) {

    for (ProfileItem p : minProfile) {
      if (debug)
	System.out
	  .println("Comparing " + i + " with profile item " + p);

      if (intervalOverlap(i.min, i.max + Duration.min(), p.min, p.max)) {
	if (debug)
	  System.out.println("Overlapping");
	if (limit.max() - p.value < Resources.min()) {
	  // Check for possible narrowing or fail
	  if (mustUseMin != -1) {
	    ProfileItem use = new ProfileItem(mustUseMin,
					      mustUseMax, Resources.min());
	    ProfileItem left = new ProfileItem();
	    ProfileItem right = new ProfileItem();
	    p.subtract(use, left, right);

	    if (left.min != -1) {
	      int UpdateMin = left.min - Duration.min() + 1, UpdateMax = left.max - 1;
	      if (!(UpdateMin > Start.max() || UpdateMax < Start
		    .min())) {
		if (debugNarr)
		  System.out.print(">>> CumulativeBasic Profile 7a. Narrowed "
				   + Start + " \\ "
				   + new IntervalDomain(UpdateMin, UpdateMax));

		if (UpdateMin <= UpdateMax)
		  Start.domain.inComplement(store.level, Start,
					    UpdateMin, UpdateMax);
		if (debugNarr)
		  System.out.println(" => " + Start);
	      }
	    }

	    if (right.min != -1) {
	      int UpdateMin = right.min - Duration.min() + 1, UpdateMax = right.max - 1;
	      if (!(UpdateMin > Start.max() || UpdateMax < Start
		    .min())) {
		if (debugNarr)
		  System.out.print(">>> CumulativeBasic Profile 7b. Narrowed "
			   + Start + " \\ "
			   + new IntervalDomain(UpdateMin, UpdateMax));

		if (UpdateMin <= UpdateMax)
		  Start.domain.inComplement(store.level, Start,
					    UpdateMin, UpdateMax);
		if (debugNarr)
		  System.out.println(" => " + Start);
	      }
	    }

	    if (Start.max() < right.min
		&& Start.dom().noIntervals() == 1) {
	      int rs = right.min - Start.min();
	      if (rs < Duration.max()) {
		if (debugNarr)
		  System.out.println(">>> CumulativeBasic Profile 9. Narrow "
				     + Duration + " in 0.." + rs);

		Duration.domain.inMax(store.level, Duration, rs);
	      }
	    }
	  } else { // (mustUse.min() == -1 )
	    int UpdateMin = p.min - Duration.min() + 1, UpdateMax = p.max - 1;
	    if (!(UpdateMin > Start.max() || UpdateMax < Start
		  .min())) {
	      if (debugNarr)
		System.out
		  .print(">>> CumulativeBasic Profile 6. Narrowed "
			 + Start
			 + " \\ "
			 + new IntervalDomain(UpdateMin,
					      UpdateMax));
	      if (UpdateMin <= UpdateMax)
		Start.domain.inComplement(store.level, Start,
					  UpdateMin, UpdateMax);

	      if (debugNarr)
		System.out.println(" => " + Start);
	    }
	  }
	} else { // ( Overlapping &&
	  // limit.max() - p.Value >= Resources.min() )
	  if (mustUseMin != -1
	      && !(mustUseMax <= p.min() || mustUseMin >= p.max())) {
	    int offset = 0;
	    if (intervalOverlap(p.min(), p.max(), mustUseMin,
				mustUseMax))
	      offset = Resources.min();
	    if (debugNarr)
	      System.out.println(">>> CumulativeBasic Profile 8. Narrowed "+ Resources
			 + " in 0.."+ (int) (limit.max() - p.value + offset));

	    Resources.domain.in(store.level, Resources, 0, limit
				.max()
				- p.value + offset);
	  }
	}
      } else { // ( ( i.min() >= p.max() || i.max()+dur <= p.min()) )
	if (Start.max() < p.min && Start.dom().noIntervals() == 1) {
	  // System.out.println("Nonoverlaping "+Start+", "+i+", "+p);
	  int ps = p.min - Start.min();
	  if (ps < Duration.max()
	      && limit.max() - p.value < Resources.min()) {
	    if (debugNarr)
	      System.out
		.println(">>> CumulativeBasic Profile 10. Narrowed "
			 + Duration + " in 0.." + ps);

	    Duration.domain.inMax(store.level, Duration, ps);
	  }
	}
      }
    }
  }

  void profileCheckTasks(Store store) {
    IntTask minUse = new IntTask();

    for (TaskView t : taskNormal) {
      IntVar resUse = t.res;
      IntVar dur = t.dur;
      // check only for tasks which cannot allow to have duration or resources = 0
      // if (dur.min() > 0 && resUse.min() > 0) {
      if (dur.max() > 0 && resUse.max() > 0) {
	int A = -1, B = -1;
	if (minUse(t, minUse)) {
	  A = minUse.start();
	  B = minUse.stop();
	}

	if (debug)
	  System.out.println("Start time = " + t.start
			     + ", resource use = " + resUse
			     + ", minimal use = {" + A + ".." + B + "}");

	IntDomain tStartDom = t.start.dom();

	for (int m = 0; m < tStartDom.noIntervals(); m++)
	  profileCheckInterval(store, t.start, dur, tStartDom
			       .getInterval(m), resUse, A, B);
      }
    }
  }

  boolean minUse(Task task, IntTask t) {
    int lst, ect;
    IntDomain sDom = task.start.dom();

    lst = sDom.max();
    ect = sDom.min() + task.dur.min();
    if (lst < ect) {
      t.start = lst;
      t.stop = ect;
      return true;
    } else
      return false;
  }
  
  boolean intervalOverlap(int min1, int max1, int min2, int max2) {
    return !(min1 >= max2 || max1 <= min2);
  }

  @Override
  public void removeConstraint() {
    for (TaskView T : taskNormal) {
      T.start.removeConstraint(this);
      T.dur.removeConstraint(this);
      T.res.removeConstraint(this);
    }
    limit.removeConstraint(this);
  }

  @Override
  public boolean satisfied() {

    Task T;
    boolean sat = true;

    // if profile has been computed make a quick check
    if (minProfile != null && maxProfile != null) {
      if ((minProfile.max() == maxProfile.max()) && limit.singleton()
	  && minProfile.max() == limit.min())
	return true;
      else
	return false;
    } else {
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

  void updateTasksRes(Store store) {
    int limitMax = limit.max();
    for (TaskView T : taskNormal)
      T.res.domain.inMax(store.level, T.res, limitMax);
  }


  @Override
  public void increaseWeight() {
    if (increaseWeight) {
      limit.weight++;
      for (TaskView t : taskNormal) { 
	t.dur.weight++;
	t.res.weight++;
	t.start.weight++;
      }
    }
  }
}
