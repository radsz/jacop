/**
 *  Geost.java 
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.jacop.constraints.Constraint;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.util.SimpleArrayList;
import org.jacop.util.SimpleHashSet;

/**
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 *
 * 1) DONE. FlushAndQueue function should be changed and some functionality
 *	moved to firstConsistencyCheck.
 *
 * 2) DONE. No propagation inside queueVariable function.
 * 
 * 3) DONE. How to incorporate GUI code within Geost constraint.
 * 
 * 4) DONE. Move part of the functionality of onObjectUpdate to consistency function.
 * 
 * 5) Refactor use of TimeBoundConstraint 
 * 5b) DONE. remove runTimeConstraint boolean variable.
 * 
 * 6) DONE. asserts for Shape register 
 * 6b) asserts about possible values of MaxInt and MinInt.
 * 
 * 7) DONE. Use simpleHashSet instead of LinkedHashSet for objectQueue.
 * 
 * 8) DONE. Discuss pruning events, do we really need ANY for all variables? For example, 
   maybe time variables always BOUND pruning event.
 * 
 * 9) DONE. Simplify queueObject by removing if statements and make sure that
 * this function is being called properly (avoid non-asserts checks
 * inside it).
 * 
 * 10) DONE. Discuss the possible implementation of satisfied function.
 *
 * 11) Introduce time switch so geost can work without time dimension. 
 * 
 * 12) Lessen the feature of geost that it does not work with variables used
 * multiple times within different objects 
 * 12b) DONE. (at least for singleton variables). 
 * 
 * 13) DONE. Verify fix to address bug in case of multiple level removals, or level 
 * removals for which no consistency function has been called. Functionality 
 * around variable currentLevel. It is still needed.
 *
 * 14. DONE. Fixing a bug connected with timestamps and multiple remove levels calls. 
 * 14b Check lastLevelVar (possibly needs to be done similarly as setStart). 
 * 
 * Future Work : 
 * 
 * 1. InArea should support subset of objects and dimensions. 
 * 
 * 2. Reuse previously generated outboxes. Create a function to create a hashkey 
 * from points coordinates for which an outbox is required. Later, for each 
 * new point we check if we have proper outbox for a given hash-key generated
 * from this outbox. 
 * 
 * 3. Not always finishing at consistency fixpoint, speculative fixpoint. 
 * 
 * 4. consider polymorphism due to rotations only, and see if
 * better performance can be reached under this assumption. 
 * 
 * 5. If objects have the same shape, and they are indistingushable 
 * then symmetry breaking can be employed. 

 * 
 * 
 */
public class Geost extends Constraint {

	/**
	 * It specifies different debugging switches to print out diverse information about
	 * execution of the geost constraint. 
	 */
	final static boolean DEBUG_ALL = false;
	
	final static boolean DEBUG_MAIN = DEBUG_ALL || false; 
	
	final static boolean DEBUG_SUBSETS = DEBUG_ALL || false;
	
	final static boolean DEBUG_DOUBLE_LAYER = DEBUG_ALL || false;
	
	final static boolean DEBUG_SHAPE_SKIP = DEBUG_ALL || false;
	
	final static boolean DEBUG_VAR_SKIP = DEBUG_ALL || false;
	
	final static boolean DEBUG_OBJECT_GROUNDING = DEBUG_ALL || false;
	
	final static boolean DEBUG_BACKTRACK = DEBUG_ALL || false;
	
	final static boolean GATHER_STATS = true;

	final static boolean DEBUG_REORDER = false;
	
	/**
	 * It counts how many constraints we discounted in outbox generation procedure as not useful ones. 
	 */
	long filteredConstraintCount;
	
	/**
	 * It counts the number of times the minimum values of geost objects origins are being examined for pruning. 
	 */
	long pruneMinCount = 0;
	
	/**
	 * It counts the number of times the minimum values of geost objects origins are being examined for pruning.
	 * It may be different (smaller than) prunedMinCount as constraint may have failed during min domain pruning.  
	 */	
	long pruneMaxCount = 0;
	
	/**
	 * It counts number of executions of outboxes generation. 
	 */
	long findForbiddenDomainCount = 0;
	
	/**
	 * It counts the number of object updates.
	 */
	long onObjectUpdateCount = 0;
	
	/**
	 * It counts how many times the feasibility check is being performed by internal constraint on a supplied 
	 * point. 
	 */
	long isFeasibleCount = 0;
	
	/**
	 * It counts how many times the object has been queued. 
	 */
	long queuedObjectCount = 0;	

	/**
	 * Not used, but kept in case graphical debugging is needed in the future.
	 */
	//BoxDisplay display = null;

	/**
	 * It specifies the unique number used to differentiate geost constraints.
	 */
	static int IdNumber = 1;

	/**
	 * It indicates whether we are currently running the consistency function or not.
	 */
	boolean inConsistency;

	/**
	 * If equal to true then modifying one object implies that all objects have to be added 
	 * to object queue.
	 */
	boolean allLinked = false;

	/**
	 * It is used to signal that some shape ID was pruned.
	 * It is required because pruning skip condition (var grounded, and not in the queue)
	 * can only be safely used if no shape id field was pruned.
	 * Indeed, if some shape ID was pruned, feasibility can change, thus a check is needed.
	 */
	boolean changedShapeID = false;


	/**
	 * if set to true, a variable will never be skipped, even if grounded and not in queue
	 */
	public boolean enforceNoSkip = false;
	
	/**
	 * It remembers if it is the first time the consistency check is being performed.
	 * If not, then the initial consistency checks which have to be done only once
	 * will be done during the first consistency check. This flag is set back to true
	 * if the remove level function is removing the level onto which the changes
	 * caused by the initial consistency were applied to. 
	 */
	boolean firstConsistencyCheck; 

	/**
	 * It remembers the level at which the consistency function was applied for the first time. 
	 * If that level is being removed then the initial consistency function must be executed again.
	 */
	int firstConsistencyLevel;


	/**
	 * It specifies for each object if consistency function should be run if this object becomes grounded. 
	 * It is set to true if the object was grounded outside consistency function call or after a shape variable
	 * has been changed. It is set to false only after exactly one consistency check during which the object 
	 * was grounded. 
	 */
	final boolean[] pruneIfGrounded;
	
	/**
	 * It maps any variable in the scope of the geost constraint to the object it belongs to.
	 */
	final Map<Var, GeostObject> variableObjectMap;
	
	
	/**
	 * It stores all variables which have changed outside the consistency function of this constraint. 
	 */
	LinkedHashSet<Var> variableQueue;	
	
	/**
	 * It stores the position of the last variable grounded in the previous level. 
	 */
	TimeStamp<Integer> lastLevelLastVar;
	
	/**
	 * It contains all the objects which have been updated in the previous levels. 
	 */
	SimpleArrayList<GeostObject> objectList;

	/**
	 * It contains all the objects which have been updated at current level. The objects
	 * from this set are moved to the array objectList as soon as level is increased. If 
	 * level is being removed then for every object in this set we inform the external constraints
	 * that their state in connection to this object may have changed.
	 */
	Set<GeostObject> updatedObjectSet;

	/**
	 * it stores the index of the first object which have changed at current level. It allows 
	 * to inform the external constraints about objects being changed due to backtracking.
	 */
	TimeStamp<Integer> setStart;

	/**
	 * It stores the information about left bound of the interval of objects which are 
	 * updated by backtracking. It is set by removeLevel function and it is used by 
	 * removeLevelLate function. It simply denotes the stopping condition. 
	 */
	//int lowerBound;

	/**
	 * 	It contains objects that need to be checked in the next sweep.
	 */
	SimpleHashSet<GeostObject> objectQueue;
	
	/**
	 * It is a locally used array which stores the enumeration of values for 
	 * the current shape variable. The enumeration is lexicographical with 
	 * one exception the previously found best shape is put on the first position.
	 */
	final int[] shapeIdsToPrune;
	
	/**
	 * set to false to disable relaxed shape pruning
	 */
	public boolean partialShapeSweep = true;
	
	/**
	 * It stores all generated internal constraints for all objects/constraints. It
	 * is used to speed up some visualization functions. If not for that reason it could
	 * have been a local variable within a function generating internal constraints.
	 */
	public Collection<InternalConstraint> internalConstraints;

	/**
	 * For each object, the set of constraint that apply to it
	 * we use object ids as keys, and can thus use an array to store
	 * the map. This is the input set to the filtering process 
	 * before pruning any object.
	 */
	Set<InternalConstraint>[] objectConstraints;

	
	
	/**
	 * It stores the special constraints responsible for the handling of holes in the domain.
	 * It is indexed by object id.
	 */
	final DomainHoles[] domainHolesConstraints;

	
	/**
	 * It specifies the order between dimensions which is used by the 
	 * pruning algorithm. The order may have influence on the algorithm 
	 * efficiency. The geost constraint chooses the order based on average
	 * length of objects in the particular dimension. The dimension with
	 * higher average length in this dimension will have the preference.
	 */
	public final LexicographicalOrder order;

	/**
	 * A preallocated array of ints used extensively within sweeping algorithm.
	 */
	final int[] c;
	/**
	 * A preallocated array of ints used extensively within sweeping algorithm.
	 */
	final int[] n;

	/**
	 * It keeps a reference to the store. 
	 * 
	 */
	protected Store store;
	
	/**
	 * It stores all variables which have been grounded. It is used to upon backtracking
	 * to update objects to their previous state.
	 */
	final SimpleArrayList<Var> groundedVars;

	/**
	 * It contains all not filtered out, useful internal constraints which should 
	 * be used to generate outboxes. The initial array of internal constraints
	 * associate with a given object being pruned can be significantly shrank 
	 * and the remaining objects (still useful) are store in this array.
	 */
	InternalConstraint[] stillUsefulInternalConstraints;
	
	/**
	 * It specifies the last useful constraint in the array of useful internal 
	 * constraints. 
	 */
	int lastConstraintToCheck = 0;

	/**
	 * It specifies that filtering of useless internal constraint takes place
	 * before an object is being pruned. It may be costly for small instances.
	 */
	public final boolean filterUseless = true; 
	
	/**
	 * It defines whether outbox generation should always rely on overlapping frames.
	 * For problems that contain objects that have small domains compared to their size, then
	 * using only frames may provide a better performance (up to 50% faster). It can only 
	 * be changed before impose() function, changing it afterwards will lead to improper
	 * behavior.
	 */
	public boolean alwaysUseFrames = false;
	

	/**
	 * It is a flag set to true during remove level late function execution so objects which 
	 * are being updated upon backtracking can be handled properly.
	 */
	public boolean backtracking;	
	
	/**
	 * If running a complete sweep for each shape is costly, because some shapes may require
	 * a significant sweep, even though a weaker bound has already been found.
	 * However, to be able to prune shapes, such a costly sweep needs to be done.
	 * A tradeoff solution consists in running a complete sweep for each shape once per
	 * node, and optimize the following runs.
	 * This implies remembering which object have already been fully pruned.
	 */
	final boolean[] fullyPruned;
		
	/**
	 * It stores temporarily objects for which pruning is suggested by external constraints. 
	 * The geost constraint checks every object from this set to see if that is actually 
	 * necessary to invoke the pruning for that object.
	 */
	final SimpleHashSet<GeostObject> temporaryObjectSet;

	
	/**
	 * A temporary list to collect bounding boxes for each shape of the given object
	 * to compute one bounding box whatever the shape of the object. It is made 
	 * as a member of the geost constraint to avoid multiple memory allocations.
	 */
	final SimpleArrayList<DBox> workingList;

	
	/**
	 * It specifies the number of dimensions of each object given to the geost constraint. 
	 */
	final int dimension;

	/**
	 * It is set by queueVariable after a time variable has been changed. It indicates 
	 * that we should run the consistency function of the time constraint.
	 */
	private boolean oneTimeVarChanged;

	/**
	 * It is used inside flushQueue function to separate timeconsistency execution from 
	 * object update (potentially expensive if for example object frame is recomputed). 
	 */
	SimpleArrayList<GeostObject> objectList4Flush = new SimpleArrayList<GeostObject>(); 

	/**
	 * It stores the reference to the collection of objects provided to 
	 * the constructor. It does not perform cloning so the collection can 
	 * not change after geost constraint was imposed.
	 */
	public final GeostObject[] objects;

	
	/**
	 * It stores the reference to the collection of external constraints
	 * which must be satisfied within this constraint. This is a reference
	 * to the collection provided within the constructor. No copying is employed
	 * therefore the collection can not change even after the constraint is imposed.
	 */
	public final ExternalConstraint[] externalConstraints;
	

	/**
	 * It stores information about shapes used by objects within this geost constraint. 
	 * It is based on shapes information provided in the constructor. 
	 */
	public final Shape[] shapeRegister;
	
	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"objects", "externalConstraints", "shapeRegister"};

	@SuppressWarnings("all")
	public Geost(Collection<GeostObject> objects, 
				 Collection<ExternalConstraint> constraints, 
				 Collection<Shape> shapes) {
		this(objects.toArray(new GeostObject[objects.size()]), 
			 constraints.toArray(new ExternalConstraint[constraints.size()]), 
			 shapes.toArray(new Shape[shapes.size()]));
	}
	/**
	 * It creates a geost constraint from provided objects, external constraints, 
	 * as well as shapes. The construct parameters are not cloned so do not 
	 * reuse them in creation in other constraints if changes are necessary.
	 * Make sure that the largest object id is as small as possible to avoid 
	 * unnecessary memory cost. 
	 * 
	 * @param objects objects in the scope of the geost constraint.
	 * @param constraints the collection of external constraints enforced by geost.
	 * @param shapes the list of different shapes used by the objects in scope of the geost. 
	 * 
	 */
	@SuppressWarnings("all")
	public Geost(GeostObject[] objects, 
				 ExternalConstraint[] constraints, 
				 Shape[] shapes) {

		// This comes from the frame computation for NonOverlapping external constraint.
		assert (IntDomain.MaxInt < Integer.MAX_VALUE / 4 - 1) : "Geost can not work with too large Constants.MaxInt";
		assert (IntDomain.MinInt > Integer.MIN_VALUE / 4 + 1) : "Geost can not work with too small Constants.MinInt";
		
		assert(objects.length > 0): "empty collection of objects";
		assert(shapes.length > 0): "empty collection of shapes";
		assert(constraints.length > 0): "empty collection of constraints";

		this.queueIndex = 2;
		this.objects = objects.clone();
		this.externalConstraints = constraints.clone();

		this.numberId = IdNumber++;
		this.variableQueue = new LinkedHashSet<Var>();
		
		//objectQueue = new LinkedHashSet<GeostObject>( objects.size() );
		//objectQueue.addAll(objects);
		
		objectQueue = new SimpleHashSet<GeostObject> ( objects.length );
		for (GeostObject o : objects)
			objectQueue.add( o );
		
		Map<Integer, Shape> idShapeMap = new HashMap<Integer, Shape>();
		
		//add all shapes to the register
		for(Shape s : shapes) {
			if(s.no < 0)
				throw new IllegalArgumentException("shape ID has to be positive");
			idShapeMap.put(s.no, s);
		}
		
		//make sure that all objects have the same dimension
		//make sure that IDs are unique
		//make sure that the shapes used are defined
		Set<Integer> objectIds = new HashSet<Integer>();
		int dim = -1;
		int idMax = 0;
		
		for(GeostObject o: objects) {
			
			if( objectIds.contains(o.no) )
				throw new IllegalArgumentException("all objects must have a different ID");
			else if(o.no < 0)
				throw new IllegalArgumentException("object ID has to be positive");
			else {
				objectIds.add(o.no);
				idMax = Math.max(o.no, idMax);
			}
			
			if(dim == -1)
				dim = o.dimension;
			else if(dim != o.dimension)
					throw new IllegalArgumentException("all objects must have the same number of dimensions");
			
			//make sure that the shapes used are defined
			ValueEnumeration shapeIDVals = o.shapeID.domain.valueEnumeration();
			while(shapeIDVals.hasMoreElements()) {
				int sid = shapeIDVals.nextElement();
				if(!idShapeMap.containsKey(sid))
					throw new IllegalArgumentException("shape id " + sid + " does not correspond to any shape");
			}
			
		}
		
		dimension = dim;
		
		objectConstraints = new Set[idMax + 1];
		domainHolesConstraints = new DomainHoles[idMax +1];
		
		pruneIfGrounded = new boolean[idMax + 1];
		Arrays.fill(pruneIfGrounded, false);
		
		shapeRegister = new Shape[idShapeMap.size()];
		
		for(Map.Entry<Integer, Shape> e : idShapeMap.entrySet()) {
			assert (e.getKey() < idShapeMap.size() ) : "Shapes do not have unique ids between 0 and n-1, where n is number of shapes.";
			shapeRegister[e.getKey()] =  e.getValue();
		}
				
		if(partialShapeSweep)
			fullyPruned = new boolean[idMax + 1];
		else 
			fullyPruned = null;
		
		//make sure the DBox pool is correctly initialized
		DBox.supportDimension(dimension);
		DBox.supportDimension(dimension+1); //one more slot for time
		
		shapeIdsToPrune = new int[shapeRegister.length];
		
		assert (dimension > 0) : "No dimensions";
		
		// one extra dimension for time
		c = new int[dimension+1];
		n = new int[dimension+1];

		//use an ordering based on average box sizes: longer dimension first
		int[] shapeNb = new int[shapeRegister.length];
		int totShapes = 0;

		//compute cumulated box sizes
		double[] averageSizes = new double[dimension + 1];

		Arrays.fill(shapeNb, 0);

		for(GeostObject o : objects) {
			ValueEnumeration vals = o.shapeID.domain.valueEnumeration();
			while (vals.hasMoreElements()) {
				shapeNb[vals.nextElement()]++;
				totShapes++;
			}
			averageSizes[dimension] += o.end.max() - o.start.min();
		}

		for(int i = 0; i < shapeRegister.length; i++)
			for(int j = 0; j < averageSizes.length - 1; j++)
				averageSizes[j] += shapeRegister[i].boundingBox.length[j]*shapeNb[i];

		for(int j = 0; j < averageSizes.length - 1; j++)
			averageSizes[j] /= totShapes;

		averageSizes[dimension] /= objects.length;

		//now, averageSizes contains, for each dimension, the average box size
		//we can now get the corresponding ordering of dimensions

		//smallest dimension first
		int[] ordering = new int[dimension + 1];
		for(int i = 0; i < ordering.length; i++) {
			//find smallest value
			double smallestYet = Double.MAX_VALUE;
			int smallestIndex = 0;
			for(int j = 0; j < ordering.length; j++)
				if(averageSizes[j] < smallestYet) {
					smallestYet = averageSizes[j];
					smallestIndex = j;
				}
			ordering[i] = smallestIndex;
			averageSizes[smallestIndex] = Double.MAX_VALUE;
		}

		//ordering now corresponds to average box sizes, smallest first
		order = new PredefinedOrder(ordering, 0);

		
		variableObjectMap = new HashMap<Var, GeostObject>();

		for(GeostObject o: objects)
			for(Var v : o.getVariables()) {
				if (!v.singleton()) {
					GeostObject previousValue = variableObjectMap.put(v, o);
					assert (previousValue == null) : "Current implementation of Geost does not allow reuse of not singleton variables.";
				}
			}

		inConsistency = false;
		
		temporaryObjectSet = new SimpleHashSet<GeostObject>();
		

		backtracking = false;
		workingList = new SimpleArrayList<DBox>();
		
		assert (checkInvariants() == null) : checkInvariants();
		
		
		groundedVars = new SimpleArrayList<Var>();
		
		// boxDisplay = new BoxDisplay(20, "inside");
	}
	
	/**
	 * It checks that this constraint has consistent data structures.
	 * 
	 * @return a string describing the consistency problem with data structures, null if no problem encountered.
	 */
	
	public String checkInvariants(){
	
		if(order == null) return "lexical order is null";
		if(variableQueue == null) return "variable queue is null";
//		if(objectQueue == null) return "object queue is null";
		if(objectQueue == null) return "object queue is null";
		if(c.length != n.length) return "c and n must have the same size";
		if(objects.length == 0) return "empty collection of objects";
		if(externalConstraints.length == 0) return "empty collection of constraints";
		
		return null;
	}
	
	
	
	/**
	 * It returns the shape with a given id if such exists.
	 * 
	 * @param id the unique id of the shape we are looking for.
	 * @return the shape of a given id previously provided.
	 */
	public final Shape getShape(int id) {
		
		assert  id >= 0 && id < shapeRegister.length && shapeRegister[id] != null : "unknown shape id: " + id;
		
		return shapeRegister[id];
		
	}
	
	
	
	protected void genInternalConstraints() {
		
		internalConstraints = new ArrayList<InternalConstraint>();
		
		int constraintCount = 0;
		
		for(ExternalConstraint ec : externalConstraints) {
		
			final Collection<? extends InternalConstraint> ics = ec.genInternalConstraints(this);
			
			//prepare all data structures
			for(GeostObject o : objects)
				ec.onObjectUpdate(o);
			
			internalConstraints.addAll(ics);
			
			constraintCount += ics.size();
		
		}
		
		assert constraintCount == internalConstraints.size() : "some constraints were not added correctly";
		
		//initialize array used to stored filtered constraints. Has to be large enough to store all constraints
		stillUsefulInternalConstraints = internalConstraints.toArray(new InternalConstraint[internalConstraints.size()]);
		
		/*
		 * TODO reuse different scopes if equal so that quadratic use of memory is avoided
		 * 
		 * For a moment a simple solution is implemented: simple case where all constraints apply to all objects
		 */
		
		//find out if all constraints apply on the whole collection of objects
		allLinked = true;
		
		Set<Object> scope = new HashSet<Object>();
		
		for(ExternalConstraint ec : externalConstraints) {
			
			GeostObject[] constraintScope = ec.getObjectScope();
			
			if(constraintScope != null) {
				
				int prevSize = scope.size();
				
				ArrayList<GeostObject> constraintScopeArr = new ArrayList<GeostObject>(constraintScope.length);
				for (GeostObject o : constraintScope)
					constraintScopeArr.add(o);
				
				boolean changed = scope.addAll(constraintScopeArr);
				
				if(changed && prevSize != 0) {
					//some constraint applies to a subset of objects only
					allLinked = false;
					break;
				}
				
			}
			
		}
		
		if( allLinked && scope.size() != objects.length ) {
			//may appear if only one constraint applies to a subset of objects
			allLinked = false;
		}
		
		/*
		 * generate constraint corresponding to holes in the domain.
		 * They are handled separately because they are relevant only for
		 * the object being placed
		 * 
		 */
		if( !allLinked ){
			for(GeostObject o: objects) {
				domainHolesConstraints[o.no] = new DomainHoles(o);

				//collect related constraints
				Set<InternalConstraint> relatedConstraints = new HashSet<InternalConstraint>();
				for(ExternalConstraint ec : externalConstraints)
					relatedConstraints.addAll(ec.getObjectConstraints(o));
				objectConstraints[o.no] = relatedConstraints;
				
			}
		} else {

			Set<InternalConstraint> commonConstraints = new HashSet<InternalConstraint>();
			commonConstraints.addAll(internalConstraints);

			for(GeostObject o: objects){
				domainHolesConstraints[o.no] = new DomainHoles(o);
				objectConstraints[o.no] = commonConstraints;
			}
		}
		
		

		
	}
	
	/**
	 * the sweeping routine for minimal bounds. Since in the polymorphic case, it is run for each possible shape,
	 * and only the weakest result is used, it cannot have side-effects. In particular, it cannot
	 * directly update domain values.
	 * If any data structure is updated here, make sure that it is done carefully enough.
	 * @param store the store
	 * @param o the object to prune
	 * @param d the current most significant dimension
	 * @param limit stop pruning if going beyond this value
	 * @return the bound found if there is one, and Constants.MaxInt if there is no feasible placement.
	 */
	
	protected int pruneMin(Store store, 
						   GeostObject o, 
						   int currentShape, 
						   int d, 
			//			   Set<InternalConstraint> I, 
						   int limit) {
		
		boolean feasiblePointFound = true;
		
		// if(USE_DISPLAY)
		//	display.eraseAll();
		
		if(DEBUG_MAIN)
			System.out.println("pruneMin");
		
		Geost.SweepDirection dir = Geost.SweepDirection.PRUNEMIN;

		order.setMostSignificantDimension(d);
		
		//c is initialized with the lower bound of the object's domain, n with the upper bound+1
		for(int i = 0, size = o.dimension; i < size ; i++) {
			c[i] = o.coords[i].min();
			n[i] = o.coords[i].max()+1;
		}
		
		c[dimension] = o.start.min();
		n[dimension] = o.start.max() + 1; 
		
		if(DEBUG_MAIN)
			System.out.println("shape ID in pruneMin: " + currentShape);
		
		if(DEBUG_MAIN) {
			System.out.println("inital, c and n:");
			System.out.println("c:" + Arrays.toString(c));
			System.out.println("n:" + Arrays.toString(n));
		}
		
		DBox f = null;
		
		while(feasiblePointFound && (f = findForbiddenDomain(o,currentShape, c, dir, order)) != null) {
		
			assert f.containsPoint(c) : "bad forbidden region, c is not contained";
			
			//update n
			for(int i = 0, size = o.dimension+1; i < size ; i++) {
				
				n[i] = Math.min(n[i], f.origin[i] + f.length[i]);
				assert n[i] > c[i] : "n is not larger than c in pruneMin";
				
			}
			
			feasiblePointFound = false;
			//sweep in each dimension, from the less significant to the most
			
			for(int i = o.dimension; i >= 0; i--) {
				
				int lexI = order.dimensionAt(i); 
				
				final int domainMin = lexI != dimension ? o.coords[lexI].min() : o.start.min();
				final int domainMax = lexI != dimension ? o.coords[lexI].max() : o.start.max();
				
				c[lexI] = n[lexI];
				n[lexI] = domainMax + 1;
				
				if(c[lexI] <= domainMax) {
					feasiblePointFound = true;
					break;
				} else {
					assert feasiblePointFound == false;
					c[lexI] = domainMin;
				}
			}
			
			if(c[d] >= limit)
				//we were asked to stop searching here
				return limit;
			
		//	if(USE_DISPLAY) {
		//		display.display2DBox(f, Color.red);
		//		display.display2DPoint(c, Color.green);
		//		display.display2DPoint(n, Color.blue);
		//	}
			
			if(DEBUG_MAIN){
				System.out.println("outbox found, c and n:");
				System.out.println("c:" + Arrays.toString(c));
				System.out.println("n:" + Arrays.toString(n));
			}
			
		}
		
		if( feasiblePointFound ) {
			assert c[d] >=  ( d != dimension ? o.coords[d].min()  : o.start.min()) : "feasible point found " + c[d] + " is outside domain " + ( d != dimension ? o.coords[d]  : o.start);
			return c[d]; // the check for sweep advance is done later by the consistency function
		} else 
			return IntDomain.MaxInt;
		
	}
	/**
	 * the sweeping routine for minimal bounds. Since in the polymorphic case, it is run for each possible shape,
	 * and only the weakest result is used, it cannot have side-effects. In particular, it cannot
	 * directly update domain values.
	 * If any data structure is updated here, make sure that it is done carefully enough.
	 * @param store the store
	 * @param o the object to prune
	 * @param d the current most significant dimension
	 * @param limit stop pruning if going beyond this value
	 * @return the bound found if there is one, and Constants.MinInt if there is no feasible placement.
	 */
	protected int pruneMax(Store store, 
						   GeostObject o, 
						   int currentShape, 
						   int d, 
		//				   Set<InternalConstraint> I, 
						   int limit) {
		
		boolean feasiblePointFound = true;
		
	//	if(USE_DISPLAY)
	//		display.eraseAll();
		
		if(DEBUG_MAIN){
			System.out.println("pruneMax");
		}
		
		Geost.SweepDirection dir = Geost.SweepDirection.PRUNEMAX;
		order.setMostSignificantDimension(d);
		
		//c is initialized with the upper bound of the object's domain, n with the lower bound-1
		for(int i = 0, size=o.dimension; i<size ; i++){
			c[i] = o.coords[i].max();
			n[i] = o.coords[i].min()-1;
		}
		//when considering time, pruneMax will try to reduce the upper bound of the domain (start+duration)
		c[dimension] = o.end.max();
		n[dimension] = o.end.min()-1;
		
		if(DEBUG_MAIN){
			System.out.println("shape ID in pruneMax: " + currentShape);
		}
		if(DEBUG_MAIN){
			System.out.println("initial c and n:");
			System.out.println("c:" + Arrays.toString(c));
			System.out.println("n:" + Arrays.toString(n));
		}
		
		DBox f = null;
		while(feasiblePointFound && (f = findForbiddenDomain(o,currentShape, c, dir, order))!=null){
			
			assert f.containsPoint(c) : "bad forbidden region, c is not contained";
	
			//update n
			for(int i = 0, size=o.dimension+1; i<size ; i++){
				/*
				 * need to subtract 1 to the origin of the outbox because we want
				 * the next feasible point, and the outbox origin is still infeasible
				 */
				n[i] = Math.max(n[i], f.origin[i]-1); 
				
				assert n[i] < c[i] : "n is not smaller than c in pruneMax";
			}
			
			feasiblePointFound = false;
			//sweep in each dimension, from the less significant to the most
			for(int i = o.dimension; i >= 0; i--){
				int lexI = order.dimensionAt(i);
				final int domainMin = lexI != dimension ? o.coords[lexI].min() : o.end.min();
				final int domainMax = lexI != dimension ? o.coords[lexI].max() : o.end.max();
				
				c[lexI] = n[lexI];
				n[lexI] = domainMin - 1;
				
				if(c[lexI] >= domainMin) {
					feasiblePointFound = true;
					break;
				} else {
					assert feasiblePointFound == false;
					c[lexI] = domainMax;
				}
				
//				if(USE_DISPLAY){
//					display.display2DBox(f, Color.red);
//					display.display2DPoint(c, Color.green);
//					display.display2DPoint(n, Color.blue);
//				}
				
			}
			if(c[d] <= limit){
				//we were asked to stop searching here
				return limit;
			}
			
			if(DEBUG_MAIN){
				System.out.println("outbox found, c and n:");
				System.out.println("c:" + Arrays.toString(c));
				System.out.println("n:" + Arrays.toString(n));
			}
			
		}
		
		if(feasiblePointFound){
			assert c[d] <=  ( d != dimension ? o.coords[d].max()  : o.end.max()) : "feasible point found " + c[d] + " is outside domain " + ( d != dimension ? o.coords[d]  : o.end);
			return c[d]; // the check for sweep advance is done later by the consistency function
		} else
			return IntDomain.MinInt;
		
	}
	
	protected DBox findForbiddenDomain(GeostObject o, 
									   int currentShape, 
									   int[] point, 
						//			   Collection<InternalConstraint> constraints, 
									   Geost.SweepDirection dir, 
									   LexicographicalOrder order){
		
		if(DEBUG_MAIN){
	//		System.out.println("findForbidenDomain: constraints:" + constraints.size());
			System.out.println("shape ID in findForbiddenDomain: " + currentShape);
		}
		
		if(GATHER_STATS)
			findForbiddenDomainCount++;
		
	//	assert constraints != null : "not using correct version";
		
		//if there are holes in the domain, consider these first
		DomainHoles holeConstraint = domainHolesConstraints[o.no];
		
		if(DomainHoles.debug) {
			System.out.println("checking for holes of object " + o);
			System.out.println("associated constraint: " + holeConstraint);
		}
		
		// If the hole within domain can be used to generate the outbox then it is checked first.
		if( holeConstraint.stillHasHole() ) {
			
			if(GATHER_STATS)
				isFeasibleCount++;
			
			DBox f = holeConstraint.isFeasible(dir, order, o, currentShape, point);
			
			if(f != null)
				return f;
			
		}
		
		if(GATHER_STATS)
			// BUG?
			// length is not ok to use since this array is allocated initially based on the count of 
			// ALL internal constraints for all objects and not the internal constraints associated with 
			// a given object. Should be objectConstraints[o.id].size() ?
			filteredConstraintCount += stillUsefulInternalConstraints.length - lastConstraintToCheck;
				
		//then go on with the standard filtered constraints
		for(int ci = lastConstraintToCheck - 1; ci >= 0; ci--) {
			
			final InternalConstraint c = stillUsefulInternalConstraints[ci];
			
			if(GATHER_STATS)
				isFeasibleCount++;
			
			DBox f = c.isFeasible(dir, order, o, currentShape, point);
			
			if(f != null)
				return f;
			
		}
		
		return null;
	}
	

	@Override
	public ArrayList<Var> arguments() {
		ArrayList<Var> args = new ArrayList<Var>();
		
		//note: having the function return a collection would avoid this copy into an array list
		args.addAll(variableObjectMap.keySet());
		
		return args;
	}

	@Override
	@SuppressWarnings("all")
	public void consistency(Store store) {
		
		try {
			
			inConsistency = true;			
			changedShapeID = false;
			
			if(DEBUG_MAIN || DEBUG_SHAPE_SKIP || DEBUG_VAR_SKIP || DEBUG_OBJECT_GROUNDING)
				System.out.println("consistency(" + store.level + ")");		

			if (firstConsistencyCheck) {
				
				// enforce duration > 0 constraint
				
				for(GeostObject o : objects) {
					o.timeConstraint.consistencyDurationGtZero(store);
					
					if(o.timeConstraint.consistencyStartPlusDurationEqEnd(store)) {
					//	queueObject(o);
						onObjectUpdate(o);
					}

				}
				
				firstConsistencyCheck = false;
				firstConsistencyLevel = store.level;
				
			}


			if(partialShapeSweep)
				Arrays.fill(fullyPruned, false);

			//update the objects that are defined by some variables that changed
			flushQueue(variableQueue);

			while(!objectQueue.isEmpty()){
				
				GeostObject o = objectQueue.removeFirst();
				
				boolean emptyQueue = false;
				
				//an object can be in the queue even though it is grounded, 
				//if it was grounded twice in the same pruning
				while (o.isGrounded() && !pruneIfGrounded[o.no] && !emptyQueue)
					if(!objectQueue.isEmpty())
						o = objectQueue.removeFirst();
					else 
						emptyQueue = true;

				if(emptyQueue)
					break; // all objects done, get out of consistency()

				// object o will be checked now and since it is grounded then there is no need for 
				// another check after that.
				pruneIfGrounded[o.no] = false;
				
				if(DEBUG_OBJECT_GROUNDING)
					System.out.println("pruning object " + o);
					

				boolean fullSweep = true;
				if(partialShapeSweep) {
					//if object already had a full sweep in this node, do partial sweep only
					if(fullyPruned[o.no] == true)
						fullSweep = false;
					else
						fullyPruned[o.no] = true;
				}

				updateInternalConstraintsGeneratingOutboxes(o);

				if(DEBUG_MAIN || DEBUG_SHAPE_SKIP || DEBUG_VAR_SKIP || DEBUG_OBJECT_GROUNDING) {
					
					System.out.println("pruning " + o);

					if(DEBUG_SHAPE_SKIP)
						System.out.println("o.bestShapeID = " + Arrays.toString(o.bestShapeID));
					
				}

				boolean inconsistent = false;

				// Sweep using master ordering. Later on, for each dimension in the 
				// loop below we will be changing most significant dimension.
				int[] ordering = order.masterOrdering();

				for(int di = 0, size = dimension + 1; di < size; di++) { //time is the additional dimension

					int d = ordering[di];

					/*
					 * if the variable is a singleton and is not in the variable queue,
					 * it means that it has been either grounded or checked by geost. 
					 * If no shape was removed, result would not change, therefore there is
					 * no need to run the pruning for that variable
					 * Another exception is if shapeID is not a singleton. Indeed, in this case, 
					 * we may be able to remove a shape that is not useful.
					 */
					boolean needPruning = true;
					//if no shape ID changed and o.shapeID is a singleton, consider skipping variable
					if(!changedShapeID && o.shapeID.singleton())
						if(d != dimension){
							final Var prunedVar = o.coords[d];
							needPruning = !(prunedVar.singleton() && !variableQueue.contains(prunedVar));
						} else {
							needPruning = !(o.start.singleton() && o.end.singleton()
									&& !variableQueue.contains(o.start)
									&& !variableQueue.contains(o.end)
									&& !variableQueue.contains(o.duration));

						}

					if(enforceNoSkip)
						needPruning = true;

					if(needPruning) {

						// It specifies the lowest lower bound found for the origin across multiple shapes.
						int minLowerBound = IntDomain.MaxInt;
						// It specifies the highest upper bound for for the origin across multiple shapes.
						int maxUpperBound = IntDomain.MinInt;

						int lastSidIndex = 0;
						boolean bestShapeIDFound = false;
						int bestSidLastPrune = o.bestShapeID[d];

						final ValueEnumeration vals = o.shapeID.domain.valueEnumeration();
						while(vals.hasMoreElements()) {
							
							int sid = vals.nextElement();

							if(sid == bestSidLastPrune){
								bestShapeIDFound = true;
								shapeIdsToPrune[0] = sid;
							} else {
								lastSidIndex++;
								shapeIdsToPrune[lastSidIndex] = sid;
							}
							
						}
						
						if(!bestShapeIDFound) {
							//best shape ID was removed from o.shapeID
							shapeIdsToPrune[0] = shapeIdsToPrune[lastSidIndex];
							assert lastSidIndex >= 1;
							lastSidIndex --;
						}


						int bestLowerBound = IntDomain.MaxInt;
						int bestUpperBound = IntDomain.MinInt;
						
						for(int i = 0; i <= lastSidIndex; i++) {
							
							int sid = shapeIdsToPrune[i];

							if(DEBUG_MAIN)
								System.out.println("shape ID in consistency: " + sid);
							
							if(GATHER_STATS)
								pruneMinCount++;
							
							int lowerBound = pruneMin(store, 
													  o,
													  sid, 
													  d, 
			//										  internalConstraintsToUse, 
													  fullSweep ? IntDomain.MaxInt : minLowerBound);
							
							if(lowerBound >= IntDomain.MaxInt) {
								
								//remove shape ID, it is infeasible
								if(DEBUG_DOUBLE_LAYER)
									System.out.println("geost " + id() + " changing " + o.shapeID + ", removing " + sid);
								
								changedShapeID = true;

								//don't skip objects again if some shape ID changed
								Arrays.fill(pruneIfGrounded, true);
								
								// o.shapeID.domain.in(store.level, o.shapeID, o.shapeID.domain.subtract(sid));
								// CHANGED. replaced the above with the line below.
								o.shapeID.domain.inComplement(store.level, o.shapeID, sid);

							} else {
								
								minLowerBound = Math.min(minLowerBound, lowerBound);

								//consider pruning in the other direction only if the first did not fail
								if(GATHER_STATS)
									pruneMaxCount++;
								
								int upperBound = pruneMax(store, 
														  o,sid, 
														  d, 
			//											  internalConstraintsToUse, 
														  fullSweep ? IntDomain.MinInt : maxUpperBound);
								
								if(upperBound <= IntDomain.MinInt) {
									
									//remove shape ID, it is infeasible
									if(DEBUG_DOUBLE_LAYER)
										System.out.println("geost " + id() + " changing " + o.shapeID + ", removing " + sid);
									
									changedShapeID = true;

									//don't skip objects if some shape ID changed
									Arrays.fill(pruneIfGrounded, true);
									
									// o.shapeID.domain.in(store.level, o.shapeID, o.shapeID.domain.subtract(sid));
									// CHANGED. replaced the above with the line below.
									o.shapeID.domain.inComplement(store.level, o.shapeID, sid);

								} else {
									maxUpperBound = Math.max(maxUpperBound, upperBound);

									//update bestShapeID if better than previous one
									if(lowerBound <= bestLowerBound && upperBound >= bestUpperBound) {
										bestLowerBound = lowerBound;
										bestUpperBound = upperBound;
										o.bestShapeID[d] = sid;
									}
									
								}
							}
						}

						assert minLowerBound > IntDomain.MinInt;
						assert maxUpperBound < IntDomain.MaxInt;

						if(minLowerBound < IntDomain.MaxInt ) {

							IntVar prunedVariable = d != dimension ? o.coords[d] : o.start;
							
							if(DEBUG_DOUBLE_LAYER)
								if(minLowerBound > prunedVariable.min())
									System.out.println("geost " + id() + " changing " + prunedVariable + " min bound to " + minLowerBound);
							
							prunedVariable.domain.inMin(store.level, prunedVariable, minLowerBound);

							if (oneTimeVarChanged) {
								o.timeConstraint.consistencyStartPlusDurationEqEnd(store);
							//	if(o.timeConstraint.consistencyStartPlusDurationEqEnd(store))
							//		//modification of some of the time variables, sweep again
							//		queueObject(o);
								oneTimeVarChanged = false;
							}
							
						} else 
							inconsistent = true;

						if(!inconsistent && maxUpperBound > IntDomain.MinInt) {
							
							IntVar prunedVariable = d != dimension ? o.coords[d] : o.end;
							
							if(DEBUG_DOUBLE_LAYER)
								if(maxUpperBound < prunedVariable.max())
										System.out.println("geost " + id() + " changing " + prunedVariable + " max bound to " + maxUpperBound);
							
							prunedVariable.domain.inMax(store.level, prunedVariable, maxUpperBound);

							if (oneTimeVarChanged) {
								o.timeConstraint.consistencyStartPlusDurationEqEnd(store);
							//	if(o.timeConstraint.consistencyStartPlusDurationEqEnd(store))
							//		//modification of some of the time variables, sweep again
							//		queueObject(o);
								oneTimeVarChanged = false;
							}							

						} else 
							inconsistent = true;
						
					}
				}
				
				if(inconsistent)
					throw Store.failException;

				if(DEBUG_MAIN){
					System.out.print("pruned " + o);
					System.out.println(""); //just to place breakpoint
				}


			}

			
			//backtracking data storage
			if (!updatedObjectSet.isEmpty()) {
		//	if(setStart.stamp() < store.level) {
			
				// TODO, think of easy way of preventing multiple objects being put to the list at the same level.
				//need to create the set for this level
				//flush last set
				for(GeostObject uo : updatedObjectSet)
					objectList.add(uo);
				
				updatedObjectSet.clear();

				//mark beginning of new set
				setStart.update(objectList.size());
				
				if(DEBUG_BACKTRACK)
					System.out.println("new set, begins at " + setStart.value() + ", stamp: " + setStart);
				
			} 

			
		} finally {

			inConsistency = false;
			variableQueue.clear();
			
			objectQueue.clear();
			// objectQueue.clear();//may not be empty if an exception was raised

		}
	}

	
	/**
	 * It is called whenever the object currently being pruned changes.
	 * useful for constraint pruning version of Geost.
	 * 
	 * @param o the object currently being pruned for which internal constraints are being filtered.
	 */
	protected void updateInternalConstraintsGeneratingOutboxes(GeostObject o) {
		
		if( filterUseless ) {

			//maximal possible size of the object
			workingList.clearNoGC();
			ValueEnumeration sids = o.shapeID.domain.valueEnumeration();
			
			while(sids.hasMoreElements())
				workingList.add(getShape(sids.nextElement()).boundingBox);
			
			// bb - boundingBox over all shapes.
			DBox bb = DBox.boundingBox(workingList).copyInto(DBox.newBox(dimension));

			
			// bounds of the domain and the bounding box over all possible shapes counted above.
			DBox domainBox = DBox.newBox(dimension + 1);
			int[] domainBoxOriginShifted = domainBox.origin; 
			int[] domainBoxLengthShifted = domainBox.length;

			for(int i = 0; i < dimension; i++) {
				domainBoxOriginShifted[i] = o.coords[i].min() + bb.origin[i];
				domainBoxLengthShifted[i] = o.coords[i].max() + bb.origin[i] + bb.length[i] - domainBoxOriginShifted[i];
			}
			//TODO cache the results of the computation above and recompute upon object change.
			
			domainBoxOriginShifted[dimension] = IntDomain.MinInt;
			domainBoxLengthShifted[dimension] = IntDomain.MaxInt*2;
			
			// it finds the box within which the constraint can propagate. 
			DBox constraintBox = DBox.newBox(dimension + 1);
			int[] constraintBoxOrigin = constraintBox.origin;
			int[] constraintBoxLength = constraintBox.length;
			
			lastConstraintToCheck = 0;
			for(InternalConstraint c : objectConstraints[o.no])
				if(c.cardInfeasible() > 0 ) { 
					
					//increase size by one unit because intersection is empty if of size zero
					int[] lowerBound = c.AbsInfeasible(Geost.SweepDirection.PRUNEMIN);
					for(int i = 0; i < dimension + 1; i++)
						constraintBoxOrigin[i] = lowerBound[i] - 1;
					
					//note: need to to them one after the other because of array reuse in absInfeasible
					int[] upperBound = c.AbsInfeasible(Geost.SweepDirection.PRUNEMAX);
					for(int i = 0; i < dimension+1; i++)
						constraintBoxLength[i] = upperBound[i] - constraintBoxOrigin[i] + 2;
					
					// if the constraint can propagate within current domains then the internal 
					// constraint can be useful and can not be filtered out, otherwise the constraint
					// is not added to the list of useful constraints.
					if(domainBox.intersectWith(constraintBox) != null) {
						stillUsefulInternalConstraints[lastConstraintToCheck] = c;
						lastConstraintToCheck++;
					}
					
				}
			
			DBox.dispatchBox(bb);
			DBox.dispatchBox(constraintBox);
			DBox.dispatchBox(domainBox);
			
		} else {
			
			lastConstraintToCheck = 0;
			for(InternalConstraint c : objectConstraints[o.no])
				if(c.cardInfeasible() > 0 ) {
					stillUsefulInternalConstraints[lastConstraintToCheck] = c;
					lastConstraintToCheck++;
				}

		}
		
		if(DEBUG_REORDER)
			System.out.println("changed pruning object");
		
	}

	
	/**
	 * It does the processing needed given the set of variables that was updated 
	 * between two consecutive calls to the consistency function.
	 * @param variables
	 */
	protected void flushQueue(Collection<Var> variables){
		
		objectList4Flush.clearNoGC();
		
		for(Var v : variables) {

			GeostObject o = variableObjectMap.get(v);

			if (o == null)
				// can be ignored as the variable was singleton upon imposition. 
				continue;

			//if it is a time variable, run time constraint
			if(v == o.start || v == o.end || v == o.duration) 
				o.timeConstraint.consistencyStartPlusDurationEqEnd(store);
			else if (v == o.shapeID)
				//some shape ID was changed by some external source, remember it
				changedShapeID = true;

			objectList4Flush.add(o);
		}

		for (GeostObject o : objectList4Flush)
			onObjectUpdate(o); 
	}

	/**
	 * It puts the object into the queue if it can be still pruned or cause failure.
	 * 
	 * @param o the object which is possibly put into the queue. 
	 * 
	 */
	final public void queueObject(GeostObject o){
		
		// Important to keep and ensure.
		assert (inConsistency) : "It is improperly called outside the consistency function.";
		
		if(!(o.isGrounded() && pruneIfGrounded[o.no] == false)) {
				
			if(DEBUG_OBJECT_GROUNDING)
				System.out.println("queued " + o);
					
			if(GATHER_STATS)
				queuedObjectCount++;
				
			objectQueue.add(o);
			
				
		} else if(DEBUG_OBJECT_GROUNDING)
				System.out.println("The object " + o + " was skipped.");
		
		
	}

	/**
	 * It performs the necessary operations for a given changed object.
	 * 
	 * If the change occurred due to backtracking then only external constraints
	 * are being informed about the change, so they can restore proper state in 
	 * connection to the object. If this function is not called during backtracking
	 * then also the following is executed.
	 * 
	 * If the change occurs due to search progress downwards then it stores 
	 * the information about object change as well as schedules pruning 
	 * check for all connected objects. 
	 *  
	 * @param o the object which had a domain change
	 */
	protected void onObjectUpdate(GeostObject o){
		
		if(GATHER_STATS)
			onObjectUpdateCount++;

		if(DEBUG_MAIN)
			System.out.println("adding objects to the queue");

		/**
		 * for now, all constraints are applied to all objects, so the set of objects
		 * connected by an external constraint to o is the whole set of objects
		 * (see technical report, page 12, last phrase in the algorithm caption)
		 * 
		 */		
		for(ExternalConstraint ec : externalConstraints)
			ec.onObjectUpdate(o);
		

		//no need to queue objects if backtracking
		if(!backtracking) {
						
			//add object to the set of this level
			updatedObjectSet.add(o);

			if(DEBUG_BACKTRACK)
				System.out.println("updating object " + o);
			
			if(allLinked) {
				//executing the else part would end up in the same result
				for(GeostObject lo : objects)
					queueObject(lo);
				
			} else {

				queueObject(o); // needed because if dimension 1 was pruned, dimension 0 might now be pruned

				temporaryObjectSet.clear();

				for(ExternalConstraint ec : externalConstraints) {

					ec.addPrunableObjects(o, temporaryObjectSet);	
					while (!temporaryObjectSet.isEmpty())
						queueObject ( temporaryObjectSet.removeFirst() );

				}					
				
			}
		}
		
	}

	@Override
	public int getConsistencyPruningEvent(Var var) {
		
		// If consistency function mode
		if (consistencyPruningEvents != null) {
			Integer possibleEvent = consistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}

		GeostObject o = variableObjectMap.get(var);
		
		if (o == null)
			return Domain.NONE;
		
		if (o.shapeID == var)
			return IntDomain.ANY;

		return IntDomain.BOUND;
		
	}

	@Override
	public String id() {
		
		if (id != null)
			return id;
		else
			return this.getClass().getSimpleName() + numberId;
	
	}

	@Override
	public void impose(Store store) {
		
		this.store = store;
		
		lastLevelLastVar = new TimeStamp<Integer>(store, store.level);
		lastLevelLastVar.update(0);
		
		genInternalConstraints();
		
		for(GeostObject o: objects)
			for(Var v : o.getVariables()) {
				v.putModelConstraint(this, getConsistencyPruningEvent(v));				
				queueVariable(store.level, v);
			}
		
		store.registerRemoveLevelListener(this);
		store.registerRemoveLevelLateListener(this);
		
		store.addChanged(this);
		store.countConstraint();

		setStart = new TimeStamp<Integer>(store, store.level);
		setStart.update(0);
		
		objectList = new SimpleArrayList<GeostObject>();
		updatedObjectSet = new HashSet<GeostObject>();
		
	}

	@Override
	public void increaseWeight() {

		if (increaseWeight)
			for(GeostObject o: objects)
				for(Var v : o.getVariables())
					v.weight++;			
		
	}
	

	private int currentLevel;

	/**
	 * It specifies the first position of the variables being removed 
	 * from grounded list upon backtracking. 
	 * 
	 * If there is no change in lastLevelVar.value between removeLevel (
	 * stored in removeLimit) and removeLevelLate then this indicates
	 * that no variable was grounded at removed level. 
	 * 
	 */
	private int removeLimit;
	
	@Override
	@SuppressWarnings("all")
	public void queueVariable(int level, Var v) {
		
		currentLevel = level;
		
		if(v.singleton()) {
			
			GeostObject o = variableObjectMap.get(v);
			
			if (o == null) {
				// can be ignored as the variable was singleton upon imposition. 
				return;
			}
			
			o.onGround(v);
			
			if(DEBUG_OBJECT_GROUNDING)
				System.out.println("grounding " + v);
			
			if(!inConsistency)
				pruneIfGrounded[o.no] = true;
			
			if(lastLevelLastVar.stamp() < store.level)
				lastLevelLastVar.update( groundedVars.size() );
			
			groundedVars.add(v);
		}
		
		if(inConsistency) {
			
			assert (variableObjectMap.containsKey(v) || v.singleton() )
				: "The variable " + v + " does not exist in variable-object map.";
			
			//if this variable can modify the sweep result, process it right away
			GeostObject o = variableObjectMap.get(v);

			if (o == null) {
				// can be ignored as the variable was singleton upon imposition. 
				return;
			}

			//if it is a time variable, run time constraint
			if(v == o.start || v == o.end || v == o.duration)
				oneTimeVarChanged = true;
			
							
			onObjectUpdate(o);
			
		} else {
			// keep it for later
			variableQueue.add(v);
		}
		
		
		if(DEBUG_VAR_SKIP || DEBUG_OBJECT_GROUNDING)
			if(inConsistency)
				System.out.println("The variable " + v + " was pruned by geost consistency function itself");
			else 
				System.out.println("The variable " + v + " was pruned by outside constraints and it is queued as changed within geost");
			
		
	}

	@Override
	public void removeConstraint() {
		
		for(GeostObject o: objects)
			for(Var v : o.getVariables())
				v.removeConstraint(this);
			
		
	}

	
	@Override
	@SuppressWarnings("all")
	public void removeLevel(int level) {
		
		// added.
		if (level > currentLevel)
			return;
		
		if(DEBUG_MAIN || DEBUG_SHAPE_SKIP || DEBUG_VAR_SKIP || DEBUG_OBJECT_GROUNDING)
			System.out.println("removeLevel(" + store.level + ")");		
		
		assert !inConsistency;
		
		if (firstConsistencyLevel == level)
			firstConsistencyCheck = true;

		removeLimit = lastLevelLastVar.value();

	//	lowerBound = setStart.value();
	}
	
	@Override
	public void removeLevelLate(int level) {

		assert !inConsistency;
		
		// added. to mask a bug if multiple remove levels are being executed for the same level.
		if (level > currentLevel)
			return;

		if (lastLevelLastVar.value() < removeLimit)
			for(int i = groundedVars.size() - 1; i >= removeLimit; i--) {

				Var v = groundedVars.remove(i);
				assert v!= null;

				if(DEBUG_OBJECT_GROUNDING)
					System.out.println("The variable " + v + " is being ungrounded");

				// no need to check for null as only not null variables are put in groundedVars.
				variableObjectMap.get(v).onUnGround(v);
			}

		backtracking = true;
				
		if( !updatedObjectSet.isEmpty() )
			for(GeostObject o : updatedObjectSet) {
				
				onObjectUpdate(o);
				if(DEBUG_BACKTRACK)
					System.out.println("restored object " + o);
			}
		
		updatedObjectSet.clear();

		int lowerBound = setStart.value();
		for(int i = objectList.size() - 1; i >= lowerBound; i--) {
			
			GeostObject o = objectList.remove(i);
			
			assert o != null;
			
		//	if(!updatedObjectSet.contains(o))
		//		// else it was already updated
			onObjectUpdate(o);

			if(DEBUG_BACKTRACK)
				System.out.println("restored object " + o);
			
		}

		/**
		 * It is cleared out as the objects changed at the level being removed are no longer needed.
		 */
		// updatedObjectSet.clear();
		
		backtracking = false;
		
	}

	/**
	 * Geost is satisfied if all of its external constraints are satisfied.
	 */
	@Override
	public boolean satisfied() {
		
		if (variableObjectMap.size() != groundedVars.size())
			return false;
		
		return true;
	}

	@Override
	public String toString() {
		//TODO, proper string representation of the constraint.
		return "Geost";
	}

	
	/**
	 * It returns all the statistics gathered by geost constraint during the search.
	 * 
	 * @return an array list consisting of different statistics collected during search.
	 */
	public List<Long> getStatistics(){

		ArrayList<Long> stats =  new ArrayList<Long>();
		
		stats.add(pruneMinCount);
		stats.add(pruneMaxCount);
		stats.add(findForbiddenDomainCount);
		stats.add(isFeasibleCount);
		stats.add(onObjectUpdateCount);
		stats.add(queuedObjectCount);
		stats.add(filteredConstraintCount);
		
		return stats;
	
	}
	
	/**
	 * @author Marc-Olivier Fleury and Radoslaw Szymanek
	 * 
	 * It specifies in what direction the sweep algorithm is progressing.
	 */
	
	public enum SweepDirection {
		/**
		 * The sweep algorithm prunes the minimal values for the origins.
		 */
		PRUNEMIN,
		/**
		 * The sweep algorithm prunes the maximal values for the origins.
		 */
		PRUNEMAX
	}
	
	
}
