/*
 * Geost.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.constraints.geost;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import lombok.extern.slf4j.Slf4j;
import org.jacop.api.RemoveLevelLate;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.constraints.Constraint;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * Geost constraint for handling geometric placement problems.
 *
 * <p>1) DONE. FlushAndQueue function should be changed and some functionality moved to
 * firstConsistencyCheck.
 *
 * <p>2) DONE. No propagation inside queueVariable function.
 *
 * <p>3) DONE. How to incorporate GUI code within Geost constraint.
 *
 * <p>4) DONE. Move part of the functionality of onObjectUpdate to consistency function.
 *
 * <p>5) Refactor use of TimeBoundConstraint 5b) DONE. remove runTimeConstraint boolean variable.
 *
 * <p>6) DONE. asserts for Shape register 6b) asserts about possible values of MaxInt and MinInt.
 *
 * <p>7) DONE. Use simpleHashSet instead of LinkedHashSet for objectQueue.
 *
 * <p>8) DONE. Discuss pruning events, do we really need ANY for all variables? For example, maybe
 * time variables always BOUND pruning event.
 *
 * <p>9) DONE. Simplify queueObject by removing if statements and make sure that this function is
 * being called properly (avoid non-asserts checks inside it).
 *
 * <p>10) DONE. Discuss the possible implementation of satisfied function.
 *
 * <p>11) Introduce time switch so geost can work without time dimension.
 *
 * <p>12) Lessen the feature of geost that it does not work with variables used multiple times
 * within different objects 12b) DONE. (at least for singleton variables).
 *
 * <p>13) DONE. Verify fix to address bug in case of multiple level removals, or level removals for
 * which no consistency function has been called. Functionality around variable currentLevel. It is
 * still needed.
 *
 * <p>14. DONE. Fixing a bug connected with timestamps and multiple remove levels calls. 14b Check
 * lastLevelVar (possibly needs to be done similarly as setStart).
 *
 * <p>Future Work :
 *
 * <p>1. InArea should support subset of objects and dimensions.
 *
 * <p>2. Reuse previously generated outboxes. Create a function to create a hashkey from points
 * coordinates for which an outbox is required. Later, for each new point we check if we have proper
 * outbox for a given hash-key generated from this outbox.
 *
 * <p>3. Not always finishing at consistency fixpoint, speculative fixpoint.
 *
 * <p>4. consider polymorphism due to rotations only, and see if better performance can be reached
 * under this assumption.
 *
 * <p>5. If objects have the same shape, and they are indistingushable then symmetry breaking can be
 * employed.
 *
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
@SuppressWarnings("PointlessBooleanExpression")
public class Geost extends Constraint implements UsesQueueVariable, Stateful, RemoveLevelLate {

  /**
   * It specifies different debugging switches to print out diverse information about execution of
   * the geost constraint.
   */
  static final boolean DEBUG_ALL = false;

  static final boolean DEBUG_MAIN = DEBUG_ALL || false;

  static final boolean DEBUG_SUBSETS = DEBUG_ALL || false;

  static final boolean DEBUG_DOUBLE_LAYER = DEBUG_ALL || false;

  static final boolean DEBUG_SHAPE_SKIP = DEBUG_ALL || false;

  static final boolean DEBUG_VAR_SKIP = DEBUG_ALL || false;

  static final boolean DEBUG_OBJECT_GROUNDING = DEBUG_ALL || false;

  static final boolean DEBUG_BACKTRACK = DEBUG_ALL || false;

  static final boolean GATHER_STATS = true;

  static final boolean DEBUG_REORDER = false;

  /** It specifies the unique number used to differentiate geost constraints. */
  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It specifies the order between dimensions which is used by the pruning algorithm. The order may
   * have influence on the algorithm efficiency. The geost constraint chooses the order based on
   * average length of objects in the particular dimension. The dimension with higher average length
   * in this dimension will have the preference.
   */
  final LexicographicalOrder order;

  /**
   * It specifies that filtering of useless internal constraint takes place before an object is
   * being pruned. It may be costly for small instances.
   */
  final boolean filterUseless = true;

  /**
   * It stores the reference to the collection of objects provided to the constructor. It does not
   * perform cloning so the collection can not change after geost constraint was imposed.
   */
  final GeostObject[] objects;

  /**
   * It stores the reference to the collection of external constraints which must be satisfied
   * within this constraint. This is a reference to the collection provided within the constructor.
   * No copying is employed therefore the collection can not change even after the constraint is
   * imposed.
   */
  final ExternalConstraint[] externalConstraints;

  /**
   * It stores information about shapes used by objects within this geost constraint. It is based on
   * shapes information provided in the constructor.
   */
  final Shape[] shapeRegister;

  /** If set to true, a variable will never be skipped, even if grounded and not in queue. */
  final boolean enforceNoSkip =
      true; // setting to false is causing a bug that allows incorrect solution to be accepted.

  /** Set to false to disable relaxed shape pruning. */
  final boolean partialShapeSweep = true;

  /**
   * It defines whether outbox generation should always rely on overlapping frames. For problems
   * that contain objects that have small domains compared to their size, then using only frames may
   * provide a better performance (up to 50% faster). It can only be changed before impose()
   * function, changing it afterwards will lead to improper behavior.
   */
  final boolean alwaysUseFrames = false;

  /**
   * It specifies for each object if consistency function should be run if this object becomes
   * grounded. It is set to true if the object was grounded outside consistency function call or
   * after a shape variable has been changed. It is set to false only after exactly one consistency
   * check during which the object was grounded.
   */
  final boolean[] pruneIfGrounded;

  /** It maps any variable in the scope of the geost constraint to the object it belongs to. */
  final Map<Var, GeostObject> variableObjectMap;

  /**
   * It is a locally used array which stores the enumeration of values for the current shape
   * variable. The enumeration is lexicographical with one exception the previously found best shape
   * is put on the first position.
   */
  final int[] shapeIdsToPrune;

  /**
   * It stores the special constraints responsible for the handling of holes in the domain. It is
   * indexed by object id.
   */
  final DomainHoles[] domainHolesConstraints;

  /** A preallocated array of ints used extensively within sweeping algorithm. */
  final int[] c;

  /** A preallocated array of ints used extensively within sweeping algorithm. */
  final int[] n;

  /**
   * It stores all variables which have been grounded. It is used to upon backtracking to update
   * objects to their previous state.
   */
  final ArrayList<Var> groundedVars;

  /**
   * If running a complete sweep for each shape is costly, because some shapes may require a
   * significant sweep, even though a weaker bound has already been found. However, to be able to
   * prune shapes, such a costly sweep needs to be done. A tradeoff solution consists in running a
   * complete sweep for each shape once per node, and optimize the following runs. This implies
   * remembering which object have already been fully pruned.
   */
  final boolean[] fullyPruned;

  /**
   * It stores temporarily objects for which pruning is suggested by external constraints. The geost
   * constraint checks every object from this set to see if that is actually necessary to invoke the
   * pruning for that object.
   */
  final LinkedHashSet<GeostObject> temporaryObjectSet;

  /**
   * A temporary list to collect bounding boxes for each shape of the given object to compute one
   * bounding box whatever the shape of the object. It is made as a member of the geost constraint
   * to avoid multiple memory allocations.
   */
  final ArrayList<Dbox> workingList;

  /** It specifies the number of dimensions of each object given to the geost constraint. */
  final int dimension;

  /**
   * It is used inside flushQueue function to separate timeconsistency execution from object update
   * (potentially expensive if for example object frame is recomputed).
   */
  final ArrayList<GeostObject> objectList4Flush = new ArrayList<>();

  /**
   * It stores all generated internal constraints for all objects/constraints. It is used to speed
   * up some visualization functions. If not for that reason it could have been a local variable
   * within a function generating internal constraints.
   */
  public Collection<InternalConstraint> internalConstraints;

  /**
   * It is a flag set to true during remove level late function execution so objects which are being
   * updated upon backtracking can be handled properly.
   */
  boolean backtracking;

  /** It keeps a reference to the store. */
  protected Store store;

  /**
   * It counts how many constraints we discounted in outbox generation procedure as not useful ones.
   */
  long filteredConstraintCount;

  /**
   * It counts the number of times the minimum values of geost objects origins are being examined
   * for pruning.
   */
  long pruneMinCount;

  /**
   * It counts the number of times the minimum values of geost objects origins are being examined
   * for pruning. It may be different (smaller than) prunedMinCount as constraint may have failed
   * during min domain pruning.
   */
  long pruneMaxCount;

  /** It counts number of executions of outboxes generation. */
  long findForbiddenDomainCount;

  /** It counts the number of object updates. */
  long onObjectUpdateCount;

  /**
   * It counts how many times the feasibility check is being performed by internal constraint on a
   * supplied point.
   */
  long isFeasibleCount;

  /** It counts how many times the object has been queued. */
  long queuedObjectCount;

  /** It indicates whether we are currently running the consistency function or not. */
  boolean inConsistency;

  /**
   * If equal to true then modifying one object implies that all objects have to be added to object
   * queue.
   */
  boolean allLinked;

  /**
   * It is used to signal that some shape ID was pruned. It is required because pruning skip
   * condition (var grounded, and not in the queue) can only be safely used if no shape id field was
   * pruned. Indeed, if some shape ID was pruned, feasibility can change, thus a check is needed.
   */
  boolean changedShapeId;

  /**
   * It remembers if it is the first time the consistency check is being performed. If not, then the
   * initial consistency checks which have to be done only once will be done during the first
   * consistency check. This flag is set back to true if the remove level function is removing the
   * level onto which the changes caused by the initial consistency were applied to.
   */
  boolean firstConsistencyCheck;

  /**
   * It remembers the level at which the consistency function was applied for the first time. If
   * that level is being removed then the initial consistency function must be executed again.
   */
  int firstConsistencyLevel;

  /**
   * It stores all variables which have changed outside the consistency function of this constraint.
   */
  LinkedHashSet<Var> variableQueue;

  /** It stores the position of the last variable grounded in the previous level. */
  TimeStamp<Integer> lastLevelLastVar;

  /** It contains all the objects which have been updated in the previous levels. */
  ArrayList<GeostObject> objectList;

  /**
   * It contains all the objects which have been updated at current level. The objects from this set
   * are moved to the array objectList as soon as level is increased. If level is being removed then
   * for every object in this set we inform the external constraints that their state in connection
   * to this object may have changed.
   */
  Set<GeostObject> updatedObjectSet;

  /**
   * It stores the index of the first object which have changed at current level. It allows to
   * inform the external constraints about objects being changed due to backtracking.
   */
  TimeStamp<Integer> setStart;

  /** It contains objects that need to be checked in the next sweep. */
  LinkedHashSet<GeostObject> objectQueue;

  /**
   * For each object, the set of constraint that apply to it we use object ids as keys, and can thus
   * use an array to store the map. This is the input set to the filtering process before pruning
   * any object.
   */
  Set<InternalConstraint>[] objectConstraints;

  /**
   * It contains all not filtered out, useful internal constraints which should be used to generate
   * outboxes. The initial array of internal constraints associate with a given object being pruned
   * can be significantly shrank and the remaining objects (still useful) are store in this array.
   */
  InternalConstraint[] stillUsefulInternalConstraints;

  /** It specifies the last useful constraint in the array of useful internal constraints. */
  int lastConstraintToCheck;

  /**
   * It is set by queueVariable after a time variable has been changed. It indicates that we should
   * run the consistency function of the time constraint.
   */
  private boolean oneTimeVarChanged;

  private int currentLevel;

  /**
   * It specifies the first position of the variables being removed from grounded list upon
   * backtracking.
   *
   * <p>If there is no change in lastLevelVar.value between removeLevel ( stored in removeLimit) and
   * removeLevelLate then this indicates that no variable was grounded at removed level.
   */
  private int removeLimit;

  @SuppressWarnings("all")
  public Geost(
      Collection<GeostObject> objects,
      Collection<ExternalConstraint> constraints,
      Collection<Shape> shapes) {
    this(
        objects.toArray(new GeostObject[objects.size()]),
        constraints.toArray(new ExternalConstraint[constraints.size()]),
        shapes.toArray(new Shape[shapes.size()]));
  }

  /**
   * It creates a geost constraint from provided objects, external constraints, as well as shapes.
   * The construct parameters are not cloned so do not reuse them in creation in other constraints
   * if changes are necessary. Make sure that the largest object id is as small as possible to avoid
   * unnecessary memory cost.
   *
   * @param objects objects in the scope of the geost constraint.
   * @param constraints the collection of external constraints enforced by geost.
   * @param shapes the list of different shapes used by the objects in scope of the geost.
   */
  @SuppressWarnings("unchecked")
  public Geost(GeostObject[] objects, ExternalConstraint[] constraints, Shape[] shapes) {

    checkInputForDuplicationSkipSingletons(
        "objects",
        Arrays.stream(objects).flatMap(obj -> obj.getVariables().stream()).toArray(IntVar[]::new));

    if (ASSERTS_ENABLED && objects.length <= 0) {
      throw new IllegalStateException(String.valueOf("empty collection of objects"));
    }
    if (ASSERTS_ENABLED && shapes.length <= 0) {
      throw new IllegalStateException(String.valueOf("empty collection of shapes"));
    }
    if (ASSERTS_ENABLED && constraints.length <= 0) {
      throw new IllegalStateException(String.valueOf("empty collection of constraints"));
    }

    this.queueIndex = 2;
    this.objects = objects.clone();
    this.externalConstraints = constraints.clone();
    this.numberId = idNumber.incrementAndGet();
    this.variableQueue = new LinkedHashSet<>();
    objectQueue = new LinkedHashSet<>(objects.length);
    objectQueue.addAll(Arrays.asList(objects));

    Map<Integer, Shape> idShapeMap = buildIdShapeMap(shapes);
    int[] dimAndIdMax = validateObjectsAndGetDimension(objects, idShapeMap);
    dimension = dimAndIdMax[0];
    int idMax = dimAndIdMax[1];

    objectConstraints = new Set[idMax + 1];
    domainHolesConstraints = new DomainHoles[idMax + 1];
    pruneIfGrounded = new boolean[idMax + 1];
    Arrays.fill(pruneIfGrounded, false);
    shapeRegister = buildShapeRegisterArray(idShapeMap);
    fullyPruned = partialShapeSweep ? new boolean[idMax + 1] : null;

    Dbox.supportDimension(dimension);
    Dbox.supportDimension(dimension + 1);
    shapeIdsToPrune = new int[shapeRegister.length];

    if (ASSERTS_ENABLED && dimension <= 0) {
      throw new IllegalStateException(String.valueOf("No dimensions"));
    }

    c = new int[dimension + 1];
    n = new int[dimension + 1];

    double[] averageSizes = computeAverageSizes(objects);
    order = new PredefinedOrder(computeDimensionOrdering(averageSizes), 0);

    variableObjectMap = Var.createEmptyPositioning();
    buildVariableObjectMap(objects);

    inConsistency = false;
    temporaryObjectSet = new LinkedHashSet<>();
    backtracking = false;
    workingList = new ArrayList<>();
    if (ASSERTS_ENABLED && checkInvariants() != null) {
      throw new IllegalStateException(String.valueOf(checkInvariants()));
    }
    groundedVars = new ArrayList<>();
    setScope(variableObjectMap.keySet());
  }

  private static Shape[] buildShapeRegisterArray(Map<Integer, Shape> idShapeMap) {
    Shape[] register = new Shape[idShapeMap.size()];
    for (Map.Entry<Integer, Shape> e : idShapeMap.entrySet()) {
      if (ASSERTS_ENABLED && e.getKey() >= idShapeMap.size()) {
        throw new IllegalStateException(
            String.valueOf(
                "Shapes do not have unique ids between 0 and n-1, where n is number of shapes."));
      }
      register[e.getKey()] = e.getValue();
    }
    return register;
  }

  private double[] computeAverageSizes(GeostObject[] objects) {
    int[] shapeNb = new int[shapeRegister.length];
    int totShapes = 0;
    double[] averageSizes = new double[dimension + 1];
    Arrays.fill(shapeNb, 0);

    for (GeostObject o : objects) {
      ValueEnumeration vals = o.shapeId.domain.valueEnumeration();
      while (vals.hasMoreElements()) {
        shapeNb[vals.nextElement()]++;
        totShapes++;
      }
      averageSizes[dimension] += o.end.max() - o.start.min();
    }

    for (int i = 0; i < shapeRegister.length; i++) {
      for (int j = 0; j < averageSizes.length - 1; j++) {
        averageSizes[j] += shapeRegister[i].boundingBox.length[j] * shapeNb[i];
      }
    }

    for (int j = 0; j < averageSizes.length - 1; j++) {
      averageSizes[j] /= totShapes;
    }
    averageSizes[dimension] /= objects.length;
    return averageSizes;
  }

  private int[] computeDimensionOrdering(double[] averageSizes) {
    int[] ordering = new int[dimension + 1];
    for (int i = 0; i < ordering.length; i++) {
      double smallestYet = Double.MAX_VALUE;
      int smallestIndex = 0;
      for (int j = 0; j < ordering.length; j++) {
        if (averageSizes[j] < smallestYet) {
          smallestYet = averageSizes[j];
          smallestIndex = j;
        }
      }
      ordering[i] = smallestIndex;
      averageSizes[smallestIndex] = Double.MAX_VALUE;
    }
    return ordering;
  }

  private void buildVariableObjectMap(GeostObject[] objects) {
    for (GeostObject o : objects) {
      for (Var v : o.getVariables()) {
        if (!v.singleton()) {
          GeostObject previousValue = variableObjectMap.put(v, o);
          if (ASSERTS_ENABLED && previousValue != null) {
            throw new IllegalStateException(
                String.valueOf(
                    "Current implementation of Geost does not allow reuse of not singleton variables."));
          }
        }
      }
    }
  }

  private static Map<Integer, Shape> buildIdShapeMap(Shape[] shapes) {
    Map<Integer, Shape> idShapeMap = new HashMap<>();
    for (Shape s : shapes) {
      if (s.no < 0) {
        throw new IllegalArgumentException("shape ID has to be positive");
      }
      idShapeMap.put(s.no, s);
    }
    return idShapeMap;
  }

  private static int[] validateObjectsAndGetDimension(
      GeostObject[] objects, Map<Integer, Shape> idShapeMap) {
    Set<Integer> objectIds = new HashSet<>();
    int dim = -1;
    int idMax = 0;
    for (GeostObject o : objects) {
      if (objectIds.contains(o.no)) {
        throw new IllegalArgumentException("all objects must have a different ID");
      }
      if (o.no < 0) {
        throw new IllegalArgumentException("object ID has to be positive");
      }
      objectIds.add(o.no);
      idMax = Math.max(o.no, idMax);

      if (dim == -1) {
        dim = o.dimension;
      } else if (dim != o.dimension) {
        throw new IllegalArgumentException("all objects must have the same number of dimensions");
      }

      ValueEnumeration shapeIdVals = o.shapeId.domain.valueEnumeration();
      while (shapeIdVals.hasMoreElements()) {
        int sid = shapeIdVals.nextElement();
        if (!idShapeMap.containsKey(sid)) {
          throw new IllegalArgumentException(
              "shape id " + sid + " does not correspond to any shape");
        }
      }
    }
    return new int[] {dim, idMax};
  }

  /**
   * It checks that this constraint has consistent data structures.
   *
   * @return a string describing the consistency problem with data structures, null if no problem
   *     encountered.
   */
  public String checkInvariants() {

    if (order == null) {
      return "lexical order is null";
    }
    if (variableQueue == null) {
      return "variable queue is null";
    }
    if (objectQueue == null) {
      return "object queue is null";
    }
    if (c.length != n.length) {
      return "c and n must have the same size";
    }
    if (objects.length == 0) {
      return "empty collection of objects";
    }
    if (externalConstraints.length == 0) {
      return "empty collection of constraints";
    }

    return null;
  }

  /**
   * It returns the shape with a given id if such exists.
   *
   * @param id the unique id of the shape we are looking for.
   * @return the shape of a given id previously provided.
   */
  public final Shape getShape(int id) {

    if (ASSERTS_ENABLED && (id < 0 || id >= shapeRegister.length || shapeRegister[id] == null)) {
      throw new IllegalStateException(String.valueOf("unknown shape id: " + id));
    }

    return shapeRegister[id];
  }

  /** Generates internal constraints from external constraints and initializes data structures. */
  protected void genInternalConstraints() {

    internalConstraints = new ArrayList<>();

    int constraintCount = 0;

    for (ExternalConstraint ec : externalConstraints) {

      final Collection<InternalConstraint> ics = ec.genInternalConstraints(this);

      // prepare all data structures
      for (GeostObject o : objects) {
        ec.onObjectUpdate(o);
      }

      internalConstraints.addAll(ics);

      constraintCount += ics.size();
    }

    if (ASSERTS_ENABLED && constraintCount != internalConstraints.size()) {
      throw new IllegalStateException(String.valueOf("some constraints were not added correctly"));
    }

    // initialize array used to stored filtered constraints. Has to be large enough to store all
    // constraints
    stillUsefulInternalConstraints = internalConstraints.toArray(new InternalConstraint[0]);

    // find out if all constraints apply on the whole collection of objects
    Set<Object> scope = new HashSet<>();
    allLinked = computeAllLinked(scope);

    if (allLinked && scope.size() != objects.length) {
      // may appear if only one constraint applies to a subset of objects
      allLinked = false;
    }

    setupDomainHolesAndObjectConstraints();
  }

  /**
   * Determines whether all external constraints apply to the whole collection of objects.
   *
   * @param scope set to accumulate constraint scopes (modified by this method)
   * @return true if all constraints are linked to the full object set so far
   */
  private boolean computeAllLinked(Set<Object> scope) {
    for (ExternalConstraint ec : externalConstraints) {
      GeostObject[] constraintScope = ec.getObjectScope();

      if (constraintScope != null) {
        int prevSize = scope.size();
        List<GeostObject> constraintScopeArr = new ArrayList<>(constraintScope.length);
        constraintScopeArr.addAll(Arrays.asList(constraintScope));
        boolean changed = scope.addAll(constraintScopeArr);

        if (changed && prevSize != 0) {
          return false;
        }
      }
    }
    return true;
  }

  /** Initializes domain holes constraints and per-object constraint sets depending on allLinked. */
  private void setupDomainHolesAndObjectConstraints() {
    if (!allLinked) {
      for (GeostObject o : objects) {
        domainHolesConstraints[o.no] = new DomainHoles(o);
        Set<InternalConstraint> relatedConstraints = new HashSet<>();
        for (ExternalConstraint ec : externalConstraints) {
          relatedConstraints.addAll(ec.getObjectConstraints(o));
        }
        objectConstraints[o.no] = relatedConstraints;
      }
    } else {
      Set<InternalConstraint> commonConstraints = new HashSet<>(internalConstraints);
      for (GeostObject o : objects) {
        domainHolesConstraints[o.no] = new DomainHoles(o);
        objectConstraints[o.no] = commonConstraints;
      }
    }
  }

  /**
   * The sweeping routine for minimal bounds. Since in the polymorphic case, it is run for each
   * possible shape, and only the weakest result is used, it cannot have side-effects. In
   * particular, it cannot directly update domain values. If any data structure is updated here,
   * make sure that it is done carefully enough.
   *
   * @param store the store
   * @param o the object to prune
   * @param currentShape the shape of the object
   * @param d the current most significant dimension
   * @param limit stop pruning if going beyond this value
   * @return the bound found if there is one, and Constants.MaxInt if there is no feasible
   *     placement.
   */
  protected int pruneMin(
      Store store,
      GeostObject o,
      int currentShape,
      int d,
      //        Set<InternalConstraint> I,
      int limit) {

    if (DEBUG_MAIN) {
      log.debug("pruneMin");
    }

    order.setMostSignificantDimension(d);
    initializePruneMinBounds(o);

    if (DEBUG_MAIN) {
      log.debug("shape ID in pruneMin: {}", currentShape);
      log.debug("inital, c and n:");
      log.debug("c:{}", Arrays.toString(c));
      log.debug("n:{}", Arrays.toString(n));
    }

    boolean feasiblePointFound = true;
    Geost.SweepDirection dir = Geost.SweepDirection.PRUNEMIN;
    Dbox f;

    while (feasiblePointFound
        && (f = findForbiddenDomain(o, currentShape, c, dir, order)) != null) {

      if (ASSERTS_ENABLED && !f.containsPoint(c)) {
        throw new IllegalStateException(String.valueOf("bad forbidden region, c is not contained"));
      }
      updateNFromForbiddenBoxPruneMin(o, f);
      feasiblePointFound = advanceToNextFeasiblePointPruneMin(o, d);

      if (c[d] >= limit) {
        return limit;
      }

      if (DEBUG_MAIN) {
        log.debug("outbox found, c and n:");
        log.debug("c:{}", Arrays.toString(c));
        log.debug("n:{}", Arrays.toString(n));
      }
    }

    if (feasiblePointFound) {
      if (ASSERTS_ENABLED && c[d] < (d != dimension ? o.coords[d].min() : o.start.min())) {
        throw new IllegalStateException(
            String.valueOf(
                "feasible point found "
                    + c[d]
                    + " is outside domain "
                    + (d != dimension ? o.coords[d] : o.start)));
      }
      return c[d];
    } else {
      return IntDomain.MAX_INT;
    }
  }

  private void initializePruneMinBounds(GeostObject o) {
    final int size = o.dimension;
    for (int i = 0; i < size; i++) {
      c[i] = o.coords[i].min();
      n[i] = o.coords[i].max() + 1;
    }
    c[dimension] = o.start.min();
    n[dimension] = o.start.max() + 1;
  }

  private void updateNFromForbiddenBoxPruneMin(GeostObject o, Dbox f) {
    final int size1 = o.dimension + 1;
    for (int i = 0; i < size1; i++) {
      n[i] = Math.min(n[i], f.origin[i] + f.length[i]);
      if (ASSERTS_ENABLED && n[i] <= c[i]) {
        throw new IllegalStateException(String.valueOf("n is not larger than c in pruneMin"));
      }
    }
  }

  private boolean advanceToNextFeasiblePointPruneMin(GeostObject o, int d) {
    for (int i = o.dimension; i >= 0; i--) {
      int lexI = order.dimensionAt(i);
      final int domainMin = lexI != dimension ? o.coords[lexI].min() : o.start.min();
      final int domainMax = lexI != dimension ? o.coords[lexI].max() : o.start.max();
      c[lexI] = n[lexI];
      n[lexI] = domainMax + 1;
      if (c[lexI] <= domainMax) {
        return true;
      }
      c[lexI] = domainMin;
    }
    return false;
  }

  /**
   * The sweeping routine for minimal bounds. Since in the polymorphic case, it is run for each
   * possible shape, and only the weakest result is used, it cannot have side-effects. In
   * particular, it cannot directly update domain values. If any data structure is updated here,
   * make sure that it is done carefully enough.
   *
   * @param store the store
   * @param o the object to prune
   * @param d the current most significant dimension
   * @param currentShape the shape of the object
   * @param limit stop pruning if going beyond this value
   * @return the bound found if there is one, and Constants.MinInt if there is no feasible
   *     placement.
   */
  protected int pruneMax(
      Store store,
      GeostObject o,
      int currentShape,
      int d,
      //          Set<InternalConstraint> I,
      int limit) {

    if (DEBUG_MAIN) {
      log.debug("pruneMax");
    }

    order.setMostSignificantDimension(d);
    initializePruneMaxBounds(o);

    if (DEBUG_MAIN) {
      log.debug("shape ID in pruneMax: {}", currentShape);
      log.debug("initial c and n:");
      log.debug("c:{}", Arrays.toString(c));
      log.debug("n:{}", Arrays.toString(n));
    }

    boolean feasiblePointFound = true;
    Geost.SweepDirection dir = Geost.SweepDirection.PRUNEMAX;
    Dbox f;
    while (feasiblePointFound
        && (f = findForbiddenDomain(o, currentShape, c, dir, order)) != null) {

      if (ASSERTS_ENABLED && !f.containsPoint(c)) {
        throw new IllegalStateException(String.valueOf("bad forbidden region, c is not contained"));
      }
      updateNFromForbiddenBoxPruneMax(o, f);
      feasiblePointFound = advanceToNextFeasiblePointPruneMax(o, d);

      if (c[d] <= limit) {
        return limit;
      }

      if (DEBUG_MAIN) {
        log.debug("outbox found, c and n:");
        log.debug("c:{}", Arrays.toString(c));
        log.debug("n:{}", Arrays.toString(n));
      }
    }

    if (feasiblePointFound) {
      if (ASSERTS_ENABLED && c[d] > (d != dimension ? o.coords[d].max() : o.end.max())) {
        throw new IllegalStateException(
            String.valueOf(
                "feasible point found "
                    + c[d]
                    + " is outside domain "
                    + (d != dimension ? o.coords[d] : o.end)));
      }
      return c[d];
    } else {
      return IntDomain.MIN_INT;
    }
  }

  private void initializePruneMaxBounds(GeostObject o) {
    final int size2 = o.dimension;
    for (int i = 0; i < size2; i++) {
      c[i] = o.coords[i].max();
      n[i] = o.coords[i].min() - 1;
    }
    c[dimension] = o.end.max();
    n[dimension] = o.end.min() - 1;
  }

  private void updateNFromForbiddenBoxPruneMax(GeostObject o, Dbox f) {
    final int size3 = o.dimension + 1;
    for (int i = 0; i < size3; i++) {
      n[i] = Math.max(n[i], f.origin[i] - 1);
      if (ASSERTS_ENABLED && n[i] >= c[i]) {
        throw new IllegalStateException(String.valueOf("n is not smaller than c in pruneMax"));
      }
    }
  }

  private boolean advanceToNextFeasiblePointPruneMax(GeostObject o, int d) {
    for (int i = o.dimension; i >= 0; i--) {
      int lexI = order.dimensionAt(i);
      final int domainMin = lexI != dimension ? o.coords[lexI].min() : o.end.min();
      final int domainMax = lexI != dimension ? o.coords[lexI].max() : o.end.max();
      c[lexI] = n[lexI];
      n[lexI] = domainMin - 1;
      if (c[lexI] >= domainMin) {
        return true;
      }
      c[lexI] = domainMax;
    }
    return false;
  }

  /**
   * Finds a forbidden domain (outbox) for the given object at the specified point.
   *
   * @param o the object being pruned
   * @param currentShape the shape id of the object
   * @param point the point coordinates to check
   * @param dir the sweep direction
   * @param order the lexicographical order for dimensions
   * @return a Dbox representing the forbidden domain, or null if the point is feasible
   */
  protected Dbox findForbiddenDomain(
      GeostObject o,
      int currentShape,
      int[] point,
      //        Collection<InternalConstraint> constraints,
      Geost.SweepDirection dir,
      LexicographicalOrder order) {

    if (DEBUG_MAIN) {
      log.debug("shape ID in findForbiddenDomain: {}", currentShape);
    }

    if (GATHER_STATS) {
      findForbiddenDomainCount++;
    }

    // if there are holes in the domain, consider these first
    DomainHoles holeConstraint = domainHolesConstraints[o.no];

    if (DomainHoles.DEBUG) {
      log.debug("checking for holes of object {}", o);
      log.debug("associated constraint: {}", holeConstraint);
    }

    // If the hole within domain can be used to generate the outbox then it is checked first.
    if (holeConstraint.stillHasHole()) {

      if (GATHER_STATS) {
        isFeasibleCount++;
      }

      Dbox f = holeConstraint.isFeasible(dir, order, o, currentShape, point);

      if (f != null) {
        return f;
      }
    }

    if (GATHER_STATS) {
      // BUG?
      // length is not ok to use since this array is allocated initially based on the count of
      // ALL internal constraints for all objects and not the internal constraints associated with
      // a given object. Should be objectConstraints[o.id].size() ?
      filteredConstraintCount += stillUsefulInternalConstraints.length - lastConstraintToCheck;
    }

    // then go on with the standard filtered constraints
    for (int ci = lastConstraintToCheck - 1; ci >= 0; ci--) {

      final InternalConstraint c = stillUsefulInternalConstraints[ci];

      if (GATHER_STATS) {
        isFeasibleCount++;
      }

      Dbox f = c.isFeasible(dir, order, o, currentShape, point);

      if (f != null) {
        return f;
      }
    }

    return null;
  }

  @Override
  @SuppressWarnings("all")
  public void consistency(Store store) {

    try {

      inConsistency = true;
      changedShapeId = false;

      if (DEBUG_MAIN || DEBUG_SHAPE_SKIP || DEBUG_VAR_SKIP || DEBUG_OBJECT_GROUNDING) {
        log.debug("consistency({})", store.level);
      }

      if (firstConsistencyCheck) {

        // enforce duration > 0 constraint

        for (GeostObject o : objects) {
          o.timeConstraint.consistencyDurationGtZero(store);

          if (o.timeConstraint.consistencyStartPlusDurationEqEnd(store)) {
            onObjectUpdate(o);
          }
        }

        firstConsistencyCheck = false;
        firstConsistencyLevel = store.level;
      }

      if (partialShapeSweep) {
        Arrays.fill(fullyPruned, false);
      }

      // update the objects that are defined by some variables that changed
      flushQueue(variableQueue);

      while (!objectQueue.isEmpty()) {

        Iterator<GeostObject> it = objectQueue.iterator();
        GeostObject o = it.next();
        it.remove();

        boolean emptyQueue = false;

        // an object can be in the queue even though it is grounded,
        // if it was grounded twice in the same pruning
        while (o.isGrounded() && !pruneIfGrounded[o.no] && !emptyQueue) {
          if (!objectQueue.isEmpty()) {
            it = objectQueue.iterator();
            o = it.next();
            it.remove();
          } else {
            emptyQueue = true;
          }
        }

        if (emptyQueue) {
          break; // all objects done, get out of consistency()

          // object o will be checked now and since it is grounded then there is no need for
          // another check after that.
        }
        pruneIfGrounded[o.no] = false;

        if (DEBUG_OBJECT_GROUNDING) {
          log.debug("pruning object {}", o);
        }

        boolean fullSweep = true;
        if (partialShapeSweep) {
          // if object already had a full sweep in this node, do partial sweep only
          if (fullyPruned[o.no]) {
            fullSweep = false;
          } else {
            fullyPruned[o.no] = true;
          }
        }

        updateInternalConstraintsGeneratingOutboxes(o);

        if (DEBUG_MAIN || DEBUG_SHAPE_SKIP || DEBUG_VAR_SKIP || DEBUG_OBJECT_GROUNDING) {

          log.debug("pruning {}", o);

          if (DEBUG_SHAPE_SKIP) {
            log.debug("o.bestShapeId = {}", Arrays.toString(o.bestShapeId));
          }
        }

        boolean inconsistent = false;

        // Sweep using master ordering. Later on, for each dimension in the
        // loop below we will be changing most significant dimension.
        int[] ordering = order.masterOrdering();

        final int size4 = dimension + 1;
        for (int di = 0; di < size4; di++) { // time is the additional dimension

          int d = ordering[di];

          /*
           * if the variable is a singleton and is not in the variable queue,
           * it means that it has been either grounded or checked by geost.
           * If no shape was removed, result would not change, therefore there is
           * no need to run the pruning for that variable
           * Another exception is if shapeId is not a singleton. Indeed, in this case,
           * we may be able to remove a shape that is not useful.
           */
          boolean needPruning = true;
          // if no shape ID changed and o.shapeId is a singleton, consider skipping variable
          if (!changedShapeId && o.shapeId.singleton()) {
            if (d != dimension) {
              final Var prunedVar = o.coords[d];
              needPruning = !(prunedVar.singleton() && !variableQueue.contains(prunedVar));
            } else {
              needPruning =
                  !(o.start.singleton()
                      && o.end.singleton()
                      && !variableQueue.contains(o.start)
                      && !variableQueue.contains(o.end)
                      && !variableQueue.contains(o.duration));
            }
          }

          if (enforceNoSkip) {
            needPruning = true;
          }

          if (needPruning) {

            // It specifies the lowest lower bound found for the origin across multiple shapes.
            int minLowerBound = IntDomain.MAX_INT;
            // It specifies the highest upper bound for for the origin across multiple shapes.
            int maxUpperBound = IntDomain.MIN_INT;

            int lastSidIndex = 0;
            boolean bestShapeIDFound = false;
            int bestSidLastPrune = o.bestShapeId[d];

            final ValueEnumeration vals = o.shapeId.domain.valueEnumeration();
            while (vals.hasMoreElements()) {

              int sid = vals.nextElement();

              if (sid == bestSidLastPrune) {
                bestShapeIDFound = true;
                shapeIdsToPrune[0] = sid;
              } else {
                lastSidIndex++;
                shapeIdsToPrune[lastSidIndex] = sid;
              }
            }

            if (!bestShapeIDFound) {
              // best shape ID was removed from o.shapeId
              shapeIdsToPrune[0] = shapeIdsToPrune[lastSidIndex];
              if (ASSERTS_ENABLED && lastSidIndex < 1) {
                throw new IllegalStateException("Assertion failed");
              }
              lastSidIndex--;
            }

            int bestLowerBound = IntDomain.MAX_INT;
            int bestUpperBound = IntDomain.MIN_INT;

            for (int i = 0; i <= lastSidIndex; i++) {

              int sid = shapeIdsToPrune[i];

              if (DEBUG_MAIN) {
                log.debug("shape ID in consistency: {}", sid);
              }

              if (GATHER_STATS) {
                pruneMinCount++;
              }

              int lowerBound =
                  pruneMin(
                      store,
                      o,
                      sid,
                      d,
                      //                     internalConstraintsToUse,
                      fullSweep ? IntDomain.MAX_INT : minLowerBound);

              if (lowerBound >= IntDomain.MAX_INT) {

                // remove shape ID, it is infeasible
                if (DEBUG_DOUBLE_LAYER) {
                  log.debug("geost {} changing {}, removing {}", id(), o.shapeId, sid);
                }

                changedShapeId = true;

                // don't skip objects again if some shape ID changed
                Arrays.fill(pruneIfGrounded, true);

                // CHANGED. replaced the above with the line below.
                o.shapeId.domain.inComplement(store.level, o.shapeId, sid);

              } else {

                minLowerBound = Math.min(minLowerBound, lowerBound);

                // consider pruning in the other direction only if the first did not fail
                if (GATHER_STATS) {
                  pruneMaxCount++;
                }

                int upperBound =
                    pruneMax(
                        store,
                        o,
                        sid,
                        d,
                        //                       internalConstraintsToUse,
                        fullSweep ? IntDomain.MIN_INT : maxUpperBound);

                if (upperBound <= IntDomain.MIN_INT) {

                  // remove shape ID, it is infeasible
                  if (DEBUG_DOUBLE_LAYER) {
                    log.debug("geost {} changing {}, removing {}", id(), o.shapeId, sid);
                  }

                  changedShapeId = true;

                  // don't skip objects if some shape ID changed
                  Arrays.fill(pruneIfGrounded, true);

                  // CHANGED. replaced the above with the line below.
                  o.shapeId.domain.inComplement(store.level, o.shapeId, sid);

                } else {
                  maxUpperBound = Math.max(maxUpperBound, upperBound);

                  // update bestShapeId if better than previous one
                  if (lowerBound <= bestLowerBound && upperBound >= bestUpperBound) {
                    bestLowerBound = lowerBound;
                    bestUpperBound = upperBound;
                    o.bestShapeId[d] = sid;
                  }
                }
              }
            }

            if (ASSERTS_ENABLED && minLowerBound <= IntDomain.MIN_INT) {
              throw new IllegalStateException("Assertion failed");
            }
            if (ASSERTS_ENABLED && maxUpperBound >= IntDomain.MAX_INT) {
              throw new IllegalStateException("Assertion failed");
            }

            if (minLowerBound < IntDomain.MAX_INT) {

              IntVar prunedVariable = d != dimension ? o.coords[d] : o.start;

              if (DEBUG_DOUBLE_LAYER) {
                if (minLowerBound > prunedVariable.min()) {
                  log.debug(
                      "geost {} changing {} min bound to {}", id(), prunedVariable, minLowerBound);
                }
              }

              prunedVariable.domain.inMin(store.level, prunedVariable, minLowerBound);

              if (oneTimeVarChanged) {
                o.timeConstraint.consistencyStartPlusDurationEqEnd(store);
                //   //modification of some of the time variables, sweep again
                oneTimeVarChanged = false;
              }

            } else {
              inconsistent = true;
            }

            if (!inconsistent && maxUpperBound > IntDomain.MIN_INT) {

              IntVar prunedVariable = d != dimension ? o.coords[d] : o.end;

              if (DEBUG_DOUBLE_LAYER) {
                if (maxUpperBound < prunedVariable.max()) {
                  log.debug(
                      "geost {} changing {} max bound to {}", id(), prunedVariable, maxUpperBound);
                }
              }

              prunedVariable.domain.inMax(store.level, prunedVariable, maxUpperBound);

              if (oneTimeVarChanged) {
                o.timeConstraint.consistencyStartPlusDurationEqEnd(store);
                //   //modification of some of the time variables, sweep again
                oneTimeVarChanged = false;
              }

            } else {
              inconsistent = true;
            }
          }
        }

        if (inconsistent) {
          throw Store.failException;
        }

        if (DEBUG_MAIN) {
          log.debug("pruned {}", o);
        }
      }

      // backtracking data storage
      if (!updatedObjectSet.isEmpty()) {

        for (GeostObject uo : updatedObjectSet) {
          objectList.add(uo);
        }

        updatedObjectSet.clear();

        // mark beginning of new set
        setStart.update(objectList.size());

        if (DEBUG_BACKTRACK) {
          log.debug("new set, begins at {}, stamp: {}", setStart.value(), setStart);
        }
      }

    } finally {

      inConsistency = false;
      variableQueue.clear();

      objectQueue.clear();
    }
  }

  /**
   * It is called whenever the object currently being pruned changes. useful for constraint pruning
   * version of Geost.
   *
   * @param o the object currently being pruned for which internal constraints are being filtered.
   */
  protected void updateInternalConstraintsGeneratingOutboxes(GeostObject o) {

    if (filterUseless) {
      filterUsefulConstraintsWithDomainBox(o);
    } else {
      collectAllConstraintsWithCardInfeasible(o);
    }

    if (DEBUG_REORDER) {
      log.debug("changed pruning object");
    }
  }

  private void filterUsefulConstraintsWithDomainBox(GeostObject o) {
    workingList.clear();
    ValueEnumeration sids = o.shapeId.domain.valueEnumeration();
    while (sids.hasMoreElements()) {
      workingList.add(getShape(sids.nextElement()).boundingBox);
    }
    Dbox bb = Dbox.boundingBox(workingList).copyInto(Dbox.newBox(dimension));

    Dbox domainBox = buildDomainBoxForObject(o, bb);
    Dbox constraintBox = Dbox.newBox(dimension + 1);
    int[] constraintBoxOrigin = constraintBox.origin;
    int[] constraintBoxLength = constraintBox.length;

    lastConstraintToCheck = 0;
    for (InternalConstraint c : objectConstraints[o.no]) {
      if (c.cardInfeasible() > 0) {
        int[] lowerBound = c.absInfeasible(Geost.SweepDirection.PRUNEMIN);
        for (int i = 0; i < dimension + 1; i++) {
          constraintBoxOrigin[i] = lowerBound[i] - 1;
        }
        int[] upperBound = c.absInfeasible(Geost.SweepDirection.PRUNEMAX);
        for (int i = 0; i < dimension + 1; i++) {
          constraintBoxLength[i] = upperBound[i] - constraintBoxOrigin[i] + 2;
        }
        if (domainBox.intersectWith(constraintBox) != null) {
          stillUsefulInternalConstraints[lastConstraintToCheck] = c;
          lastConstraintToCheck++;
        }
      }
    }

    Dbox.dispatchBox(bb);
    Dbox.dispatchBox(constraintBox);
    Dbox.dispatchBox(domainBox);
  }

  private Dbox buildDomainBoxForObject(GeostObject o, Dbox bb) {
    Dbox domainBox = Dbox.newBox(dimension + 1);
    int[] domainBoxOriginShifted = domainBox.origin;
    int[] domainBoxLengthShifted = domainBox.length;
    for (int i = 0; i < dimension; i++) {
      domainBoxOriginShifted[i] = o.coords[i].min() + bb.origin[i];
      domainBoxLengthShifted[i] =
          o.coords[i].max() + bb.origin[i] + bb.length[i] - domainBoxOriginShifted[i];
    }
    domainBoxOriginShifted[dimension] = IntDomain.MIN_INT;
    domainBoxLengthShifted[dimension] = IntDomain.MAX_INT * 2;
    return domainBox;
  }

  private void collectAllConstraintsWithCardInfeasible(GeostObject o) {
    lastConstraintToCheck = 0;
    for (InternalConstraint c : objectConstraints[o.no]) {
      if (c.cardInfeasible() > 0) {
        stillUsefulInternalConstraints[lastConstraintToCheck] = c;
        lastConstraintToCheck++;
      }
    }
  }

  /**
   * It does the processing needed given the set of variables that was updated between two
   * consecutive calls to the consistency function.
   *
   * @param variables variables in the queue
   */
  protected void flushQueue(Collection<Var> variables) {

    objectList4Flush.clear();

    for (Var v : variables) {

      GeostObject o = variableObjectMap.get(v);

      if (o == null) {
        // can be ignored as the variable was singleton upon imposition.
        continue;
      }

      // if it is a time variable, run time constraint
      if (v == o.start || v == o.end || v == o.duration) {
        o.timeConstraint.consistencyStartPlusDurationEqEnd(store);
      } else if (v == o.shapeId) {
        // some shape ID was changed by some external source, remember it
        changedShapeId = true;
      }

      objectList4Flush.add(o);
    }

    for (GeostObject o : objectList4Flush) {
      onObjectUpdate(o);
    }
  }

  /**
   * It puts the object into the queue if it can be still pruned or cause failure.
   *
   * @param o the object which is possibly put into the queue.
   */
  public final void queueObject(GeostObject o) {

    // Important to keep and ensure.
    if (ASSERTS_ENABLED && !inConsistency) {
      throw new IllegalStateException(
          String.valueOf("It is improperly called outside the consistency function."));
    }

    if (!o.isGrounded() || pruneIfGrounded[o.no]) {

      if (DEBUG_OBJECT_GROUNDING) {
        log.debug("queued {}", o);
      }

      if (GATHER_STATS) {
        queuedObjectCount++;
      }

      objectQueue.add(o);

    } else if (DEBUG_OBJECT_GROUNDING) {
      log.debug("The object {} was skipped.", o);
    }
  }

  /**
   * It performs the necessary operations for a given changed object.
   *
   * <p>If the change occurred due to backtracking then only external constraints are being informed
   * about the change, so they can restore proper state in connection to the object. If this
   * function is not called during backtracking then also the following is executed.
   *
   * <p>If the change occurs due to search progress downwards then it stores the information about
   * object change as well as schedules pruning check for all connected objects.
   *
   * @param o the object which had a domain change
   */
  protected void onObjectUpdate(GeostObject o) {

    if (GATHER_STATS) {
      onObjectUpdateCount++;
    }

    if (DEBUG_MAIN) {
      log.debug("adding objects to the queue");
    }

    for (ExternalConstraint ec : externalConstraints) {
      ec.onObjectUpdate(o);
    }

    if (!backtracking) {
      updatedObjectSet.add(o);

      if (DEBUG_BACKTRACK) {
        log.debug("updating object {}", o);
      }

      if (allLinked) {
        queueAllObjectsWhenLinked();
      } else {
        queueObjectAndPrunableFromConstraints(o);
      }
    }
  }

  private void queueAllObjectsWhenLinked() {
    for (GeostObject lo : objects) {
      queueObject(lo);
    }
  }

  private void queueObjectAndPrunableFromConstraints(GeostObject o) {
    queueObject(o);
    temporaryObjectSet.clear();
    for (ExternalConstraint ec : externalConstraints) {
      ec.addPrunableObjects(o, temporaryObjectSet);
      while (!temporaryObjectSet.isEmpty()) {
        Iterator<GeostObject> it = temporaryObjectSet.iterator();
        GeostObject next = it.next();
        it.remove();
        queueObject(next);
      }
    }
  }

  @Override
  public int getConsistencyPruningEvent(Var v) {

    // If consistency function mode
    if (consistencyPruningEvents != null) {
      Integer possibleEvent = consistencyPruningEvents.get(v);
      if (possibleEvent != null) {
        return possibleEvent;
      }
    }

    GeostObject o = variableObjectMap.get(v);

    if (o == null) {
      return Domain.NONE;
    }

    if (o.shapeId == v) {
      return IntDomain.ANY;
    }

    return IntDomain.BOUND;
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    throw new IllegalStateException("Not implemented as more precise implementation exists.");
  }

  @Override
  public void impose(Store store) {

    super.impose(store);

    this.store = store;

    lastLevelLastVar = new TimeStamp<>(store, store.level);
    lastLevelLastVar.update(-1);

    genInternalConstraints();

    store.registerRemoveLevelLateListener(this);

    setStart = new TimeStamp<>(store, store.level);
    setStart.update(0);

    objectList = new ArrayList<>();
    updatedObjectSet = new HashSet<>();
  }

  @Override
  public void increaseWeight() {

    if (IS_INCREASE_WEIGHT_ENABLED) {
      for (GeostObject o : objects) {
        for (Var v : o.getVariables()) {
          v.weight++;
        }
      }
    }
  }

  @Override
  @SuppressWarnings("all")
  public void queueVariable(int level, Var v) {

    currentLevel = level;

    if (v.singleton()) {

      GeostObject o = variableObjectMap.get(v);

      if (o == null) {
        // can be ignored as the variable was singleton upon imposition.
        return;
      }

      o.onGround(v);

      if (DEBUG_OBJECT_GROUNDING) {
        log.debug("grounding {}", v);
      }

      if (!inConsistency) {
        pruneIfGrounded[o.no] = true;
      }

      if (lastLevelLastVar.stamp() < store.level) {
        lastLevelLastVar.update(groundedVars.size());
      }

      groundedVars.add(v);
    }

    if (inConsistency) {

      if (ASSERTS_ENABLED && !variableObjectMap.containsKey(v) && !v.singleton()) {
        throw new IllegalStateException(
            String.valueOf("The variable " + v + " does not exist in variable-object map."));
      }

      // if this variable can modify the sweep result, process it right away
      GeostObject o = variableObjectMap.get(v);

      if (o == null) {
        // can be ignored as the variable was singleton upon imposition.
        return;
      }

      // if it is a time variable, run time constraint
      if (v == o.start || v == o.end || v == o.duration) {
        oneTimeVarChanged = true;
      }

      onObjectUpdate(o);

    } else {
      // keep it for later
      variableQueue.add(v);
    }

    if (DEBUG_VAR_SKIP || DEBUG_OBJECT_GROUNDING) {
      if (inConsistency) {
        log.debug("The variable {} was pruned by geost consistency function itself", v);
      } else {
        log.debug(
            "The variable {} was pruned by outside constraints and it is queued as changed within geost",
            v);
      }
    }
  }

  @Override
  @SuppressWarnings("all")
  public void removeLevel(int level) {

    // added.
    if (level > currentLevel) {
      return;
    }

    if (DEBUG_MAIN || DEBUG_SHAPE_SKIP || DEBUG_VAR_SKIP || DEBUG_OBJECT_GROUNDING) {
      log.debug("removeLevel({})", store.level);
    }

    if (ASSERTS_ENABLED && inConsistency) {
      throw new IllegalStateException("Assertion failed");
    }

    if (firstConsistencyLevel == level) {
      firstConsistencyCheck = true;
    }

    removeLimit = lastLevelLastVar.value();
  }

  @Override
  public void removeLevelLate(int level) {

    if (ASSERTS_ENABLED && inConsistency) {
      throw new IllegalStateException("Assertion failed");
    }

    // added. to mask a bug if multiple remove levels are being executed for the same level.
    if (level > currentLevel) {
      return;
    }

    ungroundVariablesAboveRemoveLimit();

    backtracking = true;

    restoreUpdatedObjects();
    updatedObjectSet.clear();

    restoreObjectsFromList();

    backtracking = false;
  }

  private void ungroundVariablesAboveRemoveLimit() {

    if (lastLevelLastVar.value() >= removeLimit) {
      return;
    }
    for (int i = groundedVars.size() - 1; i >= removeLimit; i--) {

      Var v = groundedVars.remove(i);
      if (ASSERTS_ENABLED && v == null) {
        throw new IllegalStateException("Assertion failed");
      }

      if (DEBUG_OBJECT_GROUNDING) {
        log.debug("The variable {} is being ungrounded", v);
      }

      variableObjectMap.get(v).onUnGround(v);
    }
  }

  private void restoreUpdatedObjects() {

    if (updatedObjectSet.isEmpty()) {
      return;
    }
    for (GeostObject o : updatedObjectSet) {

      onObjectUpdate(o);
      if (DEBUG_BACKTRACK) {
        log.debug("restored object {}", o);
      }
    }
  }

  private void restoreObjectsFromList() {

    int lowerBound = setStart.value();
    for (int i = objectList.size() - 1; i >= lowerBound; i--) {

      GeostObject o = objectList.remove(i);

      if (ASSERTS_ENABLED && o == null) {
        throw new IllegalStateException("Assertion failed");
      }

      onObjectUpdate(o);

      if (DEBUG_BACKTRACK) {
        log.debug("restored object {}", o);
      }
    }
  }

  @Override
  public String toString() {
    return "Geost("
        + Arrays.asList(objects)
        + ", "
        + Arrays.asList(externalConstraints)
        + ", "
        + Arrays.asList(shapeRegister)
        + ")";
  }

  /**
   * It returns all the statistics gathered by geost constraint during the search.
   *
   * @return an array list consisting of different statistics collected during search.
   */
  public List<Long> getStatistics() {

    List<Long> stats = new ArrayList<>();

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
   * It specifies in what direction the sweep algorithm is progressing.
   *
   * @author Marc-Olivier Fleury and Radoslaw Szymanek
   */
  public enum SweepDirection {
    /** The sweep algorithm prunes the minimal values for the origins. */
    PRUNEMIN,
    /** The sweep algorithm prunes the maximal values for the origins. */
    PRUNEMAX
  }
}
