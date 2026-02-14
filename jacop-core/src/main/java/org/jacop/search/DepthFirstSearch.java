/*
 * DepthFirstSearch.java
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

package org.jacop.search;

import java.lang.reflect.Array;
import java.util.concurrent.atomic.AtomicInteger;
import lombok.Getter;
import lombok.Setter;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.XltC;
import org.jacop.core.Domain;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.SwitchesPruningLogging;
import org.jacop.core.Var;

/**
 * Implements Depth First Search with number of possible plugins (listeners) to be attached to
 * modify the search.
 *
 * @param <T> type of variables used in this search.
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class DepthFirstSearch<T extends Var> implements Search<T> {

  // @todo make debugAll be used in printing statements.
  static final boolean debugAll = true;
  static final AtomicInteger no = new AtomicInteger(0);

  /** It specifies if for setVar based search the left branch should impose EinA constraint. */
  public final boolean einAinleftTree = true;

  /**
   * If it is set to true then the optimizing search will quit the search if this action is
   * indicated by the solution listener.
   */
  public boolean respectSolutionListenerAdvice;

  /** It represents the cost value of currently best solution for IntVar cost. */
  @Getter public int costValue = Integer.MAX_VALUE;

  /** It represents the cost value of currently best solution for FloatVar cost. */
  @Getter public double costValueFloat = Double.MAX_VALUE;

  /** It represents the cost variable. */
  @Getter public Var costVariable;

  /** It is invoked when returning from left or right child. */
  @Getter @Setter public ExitChildListener<T> exitChildListener;

  /** It is invoked when consistency function has been executed. */
  @Getter @Setter public ConsistencyListener consistencyListener;

  /** It is executed when a solution is found. */
  @Getter @Setter public SolutionListener<T> solutionListener = new SimpleSolutionListener<>();

  /** It is executed when search is started, before entering the search. */
  @Getter @Setter public InitializeListener initializeListener;

  /** It stores searches which will be executed when this one has assign all its variables. */
  public Search<? extends Var>[] childSearches;

  /**
   * If this search is a sub-search then this pointer will point out to the master search (i.e. the
   * search which have invoked this search).
   */
  @Setter public Search<? extends Var> masterSearch;

  /** It represents store within which a search is performed. */
  @Setter public Store store;

  /** It specifies that the time-out has occured. */
  public boolean timeOutOccured;

  /** It specifies the id of the search. */
  public String searchId;

  /** It remembers what child search has been already examined. */
  public int currentChildSearch = -1;

  /**
   * It decides if the found solution is immediately assigned to the store.* If the solution is not
   * assigned immediately after the search is concluded but later then special care may be required.
   * As soon as search exits all propagations (including the first time consistency execution of the
   * constraints) may be forgotten. Even worse some values of the variables for which the constraint
   * was never aware of (not even at impose time) may appear back in the domain. The best remedy for
   * this problem is to call store.consistency() method once and only once after the model is
   * imposed and before the search is executed and never remove the level at which the store resides
   * after store.consistency() method is executed.
   */
  @Setter boolean assignSolution = true;

  /** It specifies after how many backtracks the search exits. */
  long backtracksOut = -1;

  /** It specifies if the backtrack out is on. */
  boolean backtracksOutCheck;

  /** It specifies if search can exit before the search has finished. */
  boolean check;

  /**
   * It represents the constraint which enforces that next solution is better than currently best
   * solution.
   */
  Constraint cost;

  @Setter boolean optimize;

  /** It stores number of nodes with decisions during search. */
  @Getter int decisions;

  /** It specifies after how many decisions the search exits. */
  long decisionsOut = -1;

  /** It specifies if the decisions out is on. */
  boolean decisionsOutCheck;

  /** It represents current depth of store used in search. */
  int depth;

  /** It stores current depth of the search excluding paths in a search tree. */
  int depthExcludePaths;

  /** It represents the choice point selection heuristic. */
  SelectChoicePoint<T> heuristic;

  /** It stores the maximum depth reached during search. */
  int maxDepth;

  /** It stores the maximum depth of the search excluding paths. */
  int maxDepthExcludePaths;

  /** It stores number of nodes visited during search. */
  @Getter int nodes;

  /** It specifies after how many nodes the search exits. */
  long nodesOut = -1;

  /** It specifies if the nodes out is on. */
  boolean nodesOutCheck;

  /**
   * It stores number of backtracks during search. A backtrack is a search node for which all
   * children has failed.
   */
  int numberBacktracks;

  /** It decides if information about search is printed. */
  @Setter boolean printInfo = true;

  /** The object informed about the determination of the timeout. */
  @Getter @Setter TimeOutListener timeOutListener;

  /** It is executed upon search exit. It allows to add learnt constraints. */
  @Getter @Setter ExitListener exitListener;

  /** It specifies the exact time point after which the timeout will occur (in miliseconds). */
  long timeOut;

  /** It specifies if the timeout is on. */
  boolean timeOutCheck;

  /** It specifies the number of seconds after which the search will timeout. */
  long tOut = -1;

  /**
   * It stores number of wrong decisions during search. A wrong decision is a leaf of a search which
   * has failed.
   */
  @Getter int wrongDecisions;

  /** It specifies after how many wrong decisions the search exits. */
  long wrongDecisionsOut = -1;

  /** It specifies if the wrong decisions out is on. */
  boolean wrongDecisionsOutCheck;

  /** It specifies current child search. */
  public DepthFirstSearch() {
    searchId = "DFS" + no.incrementAndGet();
  }

  /**
   * It sets the id of the store.
   *
   * @param name the id of the store object.
   */
  public void setId(String name) {
    searchId = name;
  }

  /** {@inheritDoc} */
  public String id() {
    return searchId;
  }

  /**
   * Sets the child searches to be executed after this search assigns all its variables.
   *
   * @param child array of child searches to set.
   */
  public void setChildSearch(Search<? extends Var>[] child) {

    if (childSearches != null) {
      for (Search<? extends Var> c : childSearches) {
        c.setMasterSearch(null);
      }
    }
    childSearches = child;

    if (childSearches != null) {
      for (Search<? extends Var> c : childSearches) {
        c.setMasterSearch(this);
      }
    }
  }

  /**
   * Adds a child search to be executed after this search assigns all its variables.
   *
   * @param child the child search to add.
   */
  @SuppressWarnings("unchecked")
  public void addChildSearch(Search<? extends Var> child) {

    if (childSearches == null) {
      // Always use Search.class (the interface) as the component type since all children implement
      // Search
      // This ensures compatibility when different Search implementations are added
      childSearches = (Search<? extends Var>[]) Array.newInstance(Search.class, 1);
      childSearches[0] = child;
    } else {

      Search<? extends Var>[] old = childSearches;
      // Always use Search.class (the interface) as the component type
      childSearches =
          (Search<? extends Var>[]) Array.newInstance(Search.class, childSearches.length + 1);
      System.arraycopy(old, 0, childSearches, 0, old.length);
      childSearches[old.length] = child;
    }

    child.setMasterSearch(this);
  }

  public void setSelectChoicePoint(SelectChoicePoint<T> select) {
    heuristic = select;
  }

  /** It returns number of backtracks performed by the search. */
  public int getBacktracks() {
    return numberBacktracks;
  }

  /** It returns the maximum depth reached by a search. */
  public int getMaximumDepth() {
    return maxDepthExcludePaths;
  }

  /**
   * Returns the most recent solution found by this search.
   *
   * @return array of domains representing the last solution found.
   */
  public Domain[] getSolution() {
    return solutionListener.getSolution(solutionListener.solutionsNo());
  }

  /**
   * Returns the solution with the given number.
   *
   * @param no the solution number.
   * @return array of domains representing the specified solution.
   */
  public Domain[] getSolution(int no) {
    return solutionListener.getSolution(no);
  }

  /**
   * Returns the variables used by this search.
   *
   * @return array of variables used in this search.
   */
  public T[] getVariables() {

    T[] vars = solutionListener.getVariables();

    if (vars != null) {
      return vars;
    }

    assert false : "Fix it. Uncomment below.";

    return null;
  }

  /** This function is called recursively to assign variables one by one. */
  public boolean label(int firstVariable) {

    boolean consistent;

    if (check) {

      if (timeOutCheck && System.currentTimeMillis() > timeOut) {
        timeOutOccured = true;
        if (timeOutListener != null) {
          timeOutListener.executedAtTimeOut(solutionListener.solutionsNo());
        }
        return false;
      }

      if (nodesOutCheck && nodes > nodesOut) {
        timeOutOccured = true;
        if (timeOutListener != null) {
          timeOutListener.executedAtTimeOut(solutionListener.solutionsNo());
        }
        return false;
      }

      if (decisionsOutCheck && decisions > decisionsOut) {
        timeOutOccured = true;
        if (timeOutListener != null) {
          timeOutListener.executedAtTimeOut(solutionListener.solutionsNo());
        }
        return false;
      }

      if (wrongDecisionsOutCheck && wrongDecisions > wrongDecisionsOut) {
        timeOutOccured = true;
        if (timeOutListener != null) {
          timeOutListener.executedAtTimeOut(solutionListener.solutionsNo());
        }
        return false;
      }

      if (backtracksOutCheck && numberBacktracks > backtracksOut) {
        timeOutOccured = true;
        if (timeOutListener != null) {
          timeOutListener.executedAtTimeOut(solutionListener.solutionsNo());
        }
        return false;
      }
    }

    // Instead of imposing constraint just restrict bounds
    // -1 since costValue is the cost of last solution
    if (optimize && cost != null) {
      try {
        CostVariableHandler costHandler =
            SearchHandlerRegistry.getInstance().findCostHandler(costVariable);
        if (costHandler != null) {
          double minCost = costHandler.getMinCostValue(costVariable);
          double currentBestCost = costVariable instanceof IntVar ? costValue : costValueFloat;
          double previousCost = costHandler.getPreviousCostValue(currentBestCost);

          // Check if we can still improve
          // For IntVar: minCost <= previousCost (which is costValue - 1)
          // For FloatVar: minCost < previousCost (which accounts for floating-point precision)
          boolean canImprove =
              costVariable instanceof IntVar ? minCost <= previousCost : minCost < previousCost;

          if (canImprove) {
            // Can improve: restrict domain to exclude values worse than previous best
            costHandler.updateCostDomain(store, costVariable, currentBestCost);
          } else {
            // Cannot improve: no better solutions possible
            if (consistencyListener != null) {
              consistencyListener.executeAfterConsistency(false);
            }
            return false;
          }
        } else if (costVariable instanceof IntVar var) {
          // Fallback for IntVar (should always have handler, but just in case)
          if (var.min() <= costValue - 1) {
            var.domain.in(store.level, var, var.min(), costValue - 1);
          } else {
            if (consistencyListener != null) {
              consistencyListener.executeAfterConsistency(false);
            }
            return false;
          }
        }
      } catch (FailException _) {
        if (consistencyListener != null) {
          consistencyListener.executeAfterConsistency(false);
        }
        return false;
      }
    }

    // all search nodes begins here
    nodes++;

    consistent = store.consistency();

    if (consistencyListener != null) {
      consistent = consistencyListener.executeAfterConsistency(consistent);
    }

    if (!consistent) {
      // Failed leaf of the search tree
      wrongDecisions++;
      return false;
    } else { // consistent

      store.setLevel(++depth);
      maxDepth = Math.max(depth, maxDepth);

      // Delete function indicates which is next variable for
      // labeling

      T fdv = heuristic.getChoiceVariable(firstVariable);
      PrimitiveConstraint choice = null;
      int val = 0;

      if (fdv != null) {

        val = heuristic.getChoiceValue();
        assert store.currentConstraint == null;

        //   maybe a boolean flag, if search should work
        //   C, not(C) versus not(C), C;

        DomainOperationHandler domainHandler =
            SearchHandlerRegistry.getInstance().findDomainHandler(fdv);
        if (domainHandler != null) {
          domainHandler.inValue(store, fdv, val, einAinleftTree);
        } else if (fdv instanceof IntVar var) {
          // Fallback for IntVar (should always have handler, but just in case)
          ((IntDomain) fdv.dom()).inValue(store.level, var, val);
        }

        decisions++;

        depthExcludePaths++;
        if (depthExcludePaths > maxDepthExcludePaths) {
          maxDepthExcludePaths = depthExcludePaths;
        }

      } else {

        choice = heuristic.getChoiceConstraint(firstVariable);

        if (choice == null) {

          // Solution already found so this is not a search node
          nodes--;
          // Execute subsearches if given.

          if (childSearches != null) {

            boolean childResult = false;
            boolean childFoundSolution = false;
            currentChildSearch = 0;

            for (; currentChildSearch < childSearches.length; currentChildSearch++) {
              childSearches[currentChildSearch]
                  .getSolutionListener()
                  .setParentSolutionListener(solutionListener);
              childSearches[currentChildSearch].setStore(store);

              if (costVariable != null) {
                childSearches[currentChildSearch].setCostVar(costVariable);
              }

              int currentChildSolutionNo =
                  childSearches[currentChildSearch].getSolutionListener().solutionsNo();
              childResult = childSearches[currentChildSearch].labeling();
              if (childSearches[currentChildSearch].getSolutionListener().solutionsNo()
                  > currentChildSolutionNo) {
                childFoundSolution = true;
              }

              if (childResult) {
                break;
              }

              if (costVariable != null) {
                CostVariableHandler costHandler =
                    SearchHandlerRegistry.getInstance().findCostHandler(costVariable);
                if (costHandler != null) {
                  double childCostValue;
                  if (costVariable instanceof IntVar) {
                    childCostValue = childSearches[currentChildSearch].getCostValue();
                  } else {
                    childCostValue = childSearches[currentChildSearch].getCostValueFloat();
                  }

                  double currentBestCost =
                      costVariable instanceof IntVar ? costValue : costValueFloat;
                  if (costHandler.isBetterCost(currentBestCost, childCostValue, true)) {
                    if (costVariable instanceof IntVar) {
                      costValue = (int) childCostValue;
                    } else {
                      costValueFloat = childCostValue;
                    }
                    cost = costHandler.createCostConstraint(costVariable, childCostValue);
                  }

                  double minCost = costHandler.getMinCostValue(costVariable);
                  if (childCostValue <= minCost) {
                    // other child searches will not be able to find any solutions.
                    break;
                  } else {
                    costHandler.updateCostDomain(store, costVariable, childCostValue);
                  }
                } else if (costVariable instanceof IntVar var) {
                  // Fallback for IntVar
                  int childCostValue = childSearches[currentChildSearch].getCostValue();
                  if (childCostValue < costValue) {
                    costValue = childCostValue;
                    cost = new XltC(var, costValue);
                  }
                  if (childCostValue <= var.min()) {
                    break;
                  } else {
                    var.domain.inMax(store.level, var, childCostValue - 1);
                  }
                }
              }
            }

            if (childResult && costVariable != null) {
              CostVariableHandler costHandler =
                  SearchHandlerRegistry.getInstance().findCostHandler(costVariable);
              if (costHandler != null) {
                double childCostValue;
                if (costVariable instanceof IntVar) {
                  childCostValue = childSearches[currentChildSearch].getCostValue();
                } else {
                  childCostValue = childSearches[currentChildSearch].getCostValueFloat();
                }

                double currentBestCost =
                    costVariable instanceof IntVar ? costValue : costValueFloat;
                if (costHandler.isBetterCost(currentBestCost, childCostValue, true)) {
                  if (costVariable instanceof IntVar) {
                    costValue = (int) childCostValue;
                  } else {
                    costValueFloat = childCostValue;
                  }
                  cost = costHandler.createCostConstraint(costVariable, childCostValue);
                }
              } else if (costVariable instanceof IntVar var) {
                // Fallback for IntVar
                int childCostValue = childSearches[currentChildSearch].getCostValue();
                if (childCostValue < costValue) {
                  costValue = childCostValue;
                }
                cost = new XltC(var, costValue);
              }
            }

            boolean stopMasterSearch = false;

            if (childResult || childFoundSolution) {
              // Child search found solution, so there is a
              // solution
              // for this search too.

              stopMasterSearch = solutionListener.executeAfterSolution(this, heuristic);

              if (!childResult) {
                stopMasterSearch = false;
              }
            }

            store.removeLevel(depth);
            store.setLevel(--depth);

            if (!respectSolutionListenerAdvice && optimize) {

              return false;
            }

            return stopMasterSearch;
          }

          if (costVariable != null) {
            // it does not mean there is an optimization, only that we want to remember the value
            // of the costVariable
            CostVariableHandler costHandler =
                SearchHandlerRegistry.getInstance().findCostHandler(costVariable);
            if (costHandler != null) {
              double currentCost = costHandler.getCostValue(costVariable);
              if (costVariable instanceof IntVar) {
                costValue = (int) currentCost;
              } else {
                costValueFloat = currentCost;
              }
              cost = costHandler.createCostConstraint(costVariable, currentCost);
            } else if (costVariable instanceof IntVar var) {
              // Fallback for IntVar
              costValue = var.dom().min();
              cost = new XltC(var, costValue);
            }
          }

          if (!respectSolutionListenerAdvice && optimize) {

            solutionListener.executeAfterSolution(this, heuristic);

            store.removeLevel(depth);
            store.setLevel(--depth);

            return false;
          }

          boolean returnCode = solutionListener.executeAfterSolution(this, heuristic);

          store.removeLevel(depth);
          store.setLevel(--depth);

          return returnCode;

        } else {

          assert store.currentConstraint == null;
          store.impose(choice);
          decisions++;

          depthExcludePaths++;
          if (depthExcludePaths > maxDepthExcludePaths) {
            maxDepthExcludePaths = depthExcludePaths;
          }
        }
      }

      // choice point imposed.

      consistent = label(heuristic.getIndex());

      if (exitChildListener != null
          && ((choice == null && !exitChildListener.leftChild(fdv, val, consistent))
              || (choice != null && !exitChildListener.leftChild(choice, consistent)))) {
        store.removeLevel(depth);
        store.setLevel(--depth);
        depthExcludePaths--;
        return false;
      }

      if (consistent) {
        store.removeLevel(depth);
        store.setLevel(--depth);
        depthExcludePaths--;
        return true;
      } else {

        // Assigning current variable to a value indicated by
        // indomain result in a failure, this value is removed
        // from the domain and label is called recursively with
        // the same currentVariable.

        store.removeLevel(depth);

        Object[] args = {depth, fdv, val};

        if (SwitchesPruningLogging.traceSearchTree) {
          SwitchesPruningLogging.log(
              choice == null,
              DepthFirstSearch.class,
              "Store level: {}, Right branch: {} \\ {}",
              args);
          SwitchesPruningLogging.log(
              choice != null,
              DepthFirstSearch.class,
              "Store level: {}, Right branch: {}",
              depth,
              choice);
        }

        if (choice != null) {

          assert store.currentConstraint == null;

          store.setLevel(store.level);

          store.impose(new Not(choice));

          consistent = label(firstVariable);

          if (exitChildListener != null) {
            exitChildListener.rightChild(choice, consistent);
          }

          if (!consistent) {
            numberBacktracks++;
          }

          store.removeLevel(depth);
        } else if (!fdv.dom().singleton()) { //       else if (!fdv.dom().singleton(val)) {

          assert store.currentConstraint == null;

          store.setLevel(store.level);

          DomainOperationHandler domainHandler =
              SearchHandlerRegistry.getInstance().findDomainHandler(fdv);
          if (domainHandler != null) {
            domainHandler.inComplement(store, fdv, val, einAinleftTree);
          } else if (fdv instanceof IntVar var) {
            // Fallback for IntVar (should always have handler, but just in case)
            ((IntDomain) fdv.dom()).inComplement(store.level, var, val);
          }

          consistent = label(firstVariable);

          if (exitChildListener != null) {
            exitChildListener.rightChild(fdv, val, consistent);
          }

          if (!consistent) {
            numberBacktracks++;
          }

          store.removeLevel(depth);

        } else {
          consistent = false;
        }

        store.setLevel(--depth);

        depthExcludePaths--;

        return consistent;
      }
    }
  }

  /**
   * Sets the cost variable and enables optimization.
   *
   * @param cost the variable representing the cost to be minimized.
   */
  public void setCostVar(Var cost) {

    costVariable = cost;
    optimize = true;
  }

  /**
   * It is a labeling function called if the search is a sub-search being called from the parent
   * search. It never assigns a solution as it will be immediately retracted by search calling this
   * one.
   */
  public boolean labeling() {

    boolean raisedLevel = false;

    if (store.raiseLevelBeforeConsistency) {
      store.raiseLevelBeforeConsistency = false;
      store.setLevel(store.level + 1);
      raisedLevel = true;
    }

    depth = store.level;
    cost = null;

    if (costVariable == null) {
      optimize = false;
    }

    if (initializeListener != null) {
      initializeListener.executedAtInitialize(store);
    }

    // Iterative Solution listener sets it to zero so it can find the next batch, so it has to be
    // executed
    // after initialize listener.
    final int solutionNoBeforeSearch = solutionListener.solutionsNo();

    // If constraints employ only one time execution of the part of
    // the consistency technique then the results of that part must be
    // stored in one level above the level search starts from as this
    // can be removed.
    boolean result = store.consistency();
    store.setLevel(store.level + 1);
    depth = store.level;

    if (timeOutCheck && (timeOutOccured || System.currentTimeMillis() > timeOut)) {
      timeOutOccured = true;
      return false;
    }

    if (result) {
      result = label(0);
    }

    store.removeLevel(store.level);
    store.setLevel(store.level - 1);
    depth--;

    if (exitListener != null) {
      exitListener.executedAtExit(store, solutionListener.solutionsNo());
    }

    if (solutionListener.solutionsNo() > solutionNoBeforeSearch) {

      if (printInfo) {
        if (costVariable != null) {
          CostVariableHandler costHandler =
              SearchHandlerRegistry.getInstance().findCostHandler(costVariable);
          if (costHandler != null) {
            double cost = costVariable instanceof IntVar ? costValue : costValueFloat;
            log.info("Solution cost is {}", cost);
          } else if (costVariable instanceof IntVar) {
            log.info("Solution cost is {}", costValue);
          }
        }

        log.info("{}", this);
      }

      if (raisedLevel) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
      }

      if (timeOutCheck && (timeOutOccured || System.currentTimeMillis() > timeOut)) {
        timeOutOccured = true;

        if (printInfo) {
          log.info("Time-out {}s", tOut);
        }

        return false;
      } else if (masterSearch == null) {
        return true;
      } else {
        return result;
      }

    } else {

      if (printInfo) {

        log.info("No solution found.");

        log.info(
            "Depth First Search {}\n\nNodes : {}\nDecisions : {}\nWrong Decisions : {}\nBacktracks : {}\nMax Depth : {}",
            searchId,
            nodes,
            decisions,
            wrongDecisions,
            numberBacktracks,
            maxDepthExcludePaths);
      }

      if (raisedLevel) {
        store.removeLevel(store.level);
        store.setLevel(store.level - 1);
      }

      if (timeOutCheck && (timeOutOccured || System.currentTimeMillis() > timeOut)) {
        timeOutOccured = true;

        if (printInfo) {
          log.info("Time-out {}s", tOut);
        }
      }

      return false;
    }
  }

  /**
   * Performs labeling using the given store and choice point selection heuristic.
   *
   * @param store the constraint store.
   * @param select the choice point selection heuristic.
   * @return true if a solution was found, false otherwise.
   */
  public boolean labeling(Store store, SelectChoicePoint<T> select) {

    this.store = store;

    if (store.raiseLevelBeforeConsistency) {
      store.raiseLevelBeforeConsistency = false;
      store.setLevel(store.level + 1);
    }

    heuristic = select;
    depth = store.level;

    if (costVariable == null) {
      optimize = false;
    }

    if (initializeListener != null) {
      initializeListener.executedAtInitialize(store);
    }

    // Iterative Solution listener sets it to zero so it can find the next batch, so it has to be
    // executed
    // after initialize listener.
    final int solutionNoBeforeSearch = solutionListener.solutionsNo();

    boolean result = store.consistency();
    store.setLevel(store.level + 1);
    depth = store.level;

    if (result) {
      result = label(0);
      if (printInfo) {
        log.info("Labeling has finished with return value of {}", result);
      }
    }
    store.removeLevel(store.level);
    store.setLevel(store.level - 1);
    depth--;

    if (exitListener != null) {
      exitListener.executedAtExit(store, solutionListener.solutionsNo() - solutionNoBeforeSearch);
    }

    if (timeOutOccured && printInfo) {
      log.info("Time-out {}s", tOut);
    }

    if (solutionListener.solutionsNo() > solutionNoBeforeSearch) {

      if (assignSolution) {
        assignSolution();
      }

      if (printInfo) {
        log.info("{}", this);
      }

      return true;
    } else {

      if (printInfo) {

        log.info("No solution found.");

        log.info(
            "Depth First Search {}\n\nNodes : {}\nDecisions : {}\nWrong Decisions : {}\nBacktracks : {}\nMax Depth : {}",
            searchId,
            nodes,
            decisions,
            wrongDecisions,
            numberBacktracks,
            maxDepthExcludePaths);
      }
      return false;
    }
  }

  /**
   * Performs optimization labeling using the given store, choice point selection, and cost
   * variable.
   *
   * @param store the constraint store.
   * @param select the choice point selection heuristic.
   * @param costVar the variable representing the cost to be minimized.
   * @return true if an optimal solution was found, false otherwise.
   */
  public boolean labeling(Store store, SelectChoicePoint<T> select, Var costVar) {

    this.store = store;

    if (store.raiseLevelBeforeConsistency) {
      store.raiseLevelBeforeConsistency = false;
      store.setLevel(store.level + 1);
    }

    heuristic = select;
    depth = store.level;
    costVariable = costVar;
    optimize = true;
    cost = null;

    if (initializeListener != null) {
      initializeListener.executedAtInitialize(store);
    }

    // Iterative Solution listener sets it to zero so it can find the next batch, so it has to be
    // executed
    // after initialize listener.
    final int solutionNoBeforeSearch = solutionListener.solutionsNo();

    boolean result = store.consistency();
    store.setLevel(store.level + 1);
    depth = store.level;

    if (result) {
      result = label(0);
      if (printInfo) {
        log.info("Labeling has finished with return value of {}", result);
      }
    }
    store.removeLevel(store.level);
    store.setLevel(store.level - 1);
    depth--;

    if (exitListener != null) {
      exitListener.executedAtExit(store, solutionListener.solutionsNo());
    }

    if (timeOutOccured && printInfo) {
      log.info("Time-out {}s", tOut);
    }

    if (solutionListener.solutionsNo() > solutionNoBeforeSearch) {

      if (assignSolution) {
        assignSolution();
      }

      if (printInfo && costVariable != null) {
        CostVariableHandler costHandler =
            SearchHandlerRegistry.getInstance().findCostHandler(costVariable);
        if (costHandler != null) {
          DomainOperationHandler domainHandler =
              SearchHandlerRegistry.getInstance().findDomainHandler(costVariable);
          if (domainHandler != null) {
            log.info("Solution cost is {}", domainHandler.getDomainString(costVariable));
          } else {
            double cost = costVariable instanceof IntVar ? costValue : costValueFloat;
            log.info("Solution cost is {}", cost);
          }
        } else if (costVariable instanceof IntVar) {
          log.info("Solution cost is {}", costValue);
        }
      }

      if (printInfo) {
        log.info("{}", this);
      }

      return true;

    } else {

      if (printInfo) {

        log.info("No solution found.");

        log.info(
            "Depth First Search {}\n\nNodes : {}\nDecisions : {}\nWrong Decisions : {}\nBacktracks : {}\nMax Depth : {}",
            searchId,
            nodes,
            decisions,
            wrongDecisions,
            numberBacktracks,
            maxDepthExcludePaths);
      }
      return false;
    }
  }

  // KKU, 2015-12-17: might be used to set cost variable and
  // optimization = true for all sub-searches does not do it
  // automatically since it might not be the intention (we might
  // want to find only a single solution in the sub-search). This is
  // why it is not added to labeling with costVar.
  @SuppressWarnings("unchecked")
  void setOptimizationForChildSearches(DepthFirstSearch<T> s, Var costVar) {

    // set cost and optimization for child searches
    if (s != null) {
      DepthFirstSearch<T>[] childs = (DepthFirstSearch<T>[]) s.childSearches;
      if (childs != null) {
        for (DepthFirstSearch<T> child : childs) {
          child.setCostVar(costVar);
          child.setOptimize(true);
          setOptimizationForChildSearches(child, costVar);
        }
      }
    }
  }

  /**
   * It turns on the backtrack out.
   *
   * @param out defines how many backtracks are performed before the search exits.
   */
  public void setBacktracksOut(long out) {
    backtracksOut = out;
    check = true;
    backtracksOutCheck = true;
  }

  /**
   * It turns on the decisions out.
   *
   * @param out defines how many decisions are made before the search exits.
   */
  public void setDecisionsOut(long out) {
    decisionsOut = out;
    check = true;
    decisionsOutCheck = true;
  }

  /**
   * It turns on the nodes out.
   *
   * @param out defines how many nodes are visited before the search exits.
   */
  public void setNodesOut(long out) {
    nodesOut = out;
    check = true;
    nodesOutCheck = true;
  }

  /**
   * It turns on the timeout.
   *
   * @param out defines how many seconds before the search exits.
   */
  public void setTimeOut(long out) {
    tOut = out;
    check = true;
    timeOutCheck = true;
    timeOut = System.currentTimeMillis() + tOut * 1000;
  }

  /**
   * Sets the timeout in milliseconds after which the search will exit.
   *
   * @param out the number of milliseconds before the search exits.
   */
  public void setTimeOutMilliseconds(long out) {
    tOut = out;
    check = true;
    timeOutCheck = true;
    timeOut = System.currentTimeMillis() + tOut;
  }

  /**
   * It turns on the wrong decisions out.
   *
   * @param out defines how many wrong decisions are made before the search exits.
   */
  public void setWrongDecisionsOut(long out) {
    wrongDecisionsOut = out;
    check = true;
    wrongDecisionsOutCheck = true;
  }

  @Override
  public String toString() {

    return searchId + ": DFS(" + heuristic + ")";
  }

  /**
   * Returns a detailed string representation of this search including statistics.
   *
   * @return full string representation with nodes, decisions, backtracks, and depth info.
   */
  public String toStringFull() {

    StringBuilder buf = new StringBuilder();

    buf.append("Depth First Search ").append(searchId).append("\n");

    buf.append(heuristic);

    buf.append("\n").append(solutionListener.toString());

    if (costVariable != null) {
      CostVariableHandler costHandler =
          SearchHandlerRegistry.getInstance().findCostHandler(costVariable);
      if (costHandler != null) {
        DomainOperationHandler domainHandler =
            SearchHandlerRegistry.getInstance().findDomainHandler(costVariable);
        if (domainHandler != null) {
          buf.append("Cost ").append(domainHandler.getDomainString(costVariable)).append("\n");
        } else {
          double cost = costVariable instanceof IntVar ? costValue : costValueFloat;
          buf.append("Cost ").append(cost).append("\n");
        }
      } else if (costVariable instanceof IntVar) {
        buf.append("Cost ").append(costValue).append("\n");
      }
    }

    buf.append("Nodes : ").append(nodes).append("\n");
    buf.append("Decisions : ").append(decisions).append("\n");
    buf.append("Wrong Decisions : ").append(wrongDecisions).append("\n");
    buf.append("Backtracks : ").append(numberBacktracks).append("\n");
    buf.append("Max Depth : ").append(maxDepthExcludePaths).append("\n");

    return buf.toString();
  }

  /**
   * Assigns the most recent solution to the store.
   *
   * @return true if the solution was successfully assigned, false otherwise.
   */
  public boolean assignSolution() {

    if (solutionListener.solutionsNo() != 0) {
      return assignSolution(solutionListener.solutionsNo() - 1);
    } else {
      return assignSolution(0);
    }
  }

  /**
   * Assigns the specified solution to the store.
   *
   * @param no the solution number to assign.
   * @return true if the solution was successfully assigned, false otherwise.
   */
  public boolean assignSolution(int no) {

    boolean result;

    if (solutionListener.isRecordingSolutions()) {
      result = solutionListener.assignSolution(store, no);
    } else {
      result = solutionListener.assignSolution(store, 0);
    }

    if (!result) {
      return false;
    }

    if (childSearches != null) {
      int match = -1;

      currentChildSearch = 0;
      for (; currentChildSearch < childSearches.length && match == -1; currentChildSearch++) {
        match =
            childSearches[currentChildSearch].getSolutionListener().findSolutionMatchingParent(no);
      }

      if (match == -1) {
        return false;
      }
      return childSearches[currentChildSearch - 1].assignSolution(match);
    }

    return true;
  }

  /** Prints all solutions found by this search. */
  public void printAllSolutions() {
    solutionListener.printAllSolutions();
  }
}
