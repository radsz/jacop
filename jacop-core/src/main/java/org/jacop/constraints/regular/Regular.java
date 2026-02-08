/*
 * Regular.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2008 Polina Maakeva and Radoslaw Szymanek
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

package org.jacop.constraints.regular;

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
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
import org.jacop.constraints.ExtensionalSupportStr;
import org.jacop.constraints.In;
import org.jacop.constraints.XeqC;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.TimeStamp;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.util.Mdd;
import org.jacop.util.fsm.Fsm;
import org.jacop.util.fsm.FsmState;
import org.jacop.util.fsm.FsmTransition;

/**
 * Regular constraint accepts only the assignment to variables which is accepted by an automaton.
 * This constraint implements a polynomial algorithm to establish GAC. There are number of
 * improvements (iterative execution, optimization of computational load upon backtracking) to
 * improve the constraint further.
 *
 * @author Polina Makeeva and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class Regular extends Constraint implements UsesQueueVariable, Stateful, RemoveLevelLate {

  /** It specifies if debugging information should be printed out. */
  public static final boolean debugAll = false;

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It specifies if the translation of Fsm into optimized Mdd should take place so minimal layered
   * graph can be obtained. This option most of the time causes out of memory exception as it
   * requires finding and storing all solutions in mtrie before translation to an optimized Mdd can
   * take place. Fsm also has to be a deterministic one.
   */
  public final boolean optimizedMdd = false;

  /** It specifies if the edges should have a list of values associated with them. */
  public final boolean listRepresentation = true;

  /** It specifies if the support functionality should be used. */
  public final boolean oneSupport = true;

  /** It specifies finite state machine used by this regular. */
  public final Fsm fsm;

  /** Array of the variables of the graph levels. */
  public final IntVar[] list;

  /**
   * Queue of changed variables. TODO try to use PriorityQueue based on the number of states for a
   * given variable or a domain size to pickup first variables which may result in failure faster.
   * It does not have to be fully correct ordering.
   */
  final LinkedHashSet<IntVar> variableQueue = new LinkedHashSet<>();

  /**
   * Name of the file to store the latex output after consistency call The output will be :
   * file_name + "call number" + ".tex".
   */
  public String latexFile = "/home/radek/";

  /**
   * DNames contain a "name" for each value from the union of all variabl's domains. If Hashmap -
   * dNames - is not null then upon saving the latex graph the values on the edges will be replaced
   * with their "names".
   */
  public Map<Integer, String> dNames;

  /** It keeps for each variable value pair a current support. */
  public Map<Integer, RegEdge>[] supports;

  /** Number of states in the graph used only during the printing to latex function. */
  int stateNumber;

  Map<IntVar, Integer> mapping;

  /**
   * Consistency function call the prune arc function for every pruned variable and collect
   * information about the levels that had some changes in "levelHadChaged" array Then it collect
   * the values of the edges that are still active on the levels that had chages and update the
   * domains of the variables.
   */
  boolean firstConsistencyCheck = true;

  boolean[] levelHadChanged;
  int firstConsistencyLevel;
  List<Constraint> constraints;
  RegState[] touchedStates;
  int[] lastNumberOfActiveStates;

  /** This is the counter of save-to-latex calls. */
  private int calls;

  /** The ith smallest level of Layered Graph which have changed. */
  private TimeStamp<Integer> leftChange;

  /** The ith largest level of Layered Graph which have changed. */
  private TimeStamp<Integer> rightChange;

  /** The position of the currentTouchedIndex. */
  private TimeStamp<Integer> touchedIndex;

  /** Stores the states of all graph levels. */
  private RegState[][] stateLevels;

  /** Time-stamp for the number of active states in each level. */
  private TimeStamp<Integer>[] activeLevels;

  private int[] activeLevelsTemp;
  private Integer leftPosition;
  private Integer rightPosition;
  private int currentTouchedIndex;

  /**
   * Constructor need Store to initialize the time-stamps.
   *
   * @param fsm (deterministic) finite automaton
   * @param list variables which values have to be accepted by the automaton.
   */
  public Regular(Fsm fsm, IntVar[] list) {

    checkInputForNullness("list", list);
    checkInputForDuplicationSkipSingletons("list", list);

    this.queueIndex = 3;
    this.list = Arrays.copyOf(list, list.length);
    this.fsm = fsm;
    numberId = idNumber.incrementAndGet();
    leftPosition = 0;
    rightPosition = list.length - 1;
    touchedStates = new RegState[fsm.allStates.size() * list.length];
    setScope(list);
  }

  /**
   * Initialization phase of the algorithm.
   *
   * <p>Considering that it needs to initialize the array of graph States - stateLevels, and, thus,
   * it needs to know the actual number of the states on each level I found nothing better then run
   * the initialization phase with the complete NxN array of states and then copy the useful ones
   * into a final array (which is ugly)
   *
   * @param dfa specification of deterministic finite automaton.
   */
  private void initializeArray(Fsm dfa) {

    int levels = this.list.length;
    stateNumber = dfa.allStates.size();

    // The array that keep all possible states with arcs and their domains
    // If the domain is empty then the arc doesn't exist
    final IntDomain[][][] outarc = new IntervalDomain[levels + 1][stateNumber][stateNumber];
    final int[][] outdeg = new int[levels + 1][stateNumber];

    // Reachable region of the graph
    final Set<FsmState> reachable = new HashSet<>();
    // Temporal variable for reachable region
    final Set<FsmState> tmp = new HashSet<>();

    // Initialization of the future state array
    // and the time-stamps with the number of active states
    this.stateLevels = new RegState[levels + 1][];

    FsmState[] array = new FsmState[stateNumber];

    dfa.resize();
    for (FsmState s : dfa.allStates) {
      array[s.id] = s;
    }

    // ----- compute the reachable region of the graph -----

    // Start with initial state
    reachable.add(dfa.initState);

    int level = 0;
    while (level < levels) {
      // prepare tmp set of reachable states in the next level
      tmp.clear();
      // For each state reached until now
      for (FsmState s : reachable) {
        // watch it's edges
        for (FsmTransition t : s.transitions) {
          // prepare the set of values of this edge
          IntDomain dom = t.domain.intersect(list[level].dom());

          if (outarc[level][s.id][t.successor.id] != null) {
            outarc[level][s.id][t.successor.id].addDom(dom);
          } else {
            outarc[level][s.id][t.successor.id] = dom;
          }

          /* If the edge is not empty them add the state to tmp set
           * check that such states wasn't previously added.
           *
           * <p>If the level is the last, then check whether the state
           * belongs to the set of accepted states
           */

          if (dom.getSize() > 0) {
            if (level < levels - 1) {
              tmp.add(t.successor);
            } else if (dfa.finalStates.contains(t.successor)) {
              tmp.add(t.successor);
            }
          }
        }
      }

      // copy the tmp set of states into reachable region
      reachable.clear();
      reachable.addAll(tmp);
      // got to next level
      level++;
    }

    // initialize the last time-stamp because the counter didn't reach it.
    /* ----- delete the paths of the graph that doesn't reach the accepted state -----
     *
     *
     *  by calculating the reachable region of the graph starting from the accepted
     *  states and following the edges in the opposite direction.
     */

    while (level > 0) {
      tmp.clear();

      stateLevels[level] = new RegState[reachable.size()];

      for (int i = 0; i < stateNumber; i++) {
        for (int j = 0; j < stateNumber; j++) {
          if (outarc[level - 1][j][i] != null && outarc[level - 1][j][i].getSize() > 0) {
            if (!reachable.contains(array[i])) {
              outarc[level - 1][j][i].clear();
            } else {
              outdeg[level - 1][j] += outarc[level - 1][j][i].getSize();
              tmp.add(array[j]);
            }
          }
        }
      }

      reachable.clear();
      reachable.addAll(tmp);
      level--;
    }

    stateLevels[0] = new RegState[1];
    this.activeLevelsTemp = new int[this.list.length + 1];

    // ---- copy the resulting graph into final array ----
    int index;
    int nextLevelIndex = 0;

    for (level = 0; level < levels; level++) {
      index = nextLevelIndex;
      nextLevelIndex = 0;

      for (int i = 0; i < stateNumber; i++) {
        if (outdeg[level][i] > 0) {
          // If the outdegree of the sate is not 0 then its should be created
          RegState s = getState(level, i); // Check if it wasn't already created
          if (s == null) { // If not -> create the state
            if (listRepresentation) {
              s = new RegStateInt(level, i, outdeg[level][i], index);
            } else {
              s = new RegStateDom(level, i, outdeg[level][i], index);
            }

            stateLevels[level][index++] = s; // Add new state to the list of states of this level

            activeLevelsTemp[level] = index;

            if (debugAll) {
              log.debug(
                  "Create new state q_{}{} with in degree : {} and out degree : {}",
                  level,
                  i,
                  s.inDegree,
                  s.outDegree);
            }
          }

          // For every outgoing arc
          for (int j = 0; j < stateNumber; j++) {
            // If transition is active
            if (outarc[level][i][j] != null && outarc[level][i][j].getSize() > 0) {
              RegState suc = getState(level + 1, j); // See if such state already exists
              if (suc == null) {
                if (listRepresentation) {
                  suc = new RegStateInt(level + 1, j, outdeg[level + 1][j], nextLevelIndex);
                } else {
                  suc = new RegStateDom(level + 1, j, outdeg[level + 1][j], nextLevelIndex);
                }

                stateLevels[level + 1][nextLevelIndex++] = suc;

                activeLevelsTemp[level + 1] = nextLevelIndex;

                if (debugAll) {
                  log.debug(
                      "Create new state q_{}{} with in degree : {} and out degree : {}",
                      level + 1,
                      j,
                      suc.inDegree,
                      suc.outDegree);
                }
              }

              s.addTransitions(suc, (IntervalDomain) outarc[level][i][j]);

              if (debugAll) {
                log.debug(
                    "--  state q_{}{} with in degree : {} and out degree : {}",
                    level,
                    i,
                    s.inDegree,
                    s.outDegree);
              }

              if (debugAll) {
                log.debug(
                    "--  state q_{}{} with in degree : {} and out degree : {}",
                    level + 1,
                    j,
                    suc.inDegree,
                    suc.outDegree);
              }
            }
          }
        }
      }
    }
  }

  /**
   * Initialization phase of the algorithm.
   *
   * <p>Considering that it needs to initialize the array of graph States - stateLevels, and, thus,
   * it needs to know the actual number of the states on each level I found nothing better then run
   * the initialization phase with the complete NxN array of states and then copy the useful ones
   * into a final array (which is ugly)
   */
  @SuppressWarnings("unchecked")
  private void initializeArray(Mdd mdd) {

    int levels = this.list.length;

    // Initialization of the future state array
    // and the time-stamps with the number of active states
    this.stateLevels = new RegState[levels + 1][];

    List<RegState>[] layeredGraph =
        (ArrayList<RegState>[]) Array.newInstance(ArrayList.class, levels + 1);
    for (int i = 0; i < layeredGraph.length; i++) {
      layeredGraph[i] = new ArrayList<>();
    }

    this.activeLevelsTemp = new int[this.list.length + 1];

    final int[] currentPosition = new int[list.length];
    final int[] currentOffset = new int[list.length];
    RegState[] currentState = new RegState[list.length + 1];

    int currentLevel = 0;
    int noNeighbours = 0;

    for (int i = 0; i < list[0].getSize(); i++) {
      if (mdd.diagram[i] != Mdd.NOEDGE) {
        noNeighbours++;
      }
    }

    currentState[0] =
        new RegStateInt(currentLevel, 0, noNeighbours, activeLevelsTemp[currentLevel]++);
    currentState[list.length] = new RegStateInt(list.length, 0, 0, activeLevelsTemp[list.length]++);

    layeredGraph[0].add(currentState[currentLevel]);
    layeredGraph[list.length].add(currentState[list.length]);

    currentPosition[0] = 0;
    currentOffset[0] = 0;
    currentLevel = 0;

    while (currentLevel != -1) {

      if (currentOffset[currentLevel] >= list[currentLevel].getSize()) {
        currentLevel--;
        if (currentLevel >= 0) {
          currentOffset[currentLevel]++;
        }
        continue;
      }

      int nextNodePosition =
          mdd.diagram[currentPosition[currentLevel] + currentOffset[currentLevel]];

      // no path with a given value from a current node.
      if (nextNodePosition == Mdd.NOEDGE) {
        currentOffset[currentLevel]++;
        continue;
      }

      if (nextNodePosition == Mdd.TERMINAL) {
        currentState[currentLevel].addTransition(
            currentState[list.length],
            mdd.views[currentLevel].indexToValue[currentOffset[currentLevel]]);
        currentOffset[currentLevel]++;
        continue;
      }

      boolean visited = false;

      RegState s = null;
      for (RegState state : layeredGraph[currentLevel + 1]) {
        if (state.id == nextNodePosition) {
          s = state;
          visited = true;
        }
      }

      if (s == null) {
        noNeighbours = 0;

        if (currentLevel + 1 < list.length) {
          for (int j = nextNodePosition;
              j < nextNodePosition + list[currentLevel + 1].getSize();
              j++) {
            if (mdd.diagram[j] != Mdd.NOEDGE) {
              noNeighbours++;
            }
          }
        }

        s =
            new RegStateInt(
                currentLevel + 1,
                nextNodePosition,
                noNeighbours,
                activeLevelsTemp[currentLevel + 1]++);
        layeredGraph[currentLevel + 1].add(s);
      }

      currentState[currentLevel].addTransition(
          s, mdd.views[currentLevel].indexToValue[currentOffset[currentLevel]]);

      if (visited) {
        currentOffset[currentLevel]++;
        continue;
      }

      currentLevel++;

      currentState[currentLevel] = s;
      currentOffset[currentLevel] = 0;
      currentPosition[currentLevel] = nextNodePosition;
    }

    for (int i = 0; i < layeredGraph.length; i++) {
      stateLevels[i] = new RegState[layeredGraph[i].size()];
      int j = 0;
      for (RegState state : layeredGraph[i]) {
        stateLevels[i][j] = state;
        j++;
      }
    }
  }

  /**
   * Find the state with the corresponding id.
   *
   * @param level specifies the variable for which the state is seeked for.
   * @param id specifies the id of the state.
   * @return the state at given level with a given id.
   */
  public RegState getState(int level, int id) {

    for (int i = 0; i < stateLevels[level].length; i++) {
      if (stateLevels[level][i] != null && stateLevels[level][i].id == id) {
        return stateLevels[level][i];
      }
    }
    return null;
  }

  /**
   * Collects the damaged states, after pruning the domain of variable "var", and put these states
   * in two separated sets.
   *
   * <p>One with the states with zero incoming degree - these are the candidates for the forward
   * part. The other set consists of states with zero out-coming degree - these are the candidates
   * for backward part.
   *
   * @param varIndex the index of the variable which have changed.
   */
  public void pruneArc(int varIndex) {

    int state;
    int preThisLevelStateNb = this.activeLevels[varIndex].value();
    RegState s;
    RegState suc;
    int nextVar = varIndex + 1;
    int preNextLevelStateNb = this.activeLevels[nextVar].value();

    levelHadChanged[varIndex] = true;

    IntDomain domVar = list[varIndex].domain;

    for (state = preThisLevelStateNb - 1; state >= 0; state--) {

      s = stateLevels[varIndex][state];
      if (debugAll) {
        log.debug("{}: watch state q_{}{}", state, varIndex, s.id);
      }

      boolean alreadyTouched = false;

      for (int i = s.outDegree - 1; i >= 0; i--) {
        // If this transition must be removes because it is not in var's domain
        if (!s.intersects(domVar, i)) {

          if (debugAll) {
            log.debug(
                "must remove transition q_{}{} -{}-> q_{}{}",
                varIndex,
                s.id,
                s.sucDomToString(i),
                varIndex + 1,
                s.successors[i].id);
          }

          // we remove this transition (we know its index, so its easy)
          // This will automatically reduce the out-degree of this state
          // and reduce in-degree of the successor.

          suc = s.successors[i];
          s.removeTransition(i);

          if (!alreadyTouched) {
            addTouchedState(s);
            alreadyTouched = true;
          }

          if (debugAll) {
            log.debug(
                "--  state q_{}{} with in degree : {} and out degree : {}",
                s.level,
                s.id,
                s.inDegree,
                s.outDegree);
            log.debug(
                "--  state q_{}{} with in degree : {} and out degree : {}",
                suc.level,
                suc.id,
                suc.inDegree,
                suc.outDegree);
          }

          assert s.outDegree >= 0;

          if (s.outDegree == 0) {
            if (debugAll) {
              log.debug("Move OUT state out of scope : q_{}{}", varIndex, s.id);
            }
            assert s.level == varIndex;
            disableState(varIndex, s.pos);
          }

          assert suc.inDegree >= 0;

          if (suc.inDegree == 0) {
            if (debugAll) {
              log.debug("Move IN state out of scope : q_{}{}", suc.level, suc.id);
            }
            assert suc.level == varIndex + 1;
            disableState(nextVar, suc.pos);
            levelHadChanged[nextVar] = true;
          }
        }
      }
    }

    unreachForwardLoop(preNextLevelStateNb, varIndex + 1);
    unreachBackwardLoop(preThisLevelStateNb, varIndex - 1);
  }

  private void addTouchedState(RegState s) {

    if (currentTouchedIndex < touchedStates.length) {
      touchedStates[currentTouchedIndex++] = s;
    } else {

      RegState[] newTouchedStates = new RegState[touchedStates.length * 2];
      System.arraycopy(touchedStates, 0, newTouchedStates, 0, touchedStates.length);
      touchedStates = newTouchedStates;
    }
  }

  /**
   * It does backward check to remove inactive edges and states.
   *
   * @param sucPrevLimit previous number of states at a given level.
   * @param level level for which the backward sweep is computed.
   * @return level at which the sweep has ended. TODO return value is not used.
   */
  public int unreachBackwardLoop(int sucPrevLimit, int level) {

    RegState s;

    boolean cont = sucPrevLimit != this.activeLevels[level + 1].value();

    while (level >= 0 && cont) {

      cont = false;

      levelHadChanged[level] = true;

      for (int sPos = this.activeLevels[level].value() - 1; sPos >= 0; sPos--) {

        s = this.stateLevels[level][sPos];

        boolean alreadyTouched = false;
        for (int sucIndex = s.outDegree - 1; sucIndex >= 0; sucIndex--) {
          if (!s.successors[sucIndex].isActive(activeLevels)) {
            s.removeTransition(sucIndex);
            if (!alreadyTouched) {
              addTouchedState(s);
              alreadyTouched = true;
            }
          }
        }

        assert s.outDegree >= 0 : "Negative successor number of q_" + s.level + s.id;

        if (s.outDegree == 0) {
          assert s.level == level;
          disableState(level, sPos);
          cont = true;
        }
      }

      level--;
    }

    return level;
  }

  /**
   * Forward part deletes the outgoing edges of the damaged state and watch whether the successors
   * are still active (in-degree {@literal >} 0 ), otherwise we collect it and continue the loop.
   *
   * <p>TODO return value is not used.
   *
   * @param end the position of the last active state at a given level.
   * @param level level being examined.
   */
  public void unreachForwardLoop(int end, int level) {

    int state;
    RegState s;
    RegState suc;

    int preNextLevelStateNb;

    int currentLimit = this.activeLevels[level].value();

    boolean cont = currentLimit != end;

    while (level < this.list.length && cont) {

      levelHadChanged[level] = true;

      cont = false;

      preNextLevelStateNb = this.activeLevels[level + 1].value();

      for (state = currentLimit; state < end; state++) {
        s = stateLevels[level][state];

        // We are removing a damaged state, thus, all its arcs are removed and
        // we must remember maximal degree of it

        for (int i = s.outDegree - 1; i >= 0; i--) {

          suc = s.successors[i];
          suc.inDegree--;

          if (debugAll) {
            log.debug(
                "watch transition q_{}{} -{}-> q_{}{}",
                s.level,
                s.id,
                s.sucDomToString(i),
                suc.level,
                suc.id);
          }

          assert suc.inDegree >= 0 : "Negative indegree of successor state" + suc.level + suc.id;

          if (suc.inDegree == 0) {
            if (debugAll) {
              log.debug("> Move IN state out of scope : q_{}{}", suc.level, suc.id);
            }
            // changed to directl disableState(int, int).
            assert suc.level == level + 1;
            disableState(level + 1, suc.pos);
            // @todo levelHasChanged[level+1] = true
            cont = true;
          }
        }

        s.outDegree = 0;
      }

      end = preNextLevelStateNb;
      currentLimit = activeLevels[level + 1].value();
      level++;
    }
  }

  /**
   * It marks state as being not active.
   *
   * @param level level at which the state is residing.
   * @param pos position of the state in the array of states.
   */
  public void disableState(int level, int pos) {

    int lim = activeLevels[level].value();

    assert pos < lim;

    RegState s = stateLevels[level][pos];

    // it must be before the remaining operations
    lim--;

    stateLevels[level][pos] = stateLevels[level][lim];
    stateLevels[level][pos].pos = pos;
    stateLevels[level][lim] = s;
    s.pos = lim;
    activeLevels[level].update(lim);
  }

  @Override
  public void removeLevel(int level) {

    assert level > firstConsistencyLevel
        : "Constraint has the level at which it has computed its initial state being removed.";

    this.variableQueue.clear();

    if (leftChange.value() < leftPosition) {
      leftPosition = leftChange.value();
    }

    if (rightChange.value() > rightPosition) {
      rightPosition = rightChange.value();
    }

    for (int l = leftPosition; l <= rightPosition; l++) {
      lastNumberOfActiveStates[l] = activeLevels[l].value();
    }
  }

  /** Sweep the graph upon backtracking. */
  @Override
  public void removeLevelLate(int level) {

    RegState curState;
    int prevVal;

    int checkToIndex = touchedIndex.value();

    while (currentTouchedIndex > checkToIndex) {

      curState = touchedStates[--currentTouchedIndex];

      RegState[] successors = curState.successors;
      prevVal = curState.outDegree;
      curState.outDegree = successors.length;

      for (int i = prevVal; i < curState.outDegree; i++) {
        if (!(successors[i].isActive(activeLevels)
            && curState.intersects(list[curState.level].domain, i))) {
          curState.outDegree = i;
        } else {
          successors[i].inDegree++;
        }
      }
    }

    int stateNb;

    // for every level which has been recorded be in between the levels which have changed
    for (int l = leftPosition; l <= rightPosition; l++) {
      // for every active state in the level
      stateNb = this.activeLevels[l].value();

      // for (int s = 0; s < stateNb; s++) {
      for (int s = lastNumberOfActiveStates[l]; s < stateNb; s++) {
        // update its out degree by adding the accumulator
        // by doing this we add some old, possibly inactive edge
        curState = stateLevels[l][s];
        RegState[] successors = curState.successors;
        prevVal = curState.outDegree;
        curState.outDegree = successors.length;
        // for every new added edge is active
        // if it is not, then stop
        for (int i = prevVal; i < curState.outDegree; i++) {
          if (!(successors[i].isActive(activeLevels) && curState.intersects(list[l].domain, i))) {
            curState.outDegree = i;
          } else {
            successors[i].inDegree++;
          }
        }
      }
    }

    if (debugAll) {
      log.debug("..next prunning");
    }

    leftPosition = list.length;
    rightPosition = 0;
  }

  @Override
  public void queueVariable(int level, Var var) {

    variableQueue.add((IntVar) var);
  }

  @Override
  public void consistency(Store store) {

    if (firstConsistencyCheck) {

      RegState state;

      if (oneSupport) {

        for (int level = list.length - 1; level >= 0; level--) {

          // first restrict the domain to the sum of all edges annotations.

          IntervalDomain initial = new IntervalDomain();

          for (Integer value : supports[level].keySet()) {
            initial.unionAdapt(value, value);
          }

          this.list[level].domain.in(store.level, list[level], initial);

          ValueEnumeration enumer = list[level].domain.valueEnumeration();

          for (int v; enumer.hasMoreElements(); ) {

            v = enumer.nextElement();

            if (supports[level].get(v) == null) {
              this.list[level].domain.inComplement(store.level, list[level], v);
              enumer.domainHasChanged();
              continue;
            }

            RegEdge edge = supports[level].get(v);
            // function check - checks if there is a support, starting from the
            // current one.

            if (!edge.check(activeLevels)) {
              boolean stillSuported = false;
              for (int st = activeLevels[level].value() - 1; st >= 0; st--) {
                if (stateLevels[level][st].updateSupport(edge, v)) {
                  stillSuported = true;
                  break;
                }
              }

              if (!stillSuported) {
                list[level].domain.inComplement(store.level, list[level], v);
                enumer.domainHasChanged();
              }
            }
          }
        }
      } else {

        IntDomain varDom;

        for (int level = this.list.length - 1; level >= 0; level--) {
          varDom = new IntervalDomain();
          for (int s = activeLevels[level].value() - 1; s >= 0; s--) {
            state = this.stateLevels[level][s];
            for (int i = state.outDegree - 1; i >= 0; i--) {
              state.add(varDom, i);
            }
          }
          if (debugAll) {
            log.debug(
                ">>> Variable x_{} had domain {} and now its {}",
                level,
                this.list[level].domain,
                varDom);
          }
          this.list[level].domain.in(store.level, list[level], varDom);
        }
      }

      firstConsistencyCheck = false;
      firstConsistencyLevel = store.level;

      if (variableQueue.isEmpty()) {
        return;
      }
    }

    RegState state;

    Arrays.fill(levelHadChanged, false);

    for (Var var : variableQueue) {
      pruneArc(mapping.get(var));
    }

    // if two consistency functions executed one after the other
    // then timestamp may be asked to update to the same value. If that
    // request does not create new level because value at older level
    // is equal then here the leftChange and rightChange will not be
    // updated correctly.

    if (leftChange.stamp() < store.level) {
      for (int i = 0; i < levelHadChanged.length; i++) {
        if (levelHadChanged[i]) {
          leftChange.update(i);
          break;
        }
      }
    } else {
      int leftEnd = leftChange.value();
      for (int i = 0; i < leftEnd; i++) {
        if (levelHadChanged[i]) {
          leftChange.update(i);
          break;
        }
      }
    }

    if (rightChange.stamp() < store.level) {
      for (int i = levelHadChanged.length - 1; i >= 0; i--) {
        if (levelHadChanged[i]) {
          rightChange.update(i);
          break;
        }
      }
    } else {
      int rightEnd = rightChange.value();
      for (int i = levelHadChanged.length - 1; i > rightEnd; i--) {
        if (levelHadChanged[i]) {
          rightChange.update(i);
          break;
        }
      }
    }

    if (oneSupport) {

      for (int level = this.list.length - 1; level >= 0; level--) {
        if (levelHadChanged[level]) {

          ValueEnumeration enumer = this.list[level].domain.valueEnumeration();

          for (int v; enumer.hasMoreElements(); ) {

            v = enumer.nextElement();
            RegEdge edge = supports[level].get(v);
            // function check - checks if there is a support, starting from the
            // current one.
            if (!edge.check(activeLevels)) {

              boolean stillSuported = false;

              for (int st = activeLevels[level].value() - 1; st >= 0; st--) {
                if (stateLevels[level][st].updateSupport(edge, v)) {
                  stillSuported = true;
                  break;
                }
              }

              if (!stillSuported) {
                this.list[level].domain.inComplement(store.level, list[level], v);
                enumer.domainHasChanged();
              }
            }
          }
        }
      }
    } else {
      IntDomain varDom;
      for (int level = list.length - 1; level >= 0; level--) {
        if (levelHadChanged[level]) {
          varDom = new IntervalDomain();

          for (int s = activeLevels[level].value() - 1; s >= 0; s--) {
            state = stateLevels[level][s];
            for (int i = state.outDegree - 1; i >= 0; i--) {
              state.add(varDom, i);
            }
          }

          if (debugAll) {
            log.debug(
                ">>> Variable x_{} had domain {} and now its {}",
                level,
                list[level].domain,
                varDom);
          }

          list[level].domain.in(store.level, list[level], varDom);
        }
      }
    }

    touchedIndex.update(this.currentTouchedIndex);
  }

  @Override
  @SuppressWarnings("unchecked")
  public void impose(Store store) {

    if (optimizedMdd) {
      initializeArray(fsm.transformIntoMdd(list));
    } else {
      initializeArray(fsm);
    }

    super.impose(store);

    store.registerRemoveLevelLateListener(this);

    mapping = Var.positionMapping(list, true, this.getClass());

    lastNumberOfActiveStates = new int[list.length + 1];
    activeLevels = new TimeStamp[list.length + 1];
    for (int i = list.length; i >= 0; i--) {
      activeLevels[i] = new TimeStamp<>(store, activeLevelsTemp[i]);
    }

    leftChange = new TimeStamp<>(store, 0);
    touchedIndex = new TimeStamp<>(store, 0);

    rightChange = new TimeStamp<>(store, list.length - 1);

    activeLevelsTemp = null;

    if (oneSupport) {
      supports = (HashMap<Integer, RegEdge>[]) new HashMap[list.length];
      RegState state;
      for (int level = this.list.length - 1; level >= 0; level--) {
        supports[level] = new HashMap<>();

        for (int s = this.activeLevels[level].value() - 1; s >= 0; s--) {
          state = this.stateLevels[level][s];
          for (int i = state.outDegree - 1; i >= 0; i--) {
            state.setSupports(supports[level], i);
          }
        }
      }
    }

    levelHadChanged = new boolean[this.list.length + 1];
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder(id());
    result.append("( [ ");
    for (IntVar intVar : list) {
      result.append(intVar.id()).append(" ");
    }
    result.append(" ], Fsm \n");
    result.append(fsm.toString());
    result.append(")");

    return result.toString();
  }

  @Override
  public void imposeDecomposition(Store store) {

    if (constraints == null) {
      constraints = decompose(store);
    }

    for (Constraint c : constraints) {
      store.impose(c, queueIndex);
    }
  }

  @Override
  public List<Constraint> decompose(Store store) {

    fsm.resize();

    List<int[]> listOfTuples = new ArrayList<>();

    // tuples for transitions from not-intial states.

    for (FsmState state : fsm.allStates) {

      for (FsmTransition transition : state.transitions) {

        for (ValueEnumeration enumer = transition.domain.valueEnumeration();
            enumer.hasMoreElements(); ) {

          int[] row = {state.id, enumer.nextElement(), transition.successor.id};

          listOfTuples.add(row);
        }
      }
    }

    int[][] tuples = new int[listOfTuples.size()][];
    listOfTuples.toArray(tuples);

    IntVar[] q = new IntVar[list.length + 1];

    for (int i = 0; i < q.length; i++) {
      q[i] = new IntVar(store, "Q" + i, 0, fsm.allStates.size());
    }

    constraints = new ArrayList<>();

    for (int i = 0; i < q.length - 1; i++) {
      IntVar[] scope = {q[i], list[i], q[i + 1]};
      constraints.add(new ExtensionalSupportStr(scope, tuples));
    }

    constraints.add(new XeqC(q[0], fsm.initState.id));

    IntervalDomain finalQ = new IntervalDomain();
    for (FsmState finalState : fsm.finalStates) {
      finalQ.unionAdapt(finalState.id, finalState.id);
    }

    constraints.add(new In(q[q.length - 1], finalQ));

    if (debugAll) {
      for (int[] tuple : tuples) {
        StringBuilder sb = new StringBuilder();
        for (int val : tuple) {
          sb.append(val).append(" ");
        }
        log.debug("{}", sb);
        log.debug("{}", fsm);
        log.debug("{}", constraints);
      }
    }

    return constraints;
  }
}
