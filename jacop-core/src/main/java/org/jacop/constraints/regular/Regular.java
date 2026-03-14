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

import static org.jacop.core.Store.ASSERTS_ENABLED;

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
  public static final boolean DEBUG_ALL = false;

  private static final String STATE_Q_DEGREES =
      "--  state q_{}{} with in degree : {} and out degree : {}";

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /**
   * It specifies if the translation of Fsm into optimized Mdd should take place so minimal layered
   * graph can be obtained. This option most of the time causes out of memory exception as it
   * requires finding and storing all solutions in mtrie before translation to an optimized Mdd can
   * take place. Fsm also has to be a deterministic one.
   */
  private final boolean optimizedMdd = false;

  /** It specifies if the edges should have a list of values associated with them. */
  private final boolean listRepresentation = true;

  /** It specifies if the support functionality should be used. */
  private final boolean oneSupport = true;

  /** It specifies finite state machine used by this regular. */
  public final Fsm fsm;

  /** Array of the variables of the graph levels. */
  public final IntVar[] list;

  /** Queue of changed variables. */
  final LinkedHashSet<IntVar> variableQueue = new LinkedHashSet<>();

  /**
   * Name of the file to store the latex output after consistency call The output will be :
   * file_name + "call number" + ".tex".
   */
  private String latexFile = "/home/radek/";

  /**
   * DNames contain a "name" for each value from the union of all variabl's domains. If Hashmap -
   * dNames - is not null then upon saving the latex graph the values on the edges will be replaced
   * with their "names".
   */
  private Map<Integer, String> dNames;

  /** It keeps for each variable value pair a current support. */
  private Map<Integer, RegEdge>[] supports;

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
    final IntDomain[][][] outarc = new IntervalDomain[levels + 1][stateNumber][stateNumber];
    final int[][] outdeg = new int[levels + 1][stateNumber];
    final Set<FsmState> reachable = new HashSet<>();
    final Set<FsmState> tmp = new HashSet<>();
    this.stateLevels = new RegState[levels + 1][];
    FsmState[] array = new FsmState[stateNumber];
    dfa.resize();
    for (FsmState s : dfa.allStates) {
      array[s.id] = s;
    }
    int level = initializeArrayForwardReachable(dfa, levels, outarc, reachable, tmp);
    level =
        initializeArrayBackwardReachable(level, stateNumber, outarc, outdeg, reachable, tmp, array);
    stateLevels[0] = new RegState[1];
    this.activeLevelsTemp = new int[this.list.length + 1];
    initializeArrayCopyToStateLevels(levels, outarc, outdeg);
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
      currentLevel =
          initializeArrayStep(
              mdd,
              layeredGraph,
              currentPosition,
              currentOffset,
              currentState,
              currentLevel,
              list.length);
    }

    copyLayeredGraphToStateLevels(layeredGraph);
  }

  /**
   * Performs one step of the MDD traversal during initialization. Returns the new current level (or
   * -1 when backtracking past start).
   */
  private int initializeArrayStep(
      Mdd mdd,
      List<RegState>[] layeredGraph,
      int[] currentPosition,
      int[] currentOffset,
      RegState[] currentState,
      int currentLevel,
      int listLen) {
    if (currentOffset[currentLevel] >= list[currentLevel].getSize()) {
      int nextLevel = currentLevel - 1;
      if (nextLevel >= 0) {
        currentOffset[nextLevel]++;
      }
      return nextLevel;
    }

    int nextNodePosition = mdd.diagram[currentPosition[currentLevel] + currentOffset[currentLevel]];

    if (nextNodePosition == Mdd.NOEDGE) {
      currentOffset[currentLevel]++;
      return currentLevel;
    }

    if (nextNodePosition == Mdd.TERMINAL) {
      currentState[currentLevel].addTransition(
          currentState[listLen], mdd.views[currentLevel].indexToValue[currentOffset[currentLevel]]);
      currentOffset[currentLevel]++;
      return currentLevel;
    }

    RegState s = findStateInLayer(layeredGraph[currentLevel + 1], nextNodePosition);
    boolean visited = s != null;
    if (s == null) {
      s =
          createAndAddStateToLayeredGraph(
              mdd, layeredGraph, currentLevel, nextNodePosition, listLen);
    }

    currentState[currentLevel].addTransition(
        s, mdd.views[currentLevel].indexToValue[currentOffset[currentLevel]]);

    if (visited) {
      currentOffset[currentLevel]++;
      return currentLevel;
    }

    currentLevel++;
    currentState[currentLevel] = s;
    currentOffset[currentLevel] = 0;
    currentPosition[currentLevel] = nextNodePosition;
    return currentLevel;
  }

  private RegState findStateInLayer(List<RegState> layer, int id) {
    for (RegState state : layer) {
      if (state.id == id) {
        return state;
      }
    }
    return null;
  }

  private RegState createAndAddStateToLayeredGraph(
      Mdd mdd, List<RegState>[] layeredGraph, int currentLevel, int nextNodePosition, int listLen) {
    int noNeighbours = countNeighbours(mdd, currentLevel, nextNodePosition, listLen);
    RegState s =
        new RegStateInt(
            currentLevel + 1, nextNodePosition, noNeighbours, activeLevelsTemp[currentLevel + 1]++);
    layeredGraph[currentLevel + 1].add(s);
    return s;
  }

  private int countNeighbours(Mdd mdd, int currentLevel, int nextNodePosition, int listLen) {
    int noNeighbours = 0;
    if (currentLevel + 1 < listLen) {
      for (int j = nextNodePosition; j < nextNodePosition + list[currentLevel + 1].getSize(); j++) {
        if (mdd.diagram[j] != Mdd.NOEDGE) {
          noNeighbours++;
        }
      }
    }
    return noNeighbours;
  }

  private void copyLayeredGraphToStateLevels(List<RegState>[] layeredGraph) {
    for (int i = 0; i < layeredGraph.length; i++) {
      stateLevels[i] = new RegState[layeredGraph[i].size()];
      int j = 0;
      for (RegState state : layeredGraph[i]) {
        stateLevels[i][j] = state;
        j++;
      }
    }
  }

  private int initializeArrayForwardReachable(
      Fsm dfa, int levels, IntDomain[][][] outarc, Set<FsmState> reachable, Set<FsmState> tmp) {
    reachable.add(dfa.initState);
    int level = 0;
    while (level < levels) {
      tmp.clear();
      for (FsmState s : reachable) {
        for (FsmTransition t : s.transitions) {
          IntDomain dom = t.domain.intersect(list[level].dom());
          if (outarc[level][s.id][t.successor.id] != null) {
            outarc[level][s.id][t.successor.id].addDom(dom);
          } else {
            outarc[level][s.id][t.successor.id] = dom;
          }
          if (dom.getSize() > 0) {
            if (level < levels - 1) {
              tmp.add(t.successor);
            } else if (dfa.finalStates.contains(t.successor)) {
              tmp.add(t.successor);
            }
          }
        }
      }
      reachable.clear();
      reachable.addAll(tmp);
      level++;
    }
    return level;
  }

  private int initializeArrayBackwardReachable(
      int level,
      int stateNum,
      IntDomain[][][] outarc,
      int[][] outdeg,
      Set<FsmState> reachable,
      Set<FsmState> tmp,
      FsmState[] array) {
    while (level > 0) {
      tmp.clear();
      stateLevels[level] = new RegState[reachable.size()];
      for (int i = 0; i < stateNum; i++) {
        for (int j = 0; j < stateNum; j++) {
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
    return level;
  }

  private void initializeArrayCopyToStateLevels(
      int levels, IntDomain[][][] outarc, int[][] outdeg) {
    int nextLevelIndex = 0;
    for (int level = 0; level < levels; level++) {
      int index = nextLevelIndex;
      nextLevelIndex = 0;
      for (int i = 0; i < stateNumber; i++) {
        if (outdeg[level][i] <= 0) {
          continue;
        }
        RegState s = getState(level, i);
        if (s == null) {
          s =
              listRepresentation
                  ? new RegStateInt(level, i, outdeg[level][i], index)
                  : new RegStateDom(level, i, outdeg[level][i], index);
          stateLevels[level][index++] = s;
          activeLevelsTemp[level] = index;
          if (DEBUG_ALL) {
            log.debug(
                "Create new state q_{}{} with in degree : {} and out degree : {}",
                level,
                i,
                s.inDegree,
                s.outDegree);
          }
        }
        for (int j = 0; j < stateNumber; j++) {
          if (outarc[level][i][j] == null || outarc[level][i][j].getSize() == 0) {
            continue;
          }
          RegState suc = getState(level + 1, j);
          if (suc == null) {
            suc =
                listRepresentation
                    ? new RegStateInt(level + 1, j, outdeg[level + 1][j], nextLevelIndex)
                    : new RegStateDom(level + 1, j, outdeg[level + 1][j], nextLevelIndex);
            stateLevels[level + 1][nextLevelIndex++] = suc;
            activeLevelsTemp[level + 1] = nextLevelIndex;
            if (DEBUG_ALL) {
              log.debug(
                  "Create new state q_{}{} with in degree : {} and out degree : {}",
                  level + 1,
                  j,
                  suc.inDegree,
                  suc.outDegree);
            }
          }
          s.addTransitions(suc, (IntervalDomain) outarc[level][i][j]);
          if (DEBUG_ALL) {
            log.debug(STATE_Q_DEGREES, level, i, s.inDegree, s.outDegree);
            log.debug(STATE_Q_DEGREES, level + 1, j, suc.inDegree, suc.outDegree);
          }
        }
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
   * Collects the damaged states, after pruning the domain of variable v, and put these states in
   * two separated sets.
   *
   * <p>One with the states with zero incoming degree - these are the candidates for the forward
   * part. The other set consists of states with zero out-coming degree - these are the candidates
   * for backward part.
   *
   * @param varIndex the index of the variable which have changed.
   */
  public void pruneArc(int varIndex) {

    int preThisLevelStateNb = this.activeLevels[varIndex].value();
    int nextVar = varIndex + 1;
    int preNextLevelStateNb = this.activeLevels[nextVar].value();

    levelHadChanged[varIndex] = true;

    IntDomain domVar = list[varIndex].domain;

    for (int state = preThisLevelStateNb - 1; state >= 0; state--) {
      RegState s = stateLevels[varIndex][state];
      if (DEBUG_ALL) {
        log.debug("{}: watch state q_{}{}", state, varIndex, s.id);
      }
      pruneArcForState(s, domVar, varIndex, nextVar);
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

  private void pruneArcForState(RegState s, IntDomain domVar, int varIndex, int nextVar) {
    boolean alreadyTouched = false;
    for (int i = s.outDegree - 1; i >= 0; i--) {
      if (!s.intersects(domVar, i)) {
        RegState suc = s.successors[i];
        removeTransitionWithLog(s, i, suc, varIndex);
        s.removeTransition(i);

        if (!alreadyTouched) {
          addTouchedState(s);
          alreadyTouched = true;
        }

        if (DEBUG_ALL) {
          log.debug(STATE_Q_DEGREES, s.level, s.id, s.inDegree, s.outDegree);
          log.debug(STATE_Q_DEGREES, suc.level, suc.id, suc.inDegree, suc.outDegree);
        }

        if (ASSERTS_ENABLED && s.outDegree < 0) {
          throw new IllegalStateException("Assertion failed");
        }
        if (s.outDegree == 0) {
          if (DEBUG_ALL) {
            log.debug("Move OUT state out of scope : q_{}{}", varIndex, s.id);
          }
          if (ASSERTS_ENABLED && s.level != varIndex) {
            throw new IllegalStateException("Assertion failed");
          }
          disableState(varIndex, s.pos);
        }

        if (ASSERTS_ENABLED && suc.inDegree < 0) {
          throw new IllegalStateException("Assertion failed");
        }
        if (suc.inDegree == 0) {
          if (DEBUG_ALL) {
            log.debug("Move IN state out of scope : q_{}{}", suc.level, suc.id);
          }
          if (ASSERTS_ENABLED && suc.level != varIndex + 1) {
            throw new IllegalStateException("Assertion failed");
          }
          disableState(nextVar, suc.pos);
          levelHadChanged[nextVar] = true;
        }
      }
    }
  }

  private void removeTransitionWithLog(RegState s, int i, RegState suc, int varIndex) {
    if (DEBUG_ALL) {
      log.debug(
          "must remove transition q_{}{} -{}-> q_{}{}",
          varIndex,
          s.id,
          s.sucDomToString(i),
          varIndex + 1,
          suc.id);
    }
  }

  /**
   * It does backward check to remove inactive edges and states.
   *
   * @param sucPrevLimit previous number of states at a given level.
   * @param level level for which the backward sweep is computed.
   * @return level at which the sweep has ended.
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

        if (ASSERTS_ENABLED && s.outDegree < 0) {
          throw new IllegalStateException(
              String.valueOf("Negative successor number of q_" + s.level + s.id));
        }

        if (s.outDegree == 0) {
          if (ASSERTS_ENABLED && s.level != level) {
            throw new IllegalStateException("Assertion failed");
          }
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

          if (DEBUG_ALL) {
            log.debug(
                "watch transition q_{}{} -{}-> q_{}{}",
                s.level,
                s.id,
                s.sucDomToString(i),
                suc.level,
                suc.id);
          }

          if (ASSERTS_ENABLED && suc.inDegree < 0) {
            throw new IllegalStateException(
                String.valueOf("Negative indegree of successor state" + suc.level + suc.id));
          }

          if (suc.inDegree == 0) {
            if (DEBUG_ALL) {
              log.debug("> Move IN state out of scope : q_{}{}", suc.level, suc.id);
            }
            // changed to directl disableState(int, int).
            if (ASSERTS_ENABLED && suc.level != level + 1) {
              throw new IllegalStateException("Assertion failed");
            }
            disableState(level + 1, suc.pos);
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

    if (ASSERTS_ENABLED && pos >= lim) {
      throw new IllegalStateException("Assertion failed");
    }

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

    if (ASSERTS_ENABLED && level <= firstConsistencyLevel) {
      throw new IllegalStateException(
          String.valueOf(
              "Constraint has the level at which it has computed its initial state being removed."));
    }

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

    int checkToIndex = touchedIndex.value();

    while (currentTouchedIndex > checkToIndex) {
      RegState curState = touchedStates[--currentTouchedIndex];
      recomputeOutDegree(curState, curState.level);
    }

    for (int l = leftPosition; l <= rightPosition; l++) {
      int stateNb = this.activeLevels[l].value();
      for (int s = lastNumberOfActiveStates[l]; s < stateNb; s++) {
        recomputeOutDegree(stateLevels[l][s], l);
      }
    }

    if (DEBUG_ALL) {
      log.debug("..next prunning");
    }

    leftPosition = list.length;
    rightPosition = 0;
  }

  private void recomputeOutDegree(RegState curState, int level) {
    RegState[] successors = curState.successors;
    int prevVal = curState.outDegree;
    curState.outDegree = successors.length;
    for (int i = prevVal; i < curState.outDegree; i++) {
      if (!successors[i].isActive(activeLevels) || !curState.intersects(list[level].domain, i)) {
        curState.outDegree = i;
      } else {
        successors[i].inDegree++;
      }
    }
  }

  @Override
  public void queueVariable(int level, Var v) {

    variableQueue.add((IntVar) v);
  }

  @Override
  public void consistency(Store store) {

    if (firstConsistencyCheck) {
      doFirstConsistency(store);
      firstConsistencyCheck = false;
      firstConsistencyLevel = store.level;
      if (variableQueue.isEmpty()) {
        return;
      }
    }

    Arrays.fill(levelHadChanged, false);

    for (Var v : variableQueue) {
      pruneArc(mapping.get(v));
    }

    updateLeftChangeFromLevelHadChanged(store);
    updateRightChangeFromLevelHadChanged(store);

    if (oneSupport) {
      consistencyOneSupportLevels(store);
    } else {
      consistencyVarDomLevels(store);
    }

    touchedIndex.update(this.currentTouchedIndex);
  }

  private void doFirstConsistency(Store store) {
    if (oneSupport) {
      for (int level = list.length - 1; level >= 0; level--) {
        firstConsistencyOneSupportLevel(store, level);
      }
    } else {
      for (int level = this.list.length - 1; level >= 0; level--) {
        firstConsistencyVarDomLevel(store, level);
      }
    }
  }

  private void firstConsistencyOneSupportLevel(Store store, int level) {
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

  private void firstConsistencyVarDomLevel(Store store, int level) {
    IntDomain varDom = new IntervalDomain();
    for (int s = activeLevels[level].value() - 1; s >= 0; s--) {
      RegState state = this.stateLevels[level][s];
      for (int i = state.outDegree - 1; i >= 0; i--) {
        state.add(varDom, i);
      }
    }
    if (DEBUG_ALL) {
      log.debug(
          ">>> Variable x_{} had domain {} and now its {}", level, this.list[level].domain, varDom);
    }
    this.list[level].domain.in(store.level, list[level], varDom);
  }

  private int findFirstLevelHadChanged(int start, int end) {
    for (int i = start; i < end; i++) {
      if (levelHadChanged[i]) {
        return i;
      }
    }
    return -1;
  }

  private void updateLeftChangeFromLevelHadChanged(Store store) {
    int start = leftChange.stamp() < store.level ? 0 : 0;
    int end = leftChange.stamp() < store.level ? levelHadChanged.length : leftChange.value();
    int found = findFirstLevelHadChanged(start, end);
    if (found >= 0) {
      leftChange.update(found);
    }
  }

  private int findLastLevelHadChanged(int start, int end) {
    for (int i = start; i > end; i--) {
      if (levelHadChanged[i]) {
        return i;
      }
    }
    return -1;
  }

  private void updateRightChangeFromLevelHadChanged(Store store) {
    int start = levelHadChanged.length - 1;
    int end = rightChange.stamp() < store.level ? -1 : rightChange.value();
    int found = findLastLevelHadChanged(start, end);
    if (found >= 0) {
      rightChange.update(found);
    }
  }

  private void consistencyOneSupportLevels(Store store) {
    for (int level = this.list.length - 1; level >= 0; level--) {
      if (!levelHadChanged[level]) {
        continue;
      }
      ValueEnumeration enumer = this.list[level].domain.valueEnumeration();
      for (int v; enumer.hasMoreElements(); ) {
        v = enumer.nextElement();
        RegEdge edge = supports[level].get(v);
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

  private void consistencyVarDomLevels(Store store) {
    for (int level = list.length - 1; level >= 0; level--) {
      if (!levelHadChanged[level]) {
        continue;
      }
      IntDomain varDom = new IntervalDomain();
      for (int s = activeLevels[level].value() - 1; s >= 0; s--) {
        RegState state = stateLevels[level][s];
        for (int i = state.outDegree - 1; i >= 0; i--) {
          state.add(varDom, i);
        }
      }
      if (DEBUG_ALL) {
        log.debug(
            ">>> Variable x_{} had domain {} and now its {}", level, list[level].domain, varDom);
      }
      list[level].domain.in(store.level, list[level], varDom);
    }
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

    if (DEBUG_ALL) {
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
