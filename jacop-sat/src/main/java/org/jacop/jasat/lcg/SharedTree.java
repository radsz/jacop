/*
 * SharedTree.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.lcg;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Deque;
import java.util.function.BooleanSupplier;

/**
 * One search tree that LCG solvers of the same model, each in its own thread, divide among
 * themselves (search splitting, as opposed to a portfolio where each thread searches the whole tree
 * its own way). A part of the tree is a cube: a conjunction of atoms {@code [x >= v]} and {@code [x
 * = v]}, possibly negated, over variables known by name. A solver takes a cube, solves under it as
 * assumptions, and reports it closed when no solution better than the shared bound is left in it. A
 * solver that is busy while another waits splits its cube on its first decision below the
 * assumptions, at a restart or a new cube: it keeps the cube with the decision and gives away the
 * cube with its negation, as the shared tree workers of CP-SAT (Perron and Didier) and the dynamic
 * work sharing of Chu, Schulte and Stuckey (Confidence-based work stealing in parallel constraint
 * programming, CP 2009) do. Solving each cube under assumptions with one incremental CDCL solver
 * that keeps its learnt clauses is the conquer phase of Cube and Conquer (M. Heule, O. Kullmann, S.
 * Wieringa and A. Biere, Cube and conquer: guiding CDCL SAT solvers by lookaheads, HVC 2011);
 * dividing the search of a solver with learning among threads that share nogoods follows E. Ehlers
 * and P. J. Stuckey (Parallelizing constraint programming with learning, CPAIOR 2016), who also
 * point out that disjoint parts cost optimisation its best solutions, which is why the portfolio
 * mixes split threads with whole-tree ones. The tree starts as the empty cube, so the union of the
 * open and taken cubes always covers what is not closed; when no cube is open or taken, the whole
 * search is complete.
 *
 * <p>Since the assumptions are decisions, every clause a solver learns holds without them, so
 * clause sharing goes on as in a portfolio. The solvers must solve the same model: the same
 * symmetry breaking, no presolve that runs differently, no relax and reconstruct.
 *
 * <p>A cube is stored as {@code [id1, kind1, value1, id2, ...]} with the atoms of {@link
 * SharedClauses}.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class SharedTree {

  private static final int[] ROOT = new int[0];

  // how long a waiting solver sleeps before it looks at its stop condition again
  private static final long WAIT_MILLIS = 20;

  private final Deque<int[]> open = new ArrayDeque<>();
  private final Object lock = new Object();
  // the constraints the solvers add to the model; null until the first solver joins
  private String added;
  private boolean started;
  private int joined;
  private boolean done;
  // cubes being solved
  private int busy;
  // solvers waiting for a cube; read without the lock by busy solvers
  private volatile int idle;
  private volatile int openSize;

  /** Statistics: cubes given away by splits. */
  private long splits;

  /** Statistics: cubes closed. */
  private long closed;

  /** Statistics: the time solvers waited for a cube, in nanoseconds. */
  private long waited;

  /**
   * Registers a solver of the model plus the constraints named by {@code added}; all solvers of the
   * tree must add the same ones.
   *
   * @param addedConstraints the constraints the solver adds to the shared model, the same text for
   *     the same constraints; empty when it adds none
   * @return whether the solver may take part
   */
  public boolean join(String addedConstraints) {
    synchronized (lock) {
      if (added == null) {
        added = addedConstraints;
      }
      if (added.equals(addedConstraints)) {
        joined++;
        return true;
      }
      return false;
    }
  }

  /**
   * Statistics: the solvers that joined the tree.
   *
   * @return the number of solvers
   */
  public int joined() {
    synchronized (lock) {
      return joined;
    }
  }

  /**
   * Takes an open cube, waiting while there is none and other solvers are busy.
   *
   * @param stop true when the solver must stop waiting (a stop or a time-out)
   * @return the cube, or null when the search is complete or the solver stopped
   */
  public int[] take(BooleanSupplier stop) {
    long start = System.nanoTime();
    synchronized (lock) {
      idle++;
      try {
        while (!done) {
          if (!open.isEmpty()) {
            busy++;
            openSize = open.size() - 1;
            return open.poll();
          }
          if (!started) {
            started = true;
            busy++;
            return ROOT;
          }
          if (busy == 0) {
            done = true;
            lock.notifyAll();
            return null;
          }
          if (stop.getAsBoolean()) {
            return null;
          }
          try {
            lock.wait(WAIT_MILLIS);
          } catch (InterruptedException _) {
            Thread.currentThread().interrupt();
            return null;
          }
        }
        return null;
      } finally {
        idle--;
        waited += System.nanoTime() - start;
      }
    }
  }

  /**
   * Whether a solver waits for a cube that no open cube serves: a busy solver should split.
   *
   * @return true when a split would give a waiting solver work
   */
  public boolean wantsSplit() {
    return idle > openSize;
  }

  /**
   * Gives away the part of a taken cube that its solver no longer searches.
   *
   * @param cube the cube given away
   */
  public void split(int[] cube) {
    synchronized (lock) {
      if (done) {
        return;
      }
      open.add(cube);
      openSize = open.size();
      splits++;
      lock.notifyAll();
    }
  }

  /**
   * Reports that a taken cube has no solution better than the shared bound.
   *
   * @param cube the cube
   */
  public void closed(int[] cube) {
    synchronized (lock) {
      busy--;
      closed++;
      if (busy == 0 && open.isEmpty()) {
        done = true;
      }
      lock.notifyAll();
    }
  }

  /**
   * Gives back a taken cube that its solver did not finish, as when it stopped.
   *
   * @param cube the cube
   */
  public void release(int[] cube) {
    synchronized (lock) {
      busy--;
      if (!done) {
        open.addFirst(cube);
        openSize = open.size();
      }
      lock.notifyAll();
    }
  }

  /** Reports that the whole search is complete, as when a solver found no solution at the root. */
  public void complete() {
    synchronized (lock) {
      done = true;
      lock.notifyAll();
    }
  }

  /**
   * Whether the whole search is complete.
   *
   * @return true when every cube is closed
   */
  public boolean isComplete() {
    synchronized (lock) {
      return done;
    }
  }

  /**
   * Statistics: the cubes given away by splits.
   *
   * @return the number of splits
   */
  public long splits() {
    synchronized (lock) {
      return splits;
    }
  }

  /**
   * Statistics: the cubes closed.
   *
   * @return the number of closed cubes
   */
  public long closedCubes() {
    synchronized (lock) {
      return closed;
    }
  }

  /**
   * Statistics: the time solvers waited for a cube.
   *
   * @return the time in milliseconds, summed over the solvers
   */
  public long waitedMillis() {
    synchronized (lock) {
      return waited / 1_000_000L;
    }
  }

  /**
   * A cube with one more atom.
   *
   * @param cube the cube
   * @param id the variable's id
   * @param kind the atom's kind, plus {@link SharedClauses#NEGATED} when negated
   * @param value the atom's value
   * @return the longer cube
   */
  static int[] extend(int[] cube, int id, int kind, int value) {
    int[] c = Arrays.copyOf(cube, cube.length + 3);
    c[cube.length] = id;
    c[cube.length + 1] = kind;
    c[cube.length + 2] = value;
    return c;
  }
}
