/*
 * BuildingBlocks.java
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

package org.jacop.examples.fd;

import java.util.ArrayList;
import java.util.Arrays;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.cumulative.Cumulative;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * It solves a simple logic puzzle about blocks.
 *
 * <p>Each of four alphabet blocks has a single letter of the alphabet on each of its six sides. In
 * all, the four blocks contain every letter but Q and Z. By arranging the blocks in various ways,
 * you can spell all of the words listed below. Can you figure out how the letters are arranged on
 * the four blocks?
 *
 * <p>BAKE ONYX ECHO OVAL
 *
 * <p>GIRD SMUG JUMP TORN
 *
 * <p>LUCK VINY LUSH WRAP
 *
 * @author Krzysztof "Vrbl" Wrobel and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class BuildingBlocks extends ExampleFd {

  /**
   * It executes the program to solve this logic puzzle.
   *
   * @param args args for the program (none)
   */
  static void main(String[] args) {
    if (args == null) {
      throw new IllegalArgumentException("args must not be null");
    }
    BuildingBlocks example = new BuildingBlocks();

    example.model();

    if (example.searchSmallestDomain(false)) {
      log.info("Solution(s) found");
    }
  }

  @Override
  public void model() {

    vars = new ArrayList<>();
    store = new Store();

    log.info("Building Blocks");

    IntVar a = new IntVar(store, "A", 1, 4);
    IntVar b = new IntVar(store, "B", 1, 4);
    IntVar c = new IntVar(store, "C", 1, 4);
    IntVar d = new IntVar(store, "D", 1, 4);
    IntVar e = new IntVar(store, "E", 1, 4);
    IntVar f = new IntVar(store, "F", 1, 4);
    IntVar g = new IntVar(store, "G", 1, 4);
    IntVar h = new IntVar(store, "H", 1, 4);
    IntVar iVar = new IntVar(store, "I", 1, 4);
    IntVar j = new IntVar(store, "J", 1, 4);
    IntVar k = new IntVar(store, "K", 1, 4);
    IntVar l = new IntVar(store, "L", 1, 4);
    IntVar m = new IntVar(store, "M", 1, 4);
    IntVar n = new IntVar(store, "N", 1, 4);
    IntVar o = new IntVar(store, "O", 1, 4);
    IntVar p = new IntVar(store, "P", 1, 4);
    IntVar r = new IntVar(store, "R", 1, 4);
    IntVar s = new IntVar(store, "S", 1, 4);
    IntVar t = new IntVar(store, "T", 1, 4);
    IntVar u = new IntVar(store, "U", 1, 4);
    IntVar w = new IntVar(store, "W", 1, 4);
    IntVar v = new IntVar(store, "V", 1, 4);
    IntVar x = new IntVar(store, "X", 1, 4);
    IntVar y = new IntVar(store, "Y", 1, 4);

    // array of letters.
    IntVar[] letters = {a, b, c, d, e, f, g, h, iVar, j, k, l, m, n, o, p, r, s, t, u, w, v, x, y};

    vars.addAll(Arrays.asList(letters));

    // First word, each letter on a different block.
    IntVar[] bake = {b, a, k, e};
    store.impose(new Alldifferent(bake));

    IntVar[] onyx = {o, n, y, x};
    store.impose(new Alldifferent(onyx));

    IntVar[] echo = {e, c, h, o};
    store.impose(new Alldifferent(echo));

    IntVar[] oval = {o, v, a, l};
    store.impose(new Alldifferent(oval));

    IntVar[] grid = {g, r, iVar, d};
    store.impose(new Alldifferent(grid));

    IntVar[] smug = {s, m, u, g};
    store.impose(new Alldifferent(smug));

    IntVar[] jump = {j, u, m, p};
    store.impose(new Alldifferent(jump));

    IntVar[] torn = {t, o, r, n};
    store.impose(new Alldifferent(torn));

    IntVar[] luck = {l, u, c, k};
    store.impose(new Alldifferent(luck));

    IntVar[] viny = {v, iVar, n, y};
    store.impose(new Alldifferent(viny));

    IntVar[] lush = {l, u, s, h};
    store.impose(new Alldifferent(lush));

    IntVar[] wrap = {w, r, a, p};
    store.impose(new Alldifferent(wrap));

    // auxilary variables
    IntVar one = new IntVar(store, "one", 1, 1);
    IntVar six = new IntVar(store, "six", 6, 6);

    IntVar[] ones = new IntVar[24];
    for (int i = 0; i < 24; i++) {
      ones[i] = one;
    }

    // Each block can not contain more than six letters.
    store.impose(new Cumulative(letters, ones, ones, six));

    // Letters decode the start time (block number).
    // Duration, each letter is only on one block (duration 1).
    // Resource, each letter takes only one space (usage 1).
    // Limit, all blocks can accommodate 6 letters.

  }
}
