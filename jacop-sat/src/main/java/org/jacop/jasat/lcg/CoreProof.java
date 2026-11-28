/*
 * CoreProof.java
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

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.Constraint;
import org.jacop.lcg.LinearForm;

/**
 * The VeriPB proof of the core-guided phase ({@link CoreSearch}), in the style of the certified OLL
 * of Berg, Bogaerts, Nordström, Oertel and Vandesande (CADE 2023). The proof keeps one derived
 * line, {@code obj - sum of w_s * s >= L}, where the s are the soft literals, each with its weight
 * left, and the literals that are not soft yet with their full weight, and L is the lower bound up
 * to the root's fixed literals, which unit propagation counts:
 *
 * <ul>
 *   <li>at the start it is the sum of the model's lines of the objective's definitions, each scaled
 *       as the search substituted it;
 *   <li>a soft literal that stands for the levels of a hole of a term's domain takes their weights
 *       by the order lines between them;
 *   <li>each totalizer output {@code o_k} over n leaves is defined by two {@code red} steps, {@code
 *       o_k -> sum >= k} and {@code sum >= k -> o_k}, and each totalizer clause is the sum of the
 *       definitions it links;
 *   <li>a core of n literals with smallest weight m adds m times {@code sum - (o_2 + ... + o_n) >=
 *       1}, which the outputs' definitions give, divided step by step.
 * </ul>
 *
 * <p>The clause that the objective is at least the lower bound is then a {@code rup} step, and so
 * is each hardened literal once the line is added to the constraint that the objective improves on
 * the best solution.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class CoreProof {

  /** A definition the search substituted: the constraint, its form, and the scale it took. */
  record Definition(Constraint constraint, LinearForm form, long scale) {}

  private final LcgSolver lcg;
  private final VeriPbProof proof;
  // the lower-bound line, and whether this proof derived it (otherwise it is a model line)
  private long line;
  private boolean derived;
  // the definitions of each totalizer output: o -> sum >= k, and sum >= k -> o
  private final Map<Integer, long[]> definitions = new HashMap<>();

  private CoreProof(LcgSolver lcg) {
    this.lcg = lcg;
    this.proof = lcg.proof();
  }

  /**
   * Derives the lower-bound line from the definitions.
   *
   * @return the proof, or null when the model does not have a definition's lines
   */
  static CoreProof of(LcgSolver lcg, List<Definition> definitions) {
    if (definitions.isEmpty()) {
      return null;
    }
    StringBuilder s = new StringBuilder();
    long only = 0;
    for (Definition d : definitions) {
      long[] lines = lcg.proofEquality(d.constraint(), d.form());
      if (lines == null) {
        return null;
      }
      long id = d.scale() > 0 ? lines[0] : lines[1];
      long k = Math.abs(d.scale());
      only = k == 1 ? id : 0;
      s.append(s.isEmpty() ? "" : " ").append(id);
      if (k != 1) {
        s.append(' ').append(k).append(" *");
      }
      if (d != definitions.get(0)) {
        s.append(" +");
      }
    }
    CoreProof p = new CoreProof(lcg);
    p.proof.comment("core-guided phase: the objective's lower-bound line");
    if (definitions.size() == 1 && only != 0) {
      p.line = only; // the model's line itself
    } else {
      p.update(s);
    }
    return p;
  }

  // replaces the line by a new one, deleting the old one when the proof derived it
  private void update(CharSequence operands) {
    long old = derived ? line : 0;
    line = proof.pol(operands);
    derived = true;
    if (old != 0) {
      proof.deleteSteps(old);
    }
  }

  /**
   * Moves the weight of the levels {@code level..to - 1} of a term onto the literal of level to,
   * which they equal in a hole of the domain: w times the order line between each level and the
   * next, as many times as levels below it are moved.
   *
   * @param i the term's variable
   * @param up whether the levels are {@code [x >= base + l]}, otherwise {@code [x <= base - l]}
   * @param base the bound the levels are counted from
   * @param level the first level
   * @param to the level of the literal
   * @param weight the weight of each level
   */
  void fold(int i, boolean up, int base, int level, int to, long weight) {
    if (to <= level) {
      return;
    }
    StringBuilder s = new StringBuilder().append(line);
    for (int l = level; l < to; l++) {
      long id = lcg.proofChainLine(i, up ? base + l : base - l);
      if (id != 0) {
        s.append(' ').append(id).append(' ').append(weight * (l - level + 1)).append(" * +");
      }
    }
    update(s);
  }

  /**
   * Defines the outputs of a totalizer node over the leaves {@code inputs[from..to)}: output k
   * (from 0) is true exactly when at least k + 1 leaves are.
   */
  void define(int[] outputs, int[] inputs, int from, int to) {
    int n = to - from;
    for (int k = 0; k < outputs.length; k++) {
      int o = outputs[k];
      lcg.nameAuxiliary(o);
      String name = lcg.proofLiteral(o);
      int count = k + 1;
      StringBuilder forward = new StringBuilder().append(count).append(" ~").append(name);
      StringBuilder backward = new StringBuilder().append(n - count + 1).append(' ').append(name);
      for (int j = from; j < to; j++) {
        forward.append(" 1 ").append(lcg.proofLiteral(inputs[j]));
        backward.append(" 1 ").append(lcg.proofLiteral(-inputs[j]));
      }
      forward.append(" >= ").append(count).append(" : ").append(name).append(" -> 0");
      backward.append(" >= ").append(n - count + 1).append(" : ").append(name).append(" -> 1");
      long f = proof.red(forward);
      long b = proof.red(backward);
      definitions.put(o, new long[] {f, b});
    }
  }

  /**
   * Derives the totalizer clause {@code not a or not b or o}, the sum of the definitions of a and b
   * (when they are outputs, not leaves) and the definition {@code sum >= k -> o}; that sum
   * propagates as the clause does.
   *
   * @param a the output of the first child, or 0 for none or a leaf
   * @param b the output of the second child, or 0 for none or a leaf
   * @param o the output
   */
  void totalizerClause(int a, int b, int o) {
    StringBuilder s = new StringBuilder();
    for (int x : new int[] {a, b}) {
      if (x != 0) {
        s.append(definitions.get(x)[0]).append(' ');
      }
    }
    if (s.isEmpty()) {
      return; // the definition of o is the clause
    }
    s.append(definitions.get(o)[1]).append(" +");
    if (a != 0 && b != 0) {
      s.append(" +");
    }
    proof.pol(s);
  }

  /**
   * Adds a core to the lower-bound line: its weight times {@code sum - (o_2 + ... + o_n) >= 1},
   * from the definitions {@code o_k -> sum >= k} combined and divided step by step into {@code sum
   * - (o_1 + ... + o_n) >= 0}, and the unit {@code o_1}, which the core's clause gives.
   *
   * @param outputs the totalizer's outputs over the core's literals, all of them
   * @param weight the core's smallest weight
   */
  void core(int[] outputs, long weight) {
    long unit = proof.lemma("rup 1 " + lcg.proofLiteral(outputs[0]) + " >= 1 ;\n");
    StringBuilder s = new StringBuilder().append(definitions.get(outputs[0])[0]);
    for (int k = 2; k <= outputs.length; k++) {
      if (k > 2) {
        s.append(' ').append(k - 1).append(" *");
      }
      s.append(' ').append(definitions.get(outputs[k - 1])[0]).append(" + ").append(k).append(" d");
    }
    s.append(' ').append(unit).append(" +");
    if (weight != 1) {
      s.append(' ').append(weight).append(" *");
    }
    s.append(' ').append(line).append(" +");
    update(s);
  }

  /**
   * Writes the line that the soft literals' weights sum to less than the gap between the best
   * solution and the lower bound: the lower-bound line plus the constraint that the objective
   * improves on the best solution. Unit propagation on it makes false each literal that weighs more
   * than the gap.
   *
   * @return its id, or 0 when no solution is logged
   */
  long gap() {
    long improvement = proof.improvement();
    if (improvement == 0) {
      return 0;
    }
    return proof.pol(line + " " + improvement + " +");
  }

  /** Deletes a line {@link #gap} wrote. */
  void delete(long id) {
    if (id != 0) {
      proof.deleteSteps(id);
    }
  }
}
