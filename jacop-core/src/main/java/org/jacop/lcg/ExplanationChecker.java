/*
 * ExplanationChecker.java
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

package org.jacop.lcg;

import java.util.Map;
import org.jacop.constraints.Constraint;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;

/**
 * Checks explanations in a scratch store: the constraint is copied over fresh variables with the
 * trail's initial domains, the reason's atoms are imposed, and the explained atom is negated (for a
 * failure, nothing more). Propagation that fails proves the explanation; otherwise a search for a
 * solution decides, since an explanation may be stronger than the propagator (energy reasoning for
 * a time-table propagator, for example). A solution is a counterexample: the explanation is wrong.
 * A search that reaches its node limit leaves the explanation undecided. It is a debugging aid: it
 * costs a store and a search per explanation.
 *
 * <p>Constraints that cannot be copied, or that have variables other than {@link IntVar}, {@link
 * BooleanVar} and {@link Mirrored} ones, are skipped.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public final class ExplanationChecker {

  private final AtomicTrail trail;

  /** Statistics: explanations derived again. */
  public long checked;

  /** Statistics: explanations skipped because their constraint cannot be copied. */
  public long skipped;

  /** Statistics: explanations whose search for a counterexample reached its node limit. */
  public long undecided;

  private static final long NODE_LIMIT = 100_000;

  /**
   * Creates a checker for the explanations of a trail.
   *
   * @param trail the trail
   */
  public ExplanationChecker(AtomicTrail trail) {
    this.trail = trail;
  }

  /**
   * Checks the reason of an entry propagated by a constraint.
   *
   * @param entry the entry
   * @param reason the entries of its reason
   * @return null when the reason implies the entry or cannot be checked, otherwise a description
   */
  public String checkReason(int entry, EntryList reason) {
    return check(trail.reason(entry), entry, reason);
  }

  /**
   * Checks the reason of a constraint's failure.
   *
   * @param failed the constraint that failed
   * @param reason the entries of its reason
   * @return null when the reason implies the failure or cannot be checked, otherwise a description
   */
  public String checkFailure(Constraint failed, EntryList reason) {
    return check(failed, -1, reason);
  }

  private String check(Constraint c, int entry, EntryList reason) {
    ScratchCopy copy = ScratchCopy.of(trail, c);
    if (copy == null) {
      skipped++;
      return null;
    }
    Store scratch = copy.store;
    checked++;
    try {
      for (int k = 0; k < reason.size(); k++) {
        if (!impose(copy, reason.get(k), reason.slack(k))) {
          return describe(c, entry, reason, "has an atom on a variable outside the constraint");
        }
      }
      copy.imposeCopy(c);
      if (!scratch.consistency()) {
        return null;
      }
    } catch (FailException _) {
      return null;
    }
    if (entry < 0) {
      return counterexample(scratch, copy.copies, c, entry, reason);
    }
    try {
      // the propagator may be weaker than the explanation: look for a solution with the atom false
      if (!copy.imposeNegation(entry)) {
        return describe(c, entry, reason, "explains an atom on a variable outside the constraint");
      }
      if (!scratch.consistency()) {
        return null;
      }
    } catch (FailException _) {
      return null;
    }
    return counterexample(scratch, copy.copies, c, entry, reason);
  }

  /**
   * Searches the scratch store for a solution, which shows the reason wrong. A search that reaches
   * its node limit counts as undecided.
   */
  private String counterexample(
      Store scratch, Map<Var, Var> copies, Constraint c, int entry, EntryList reason) {
    IntVar[] scope =
        copies.values().stream()
            .filter(IntVar.class::isInstance)
            .map(IntVar.class::cast)
            .toArray(IntVar[]::new);
    DepthFirstSearch<IntVar> search = new DepthFirstSearch<>();
    search.setPrintInfo(false);
    search.setAssignSolution(false);
    search.setNodesOut(NODE_LIMIT);
    StringBuilder solution = new StringBuilder();
    search.setSolutionListener(
        new SimpleSolutionListener<>() {
          @Override
          public boolean executeAfterSolution(Search<IntVar> s, SelectChoicePoint<IntVar> select) {
            for (IntVar x : scope) {
              solution.append(' ').append(x.id()).append('=').append(x.value());
            }
            return super.executeAfterSolution(s, select);
          }
        });
    if (search.labeling(scratch, new SimpleSelect<>(scope, null, new IndomainMin<>()))) {
      String problem = entry < 0 ? "does not imply the failure" : "does not imply it";
      return describe(c, entry, reason, problem + "; solution" + solution);
    }
    if (search.getNodes() > NODE_LIMIT) {
      undecided++;
    }
    return null;
  }

  // imposes an atom weakened by its slack, as the solver may cite it
  private boolean impose(ScratchCopy copy, int entry, int slack) {
    if (slack == 0) {
      return copy.impose(entry);
    }
    IntVar y = copy.get(trail.variable(entry));
    if (y == null) {
      return false;
    }
    int v = trail.value(entry);
    if (trail.kind(entry) == AtomicTrail.GE) {
      y.domain.inMin(copy.store.level, y, v - slack);
    } else {
      y.domain.inMax(copy.store.level, y, v + slack);
    }
    return true;
  }

  private String describe(Constraint c, int entry, EntryList reason, String problem) {
    StringBuilder result = new StringBuilder("the reason ");
    for (int k = 0; k < reason.size(); k++) {
      result.append(k == 0 ? "" : " ").append(trail.atomString(reason.get(k)));
      if (reason.slack(k) != 0) {
        result.append(" (slack ").append(reason.slack(k)).append(')');
      }
    }
    result.append(entry < 0 ? " of the failure" : " of " + trail.atomString(entry));
    return result.append(' ').append(problem).append(", by ").append(c).toString();
  }
}
