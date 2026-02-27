/*
 * DomainStructure.java
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

package org.jacop.constraints.netflow;

import static org.jacop.constraints.netflow.simplex.NetworkSimplex.DELETED_ARC;
import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.Collections;
import java.util.List;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.netflow.simplex.Arc;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Var;

/**
 * A domain based structure variable.
 *
 * <p>Arcs can be associated to sub-domains of the structure variable. The state of the arc is said
 * to be active if the variable takes a value from its sub-domain and it is inactive otherwise.
 *
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class DomainStructure implements VarHandler {

  final IntVar variable;
  final Arc[] arcs;
  final IntDomain[] domains;
  final Behavior behavior;
  int notGrounded;

  /**
   * Creates an S-variable.
   *
   * @param variable variable to create for
   * @param domList list of domains
   * @param arcList list of arcs
   */
  public DomainStructure(IntVar variable, List<Domain> domList, List<Arc> arcList) {

    this(variable, domList.toArray(new IntDomain[0]), arcList.toArray(new Arc[0]));
  }

  /**
   * Creates a domain structure with default pruning behavior of {@link Behavior#PRUNE_BOTH}.
   *
   * @param variable the structure variable.
   * @param domains the sub-domains associated with each arc.
   * @param arcs the arcs associated with each sub-domain.
   */
  public DomainStructure(IntVar variable, IntDomain[] domains, Arc[] arcs) {

    this(variable, domains, arcs, Behavior.PRUNE_BOTH);
  }

  /**
   * Creates a domain structure with the specified pruning behavior.
   *
   * @param variable the structure variable.
   * @param domains the sub-domains associated with each arc.
   * @param arcs the arcs associated with each sub-domain.
   * @param behavior the pruning behavior for this structure.
   */
  public DomainStructure(IntVar variable, IntDomain[] domains, Arc[] arcs, Behavior behavior) {

    if (domains.length != arcs.length) {
      throw new IllegalArgumentException("#domains != #arcs");
    }

    this.variable = variable;
    this.arcs = arcs;
    this.domains = domains;
    this.notGrounded = arcs.length;
    this.behavior = behavior;

    for (int id = 0; id < arcs.length; id++) {
      if (!arcs[id].forward) {
        throw new IllegalArgumentException("Not a forward arc");
      }

      ArcCompanion companion = arcs[id].companion;
      if (companion == null) {
        arcs[id].companion = new ArcCompanion(arcs[id], 0);
      }
      arcs[id].companion.structure = this;
      arcs[id].companion.arcId = id;
    }
  }

  /**
   * Updates the network after the structure variable has changed, grounding arcs as needed.
   *
   * @param variable the variable whose domain has changed.
   * @param network the mutable network to update.
   */
  public void processEvent(IntVar variable, MutableNetwork network) {

    IntDomain vardom = variable.domain;
    int size = vardom.getSize();

    for (int id = notGrounded - 1; id >= 0; id--) {

      // arc already deleted ?
      if (arcs[id].index == DELETED_ARC) {
        if (ASSERTS_ENABLED) {
          throw new IllegalStateException("Assertion failed");
        }
        continue;
      }

      int inter = domains[id].intersect(vardom).getSize();
      if (inter < 0) {
        inter = 0;
      }

      // make arc inactive ?
      if (inter == 0 && behavior != Behavior.PRUNE_ACTIVE) {
        groundArc(id, false, network);
      } else if (inter == size && behavior != Behavior.PRUNE_INACTIVE) {
        groundArc(id, true, network);
      }
    }
  }

  private void groundArc(int arcId, boolean active, MutableNetwork network) {

    if (ASSERTS_ENABLED && arcId >= notGrounded) {
      throw new IllegalStateException("Assertion failed");
    }

    // prune domain of x variable

    Arc arc = arcs[arcId];
    ArcCompanion companion = arc.companion;
    IntVar xVar = companion.xVar;

    // active arc - ground flow at upper bound
    if (active) {

      int maxFlow = companion.flowOffset + arc.capacity + arc.sister.capacity;

      if (xVar != null) {
        int level = network.getStoreLevel();
        xVar.domain.in(level, xVar, maxFlow, maxFlow);
      }

      companion.setFlow(maxFlow);

      if (arc.index >= 0) {
        ((Network) network).lower[arc.index] = arc.sister;
      }
    } else { // inactive arc - ground flow at lower bound
      int minFlow = companion.flowOffset;

      if (xVar != null) {
        int level = network.getStoreLevel();
        xVar.domain.in(level, xVar, minFlow, minFlow);
      }

      companion.setFlow(minFlow);
      if (arc.index >= 0) {
        ((Network) network).lower[arc.index] = arc;
      }
    }

    // remove arc from graph
    network.remove(arcs[arcId]);

    // remove domain/arc pair
    swap(arcId, --notGrounded);
  }

  private void swap(int i, int j) {
    if (i == j) {
      return;
    }

    IntDomain temp1 = domains[i];
    domains[i] = domains[j];
    domains[j] = temp1;

    Arc temp2 = arcs[i];
    arcs[i] = arcs[j];
    arcs[j] = temp2;

    arcs[j].companion.arcId = j;
    arcs[i].companion.arcId = i;
  }

  /**
   * Marks a previously grounded arc as not grounded, restoring it to active status.
   *
   * @param arcId the index of the arc to unground.
   */
  public void ungroundArc(int arcId) {
    if (ASSERTS_ENABLED && arcId < notGrounded) {
      throw new IllegalStateException("Assertion failed");
    }

    // add domain/arc pair
    if (ASSERTS_ENABLED && arcId != notGrounded) {
      throw new IllegalStateException("Assertion failed");
    }
    notGrounded++;
  }

  /**
   * Returns a singleton list containing the structure variable.
   *
   * @return a list with the single structure variable.
   */
  public List<IntVar> listVariables() {
    return Collections.singletonList(variable);
  }

  /**
   * Checks whether the arc with the given ID is grounded (fixed at a bound).
   *
   * @param arcId the index of the arc to check.
   * @return true if the arc is grounded, false otherwise.
   */
  public boolean isGrounded(int arcId) {
    return arcId >= notGrounded;
  }

  /**
   * Returns the pruning event type for the given variable.
   *
   * @param v the variable for which to determine the pruning event.
   * @return the pruning event constant for structure variables.
   */
  public int getPruningEvent(Var v) {
    return IntDomain.ANY; // for S-variables
  }

  /** Pruning behavior for arc variables. */
  public enum Behavior {
    PRUNE_ACTIVE,
    PRUNE_INACTIVE,
    PRUNE_BOTH
  }
}
