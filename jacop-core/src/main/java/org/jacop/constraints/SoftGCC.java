/*
 * SoftGCC.java
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

package org.jacop.constraints;

import static org.jacop.core.Store.ASSERTS_ENABLED;

import java.util.ArrayList;
import java.util.List;
import org.jacop.constraints.netflow.DomainStructure;
import org.jacop.constraints.netflow.NetworkBuilder;
import org.jacop.constraints.netflow.simplex.Arc;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;

/**
 * This class provides soft-gcc constraint by decomposing it either into a network flow constraint
 * or a set of primitive constraints.
 *
 * <p>It is soft in a sense that every violation of softLower, softUpper bound or softCounter
 * contributes to the violation cost. It is hard in a sense that it does enforce hardLower,
 * hardUpper bound or hardCounter. It uses value based violation metric.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
@SuppressWarnings(
    "checkstyle:AbbreviationAsWordInName") // GCC is standard constraint programming terminology
public class SoftGCC extends DecomposedConstraint<Constraint> {

  private final IntVar[] xvars;
  private final int[] countedValue;
  private final IntVar costVar;
  private final ViolationMeasure violationMeasure;
  private List<Constraint> decomposition;
  private IntVar[] hardCounters;
  private IntVar[] softCounters;
  private int[] softLowerBound;
  private int[] softUpperBound;
  private int[] hardLowerBound;
  private int[] hardUpperBound;

  /**
   * Helper method to compute countedValue from xvars domains.
   *
   * @param xvars the variables
   * @return array of counted values
   */
  private static int[] computeCountedValue(IntVar[] xvars) {
    IntDomain sum = new IntervalDomain();
    for (IntVar xVar : xvars) {
      sum.unionAdapt(xVar.domain);
    }

    int[] result = new int[sum.getSize()];
    int i = 0;
    for (ValueEnumeration enumer = sum.valueEnumeration(); enumer.hasMoreElements(); ) {
      result[i++] = enumer.nextElement();
    }
    return result;
  }

  /**
   * Helper method to copy an IntVar array.
   *
   * @param source the source array
   * @return a copy of the array
   */
  private static IntVar[] copyIntVarArray(IntVar[] source) {
    IntVar[] result = new IntVar[source.length];
    System.arraycopy(source, 0, result, 0, source.length);
    return result;
  }

  /**
   * Helper method to copy an int array.
   *
   * @param source the source array
   * @return a copy of the array
   */
  private static int[] copyIntArray(int[] source) {
    int[] result = new int[source.length];
    System.arraycopy(source, 0, result, 0, source.length);
    return result;
  }

  /**
   * It specifies soft-GCC constraint.
   *
   * @param xvars variables over which counting takes place.
   * @param hardCounters idNumber variables for different values being counted. Their domain specify
   *     hard constraints on the occurrences.
   * @param countedValue it specifies values which occurrence is being counted.
   * @param softLowerBound it specifies constraint what is the minimal number of occurrences.
   * @param softUpperBound it specifies constraint what is the maximal number of occurrences.
   * @param costVar a cost variable specifying the cost of violations.
   * @param violationMeasure it is only accepted to use Value_Based violation measure.
   */
  public SoftGCC(
      IntVar[] xvars,
      IntVar[] hardCounters,
      int[] countedValue,
      int[] softLowerBound,
      int[] softUpperBound,
      IntVar costVar,
      ViolationMeasure violationMeasure) {

    checkInputForNullness(
        new String[] {
          "xvars",
          "hardCounters",
          "countedValue",
          "softLowerBound",
          "softUpperBound",
          "costVar",
          "violationMeasure"
        },
        new Object[][] {
          xvars,
          hardCounters,
          {countedValue},
          {softLowerBound},
          {softUpperBound},
          {costVar},
          {violationMeasure}
        });

    this.xvars = copyIntVarArray(xvars);
    this.hardCounters = copyIntVarArray(hardCounters);
    this.softLowerBound = copyIntArray(softLowerBound);
    this.softUpperBound = copyIntArray(softUpperBound);
    this.countedValue = copyIntArray(countedValue);
    this.costVar = costVar;
    this.violationMeasure = violationMeasure;
  }

  /**
   * It specifies soft-GCC constraint.
   *
   * @param xvars variables over which counting takes place.
   * @param hardLowerBound it specifies constraint what is the minimal number of occurrences. (hard)
   * @param hardUpperBound it specifies constraint what is the maximal number of occurrences. (hard)
   * @param countedValue it specifies values which occurrence is being counted.
   * @param softCounters it specifies the number of occurrences (soft).
   * @param costVar a cost variable specifying the cost of violations.
   * @param violationMeasure it is only accepted to use Value_Based violation measure.
   */
  public SoftGCC(
      IntVar[] xvars,
      int[] hardLowerBound,
      int[] hardUpperBound,
      int[] countedValue,
      IntVar[] softCounters,
      IntVar costVar,
      ViolationMeasure violationMeasure) {

    this.xvars = copyIntVarArray(xvars);
    this.softCounters = copyIntVarArray(softCounters);
    this.hardLowerBound = copyIntArray(hardLowerBound);
    this.hardUpperBound = copyIntArray(hardUpperBound);
    this.countedValue = copyIntArray(countedValue);
    this.costVar = costVar;
    this.violationMeasure = violationMeasure;
  }

  /**
   * It specifies soft-GCC constraint.
   *
   * @param xvars variables over which counting takes place.
   * @param hardCounters idNumber variables for different values being counted. (hard)
   * @param countedValue it specifies values which occurrence is being counted.
   * @param softCounters idNumber variables for different values being counted. (soft)
   * @param costVar a cost variable specifying the cost of violations.
   * @param violationMeasure it is only accepted to use Value_Based violation measure.
   */
  public SoftGCC(
      IntVar[] xvars,
      IntVar[] hardCounters,
      int[] countedValue,
      IntVar[] softCounters,
      IntVar costVar,
      ViolationMeasure violationMeasure) {

    this.xvars = copyIntVarArray(xvars);
    this.softCounters = copyIntVarArray(softCounters);
    this.hardCounters = copyIntVarArray(hardCounters);
    this.countedValue = copyIntArray(countedValue);
    this.costVar = costVar;
    this.violationMeasure = violationMeasure;
  }

  /**
   * It specifies soft-GCC constraint.
   *
   * @param xvars variables over which counting takes place.
   * @param hardCounters idNumber variables for different values being counted. (hard)
   * @param softLowerBound it specifies constraint what is the minimal number of occurrences. (soft)
   * @param softUpperBound it specifies constraint what is the maximal number of occurrences. (soft)
   * @param costVar a cost variable specifying the cost of violations.
   * @param violationMeasure it is only accepted to use Value_Based violation measure.
   */
  public SoftGCC(
      IntVar[] xvars,
      IntVar[] hardCounters,
      int[] softLowerBound,
      int[] softUpperBound,
      IntVar costVar,
      ViolationMeasure violationMeasure) {

    this.countedValue = computeCountedValue(xvars);
    this.xvars = copyIntVarArray(xvars);
    this.hardCounters = copyIntVarArray(hardCounters);
    this.softLowerBound = copyIntArray(softLowerBound);
    this.softUpperBound = copyIntArray(softUpperBound);
    this.costVar = costVar;
    this.violationMeasure = violationMeasure;
  }

  /**
   * It specifies soft-GCC constraint.
   *
   * @param xvars variables over which counting takes place.
   * @param hardLowerBound it specifies constraint what is the minimal number of occurrences. (hard)
   * @param hardUpperBound it specifies constraint what is the maximal number of occurrences. (hard)
   * @param softCounters idNumber variables for different values being counted. (soft)
   * @param costVar a cost variable specifying the cost of violations.
   * @param violationMeasure it is only accepted to use Value_Based violation measure.
   */
  public SoftGCC(
      IntVar[] xvars,
      int[] hardLowerBound,
      int[] hardUpperBound,
      IntVar[] softCounters,
      IntVar costVar,
      ViolationMeasure violationMeasure) {

    this.countedValue = computeCountedValue(xvars);
    this.xvars = copyIntVarArray(xvars);
    this.softCounters = copyIntVarArray(softCounters);
    this.hardLowerBound = copyIntArray(hardLowerBound);
    this.hardUpperBound = copyIntArray(hardUpperBound);

    this.costVar = costVar;
    this.violationMeasure = violationMeasure;
  }

  /**
   * It specifies soft-GCC constraint.
   *
   * @param xvars variables over which counting takes place.
   * @param hardCounters idNumber variables for different values being counted. (hard)
   * @param softCounters idNumber variables that may be violated.
   * @param costVar a cost variable specifying the cost of violations.
   * @param violationMeasure it is only accepted to use Value_Based violation measure.
   */
  public SoftGCC(
      IntVar[] xvars,
      IntVar[] hardCounters,
      IntVar[] softCounters,
      IntVar costVar,
      ViolationMeasure violationMeasure) {

    this.countedValue = computeCountedValue(xvars);
    this.xvars = copyIntVarArray(xvars);
    this.softCounters = copyIntVarArray(softCounters);
    this.hardCounters = copyIntVarArray(hardCounters);

    this.costVar = costVar;
    this.violationMeasure = violationMeasure;
  }

  /**
   * Decomposes the constraint into primitive constraints.
   *
   * @param store the constraint store.
   * @return list of primitive constraints.
   */
  public List<Constraint> primitiveDecomposition(Store store) {

    if (decomposition == null) {
      decomposition = new ArrayList<>();
      buildValueBasedDecomposition(store, decomposition);
      return decomposition;
    }
    List<Constraint> result = new ArrayList<>();
    buildValueBasedDecomposition(store, result);
    return result;
  }

  private void buildValueBasedDecomposition(Store store, List<Constraint> target) {
    if (violationMeasure != ViolationMeasure.VALUE_BASED) {
      throw new UnsupportedOperationException("Unsupported violation measure " + violationMeasure);
    }
    List<IntVar> costs = new ArrayList<>(countedValue.length);
    for (int i = 0; i < countedValue.length; i++) {
      if (hardCounters != null && softLowerBound != null) {
        buildValueBasedHardCountersSoftBounds(store, target, costs, i);
      } else if (softCounters != null) {
        buildValueBasedSoftCounters(store, target, costs, i);
      }
    }
    target.add(new SumInt(costs, "==", costVar));
  }

  private void buildValueBasedHardCountersSoftBounds(
      Store store, List<Constraint> target, List<IntVar> costs, int i) {
    target.add(new Count(xvars, hardCounters[i], countedValue[i]));
    if (ASSERTS_ENABLED && (softLowerBound[i] < 0 || softLowerBound[i] > xvars.length)) {
      throw new IllegalStateException(
          String.valueOf(
              "LowerBound for " + i + "-th element must be between 0 and number of variables"));
    }
    if (ASSERTS_ENABLED && (softUpperBound[i] < 0 || softUpperBound[i] > xvars.length)) {
      throw new IllegalStateException(
          String.valueOf(
              "UpperBound for " + i + "-th element must be between 0 and number of variables"));
    }
    int[][] table = new int[xvars.length + 1][2];
    for (int j = 0; j <= xvars.length; j++) {
      table[j][0] = j;
      table[j][1] = 0;
      if (j < softLowerBound[i]) {
        table[j][1] = softLowerBound[i] - j;
      }
      if (j > softUpperBound[i]) {
        table[j][1] = j - softUpperBound[i];
      }
    }
    IntVar v = new IntVar(store, 0, xvars.length);
    costs.add(v);
    target.add(new ExtensionalSupportVa(new IntVar[] {hardCounters[i], v}, table));
  }

  private void buildValueBasedSoftCounters(
      Store store, List<Constraint> target, List<IntVar> costs, int i) {
    IntVar hardCounter =
        hardLowerBound != null
            ? new IntVar(store, hardLowerBound[i], hardUpperBound[i])
            : hardCounters[i];
    target.add(new Count(xvars, hardCounter, countedValue[i]));
    List<int[]> tuples = new ArrayList<>();
    for (ValueEnumeration hard = hardCounter.domain.valueEnumeration(); hard.hasMoreElements(); ) {
      int hardElement = hard.nextElement();
      for (ValueEnumeration soft = softCounters[i].domain.valueEnumeration();
          soft.hasMoreElements(); ) {
        int softElement = soft.nextElement();
        int cost =
            hardElement > softElement ? hardElement - softElement : softElement - hardElement;
        tuples.add(new int[] {hardElement, softElement, cost});
      }
    }
    IntVar v = new IntVar(store, 0, xvars.length);
    costs.add(v);
    target.add(
        new ExtensionalSupportVa(
            new IntVar[] {hardCounter, softCounters[i], v},
            tuples.toArray(new int[tuples.size()][3])));
  }

  @Override
  public List<Constraint> decompose(Store store) {

    if (decomposition == null || decomposition.size() > 1) {
      decomposition = new ArrayList<>();
      decomposition.add(buildSoftGCCConstraint());
    }

    return decomposition;
  }

  private Constraint buildSoftGCCConstraint() {
    IntDomain all = new IntervalDomain();
    for (int value : countedValue) {
      all.unionAdapt(value);
    }
    int d = all.getSize();
    IntDomain[] doms = new IntDomain[d];
    ValueEnumeration it = all.valueEnumeration();
    for (int i = 0; it.hasMoreElements(); i++) {
      int value = it.nextElement();
      doms[i] = new IntervalDomain(value, value);
    }
    return new SoftGCCBuilder(all, doms, violationMeasure).build();
  }

  @Override
  public void imposeDecomposition(Store store) {

    if (decomposition == null) {
      decomposition = decompose(store);
    }

    for (Constraint c : decomposition) {
      store.impose(c);
    }
  }

  @Override
  public String toString() {
    StringBuilder result = new StringBuilder();
    result.append(" : SoftGCC([");
    toStringAppendXvars(result);
    result.append("], [");
    toStringAppendCountedValue(result);
    result.append("], [");
    toStringAppendHardBounds(result);
    result.append("], [");
    toStringAppendSoftBounds(result);
    result.append("], ");
    result.append(costVar).append(", ").append(violationMeasure).append(")");
    return result.toString();
  }

  private void toStringAppendXvars(StringBuilder result) {
    for (int i = 0; i < xvars.length; i++) {
      result.append(xvars[i]);
      if (i < xvars.length - 1) {
        result.append(", ");
      }
    }
  }

  private void toStringAppendCountedValue(StringBuilder result) {
    for (int i = 0; i < countedValue.length; i++) {
      result.append(countedValue[i]);
      if (i < countedValue.length - 1) {
        result.append(", ");
      }
    }
  }

  private void toStringAppendHardBounds(StringBuilder result) {
    if (hardCounters == null) {
      for (int i = 0; i < hardLowerBound.length; i++) {
        result.append(hardLowerBound[i]).append("..").append(hardUpperBound[i]);
        if (i < hardLowerBound.length - 1) {
          result.append(", ");
        }
      }
    } else {
      for (int i = 0; i < hardCounters.length; i++) {
        result.append(hardCounters[i]);
        if (i < hardCounters.length - 1) {
          result.append(", ");
        }
      }
    }
  }

  private void toStringAppendSoftBounds(StringBuilder result) {
    if (softCounters == null) {
      for (int i = 0; i < softLowerBound.length; i++) {
        result.append(softLowerBound[i]).append("..").append(softUpperBound[i]);
        if (i < softLowerBound.length - 1) {
          result.append(", ");
        }
      }
    } else {
      for (int i = 0; i < softCounters.length; i++) {
        result.append(softCounters[i]);
        if (i < softCounters.length - 1) {
          result.append(", ");
        }
      }
    }
  }

  @SuppressWarnings("checkstyle:AbbreviationAsWordInName") // GCC is standard terminology
  private class SoftGCCBuilder extends NetworkBuilder {

    private SoftGCCBuilder(IntDomain all, IntDomain[] doms, ViolationMeasure vm) {
      super(costVar);
      if (vm != ViolationMeasure.VALUE_BASED) {
        throw new UnsupportedOperationException("Unknown violation measure : " + vm);
      }
      int n = xvars.length;
      int m = doms.length;
      Node[] xNodes = new Node[n];
      Node[] valueNodes = new Node[m];
      Node[] countNodes = new Node[m];
      for (int i = 0; i < n; i++) {
        xNodes[i] = addNode(xvars[i].id, 1);
      }
      for (int i = 0; i < m; i++) {
        valueNodes[i] = addNode(doms[i].toString(), 0);
      }
      for (int i = 0; i < m; i++) {
        countNodes[i] = addNode("c_" + doms[i].toString(), 0);
      }
      Node s = addNode("source", 0);
      Node t = addNode("sink", -n);
      addArc(t, s, 0, 0, n * countedValue.length);
      addValueBasedXArcs(all, doms, n, m, xNodes, valueNodes, t);
      addValueBasedCountArcs(n, s, t, countNodes, valueNodes);
    }

    private void addValueBasedXArcs(
        IntDomain all, IntDomain[] doms, int n, int m, Node[] xNodes, Node[] valueNodes, Node t) {
      for (int i = 0; i < n; i++) {
        IntVar v = xvars[i];
        List<Arc> arcs = new ArrayList<>();
        List<Domain> domains = new ArrayList<>();
        IntDomain vDom = v.domain;
        for (int j = 0; j < m; j++) {
          if (vDom.isIntersecting(doms[j])) {
            arcs.add(addArc(xNodes[i], valueNodes[j], 0, 1));
            domains.add(doms[j]);
          }
          IntDomain notCounted = vDom.subtract(all);
          if (!notCounted.isEmpty()) {
            arcs.add(addArc(xNodes[i], t, 0, 1));
            domains.add(notCounted);
          }
        }
        handlerList.add(new DomainStructure(v, domains, arcs));
      }
    }

    private void addValueBasedCountArcs(
        int n, Node s, Node t, Node[] countNodes, Node[] valueNodes) {
      for (int i = 0; i < countNodes.length; i++) {
        if (softLowerBound != null) {
          addArc(s, countNodes[i], 1, 0, softLowerBound[i]);
        } else {
          addArc(s, countNodes[i], 1, 0, softCounters[i].max());
        }
        int excessCap = softUpperBound != null ? n - softUpperBound[i] : n - softCounters[i].min();
        if (excessCap > 0) {
          addArc(countNodes[i], t, 1, 0, excessCap);
        }
        if (hardCounters != null) {
          addArc(valueNodes[i], countNodes[i], 0, hardCounters[i]);
        } else {
          addArc(valueNodes[i], countNodes[i], 0, hardLowerBound[i], hardUpperBound[i]);
        }
        if (softLowerBound != null) {
          addArc(countNodes[i], t, 0, softLowerBound[i], softUpperBound[i]);
        } else {
          addArc(countNodes[i], t, 0, softCounters[i]);
        }
      }
    }
  }
}
