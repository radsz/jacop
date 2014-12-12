/**
 *  Pruning.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

package org.jacop.constraints.netflow;

import static org.jacop.constraints.netflow.Assert.checkFlow;
import static org.jacop.constraints.netflow.Assert.checkStructure;

import java.util.ArrayList;
import java.util.List;
import java.util.PriorityQueue;

import org.jacop.constraints.netflow.DomainStructure.Behavior;
import org.jacop.constraints.netflow.simplex.Arc;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;

/**
 * 
 * @author Robin Steiger and Radoslaw Szymanek
 * @version 4.2
 * 
 */

public class Pruning extends Network {

	// whether to count success rates, etc..
	private static final boolean DO_INSTRUMENTATION = false;

	// minimum number of pruned arcs of call
	private static final int MIN_NUM_PRUNING = 0;

	// percent of pruned arcs of call
	private static final double P_ATTEMPT_PRUNING = 1.0;

	// Increase in score upon successful pruning
	private static final int SUCCESS_SCORE = 5;

	// Decrease in score upon successful pruning
	private static final int FAIL_SCORE = 2;

	interface PruningStrategy {
		
		void init();

		ArcCompanion next();

		void close();
	}

	// int z;
	//
	// private void checkCount() {
	// z++;
	// int count = 0;
	// for (ArcCompanion c : queue) {
	// if (c.arc.index != DELETED_ARC)
	// count++;
	// else
	// assert (c.xVar.singleton()) : c.xVar;
	// }
	// assert (count == numActiveArcs) : count + " != " + numActiveArcs
	// + "  (" + z + ")";
	// }

	public class PercentStrategy implements PruningStrategy {
	
		ArrayList<ArcCompanion> seen = new ArrayList<ArcCompanion>();
		
		int i;
		final double percentage;
		int limit;
		final int minimum;

		PercentStrategy(double percentage, int minimum) {
			this.percentage = percentage;
			this.minimum = minimum;
		}

		public void init() {
			int numActiveArcs = 0;
			for (ArcCompanion c : queue) {
				if (c.arc.index != DELETED_ARC)
					numActiveArcs++;
			}

			i = 0;
			limit = Math.max(Math.min(minimum, numActiveArcs), (int) Math
					.round(numActiveArcs * percentage));

			// checkCount();
		}

		public ArcCompanion next() {
			if (i < limit) {
				ArcCompanion companion = queue.poll();
				seen.add(companion);
				while (companion.arc.index == DELETED_ARC) {
					return next();
				}
				i++;
				return companion;
			}
			// assert (queue.peek().arc.index == DELETED_ARC);
			return null;
		}

		public void close() {
			queue.addAll(seen);
			seen.clear();
		}
	}

	private PriorityQueue<ArcCompanion> queue;
	private PruningStrategy strategy;
	public int numActiveArcs;

	public Pruning(List<Node> nodes, List<Arc> arcs) {

		super(nodes, arcs);
		
		this.queue = new PriorityQueue<ArcCompanion>();
		this.strategy = new PercentStrategy(P_ATTEMPT_PRUNING, MIN_NUM_PRUNING);

		for (Arc arc : arcs) {
			if (arc.hasCompanion() && arc.index != DELETED_ARC)
				queue.add(arc.getCompanion());
		}
		this.numActiveArcs = queue.size();

		// checkCount();
	}

	private void xVarInMax(ArcCompanion companion, int maxFlow) {
		
		IntVar xVar = companion.xVar;
		int sizeBefore;
		if (DO_INSTRUMENTATION) {
			Statistics.XVARS.arcsExamined++;
			sizeBefore = xVar.domain.getSize();
		}
		xVar.domain.inMax(store.level, xVar, maxFlow);
		if (DO_INSTRUMENTATION) {
			int sizeAfter = xVar.domain.getSize();
			if (sizeAfter < sizeBefore) {
				Statistics.XVARS.arcsPruned++;
				Statistics.XVARS.amountPruned += (sizeBefore - sizeAfter);
				companion.pruningScore += SUCCESS_SCORE;
			} else {
				companion.pruningScore -= FAIL_SCORE;
			}
		}
	}

	private void xVarInMin(ArcCompanion companion, int minFlow) {
		
		IntVar xVar = companion.xVar;
		int sizeBefore;
		if (DO_INSTRUMENTATION) {
			Statistics.XVARS.arcsExamined++;
			sizeBefore = xVar.domain.getSize();
		}
		xVar.domain.inMin(store.level, xVar, minFlow);
		if (DO_INSTRUMENTATION) {
			int sizeAfter = xVar.domain.getSize();
			if (sizeAfter < sizeBefore) {
				Statistics.XVARS.arcsPruned++;
				Statistics.XVARS.amountPruned += (sizeBefore - sizeAfter);
				companion.pruningScore += SUCCESS_SCORE;
			} else {
				companion.pruningScore -= FAIL_SCORE;
			}
		}
	}

	private void nVarIn(ArcCompanion companion, int minFlow, int maxFlow) {
		IntVar nVar = companion.xVar;
		int sizeBefore;
		if (DO_INSTRUMENTATION) {
			Statistics.NVARS.arcsExamined++;
			sizeBefore = nVar.domain.getSize();
		}
		nVar.domain.in(store.level, nVar, minFlow, maxFlow);
		if (DO_INSTRUMENTATION) {
			int sizeAfter = nVar.domain.getSize();
			if (sizeAfter < sizeBefore) {
				Statistics.NVARS.arcsPruned++;
				Statistics.NVARS.amountPruned += (sizeBefore - sizeAfter);
				companion.pruningScore += SUCCESS_SCORE;
			} else {
				companion.pruningScore -= FAIL_SCORE;
			}
		}
	}

	private void nVarInShift(ArcCompanion companion, IntDomain domain, int shift) {
		IntVar nVar = companion.xVar;
		int sizeBefore;
		if (DO_INSTRUMENTATION) {
			Statistics.NVARS.arcsExamined++;
			sizeBefore = nVar.domain.getSize();
		}
		nVar.domain.inShift(store.level, nVar, domain, shift);
		if (DO_INSTRUMENTATION) {
			int sizeAfter = nVar.domain.getSize();
			if (sizeAfter < sizeBefore) {
				Statistics.NVARS.arcsPruned++;
				Statistics.NVARS.amountPruned += (sizeBefore - sizeAfter);
				companion.pruningScore += SUCCESS_SCORE;
			} else {
				companion.pruningScore -= FAIL_SCORE;
			}
		}
	}

	private void wVarIn(ArcCompanion companion, int maxCost) {
		IntVar wVar = companion.wVar;
		int sizeBefore;
		if (DO_INSTRUMENTATION) {
			Statistics.WVARS.arcsExamined++;
			sizeBefore = wVar.domain.getSize();
		}
		wVar.domain.inMax(store.level, wVar, maxCost);

		if (DO_INSTRUMENTATION) {
			int sizeAfter = wVar.domain.getSize();
			if (sizeAfter < sizeBefore) {
				Statistics.WVARS.arcsPruned++;
				Statistics.WVARS.amountPruned += (sizeBefore - sizeAfter);
				companion.pruningScore += SUCCESS_SCORE;
			} else {
				companion.pruningScore -= FAIL_SCORE;
			}
		}
	}

	private void sVarInDom(ArcCompanion companion, Domain domain) {
		IntVar sVar = companion.structure.variable;
		int sizeBefore;
		if (DO_INSTRUMENTATION) {
			Statistics.SVARS.arcsExamined++;
			sizeBefore = sVar.domain.getSize();
		}
		sVar.domain.in(store.level, sVar, domain);
		if (DO_INSTRUMENTATION) {
			int sizeAfter = sVar.domain.getSize();
			if (sizeAfter < sizeBefore) {
				Statistics.SVARS.arcsPruned++;
				Statistics.SVARS.amountPruned += (sizeBefore - sizeAfter);
				companion.pruningScore += SUCCESS_SCORE;
			} else {
				companion.pruningScore -= FAIL_SCORE;
			}
		}
	}

	void pruneNodesWithSmallDegree() {
		// TODO filter arcs with x-variables first ?
		// It should work on fixpoint principle, so there is propagation in the chain of 2-degree nodes.
		for (Node node : nodes) {
			if (node.degree == 1) {
				Arc arc = node.adjacencyList[0];

				ArcCompanion companion = arc.companion;
				if (companion != null && companion.xVar != null) {

					int flow = companion.flowOffset + arc.sister.capacity;
					if (arc.head == node) {
						assert (arc.sister.capacity == -node.balance) : "\n"
								+ node + "\n" + arc;
					} else {
						assert (arc.sister.capacity == node.balance) : "\n"
								+ node + "\n" + arc;
					}
					nVarIn(companion, flow, flow);
				}
			} else if (node.degree == 2) {
				
				Arc arc1 = node.adjacencyList[0];
				Arc arc2 = node.adjacencyList[1];

				ArcCompanion companion1 = arc1.companion;
				ArcCompanion companion2 = arc2.companion;
				if (companion1 != null && companion1.xVar != null
						&& companion2 != null && companion2.xVar != null) {

					boolean differentDir;
					int shift = -companion1.flowOffset;
					
					if (arc1.head == node) {
						differentDir = (arc2.head != node);
						shift += node.balance;
					} else {
						differentDir = (arc2.head == node);
						shift -= node.balance;
					}
					
					if (differentDir) {
						shift += companion2.flowOffset;
					} else {
						shift -= companion2.flowOffset;
					}

					IntVar xVar1 = companion1.xVar;
					IntVar xVar2 = companion2.xVar;
					if (differentDir) {
						nVarInShift(companion1, xVar2.domain, -shift);
						nVarInShift(companion2, xVar1.domain, shift);
					} else {
						// TODO Double test this code.

						IntDomain xDom = xVar1.dom();
						IntervalDomain yDomIn = new IntervalDomain(xDom.noIntervals() + 1);
						for (int i = xDom.noIntervals() - 1; i >= 0; i--)
							yDomIn.unionAdapt(new Interval(-shift - xDom.rightElement(i), -shift
									- xDom.leftElement(i)));

						nVarInShift(companion2, yDomIn, 0);
						
						IntDomain yDom = xVar2.domain;
						IntervalDomain xDomIn = new IntervalDomain(yDom.noIntervals() + 1);
						for (int i = yDom.noIntervals() - 1; i >= 0; i--)
							xDomIn.unionAdapt(new Interval(-shift - yDom.rightElement(i), -shift
									- yDom.leftElement(i)));

						nVarInShift(companion1, xDomIn, 0);

					}
				}
			}
		}
	}

	public void analyze(int costLimit) {
		
		ArcCompanion companion, prev = null;
		strategy.init();

		companion = strategy.next();
		
		if (DO_INSTRUMENTATION) {
			if (companion != null) {
				Statistics.XVARS.maxScoreSum += companion.pruningScore;
				Statistics.WVARS.maxScoreSum += companion.pruningScore;
				Statistics.SVARS.maxScoreSum += companion.pruningScore;
			}
		}

		while (companion != null) {

			Arc arc1 = companion.arc;
			Arc arc2 = arc1.sister;
			int residual1 = arc1.capacity;
			int residual2 = arc2.capacity;

			if (residual1 == 0) {
				analyzeArcHelper(arc2, costLimit);
			} else if (residual2 == 0) {
				analyzeArcHelper(arc1, costLimit);
			} else if (residual1 < residual2) {
				analyzeArcHelper(arc1, costLimit);
				analyzeArcHelper(arc2, costLimit);
			} else {
				analyzeArcHelper(arc2, costLimit);
				analyzeArcHelper(arc1, costLimit);
			}

			if (companion.wVar != null && companion.flowOffset > 0) {
				int maxCost = companion.wVar.min()
						+ (costLimit / companion.flowOffset);
				wVarIn(companion, maxCost);
			}

			prev = companion;
			companion = strategy.next();
		}
		if (DO_INSTRUMENTATION) {
			if (prev != null) {
				Statistics.XVARS.minScoreSum += prev.pruningScore;
				Statistics.WVARS.minScoreSum += prev.pruningScore;
				Statistics.SVARS.minScoreSum += prev.pruningScore;
			}
		}
		strategy.close();
	}

	private void analyzeArcHelper(Arc arc, int costLimit) {
		if (arc.capacity == 0)
			return;

		long cost = cost(Long.MAX_VALUE);
		int capacity = arc.capacity;
		int flow = analyzeArc(arc, costLimit);
		assert (arc.capacity == (capacity - flow));

		final int _capacity = arc.capacity;
		final int _residual = arc.sister.capacity;
		final boolean _forward = arc.forward;
		final ArcCompanion _companion = arc.getCompanion();

		if (arc.index == DELETED_ARC) {
			addArcWithFlow(arc);
		}
		assert (checkFlow(this));
		assert (checkStructure(this));

		if (DO_INSTRUMENTATION) {
			if (_companion.xVar != null)
				Statistics.XVARS.arcsExamined++;
			if (_companion.wVar != null)
				Statistics.WVARS.arcsExamined++;
			if (_companion.structure != null)
				Statistics.SVARS.arcsExamined++;
		}

		if (_capacity > 0) {
			pruneArc(_capacity, _residual, _forward, _companion);
		}

		// restore optimal flow
		// if (cost(Long.MAX_VALUE) != cost)
		networkSimplex(999999);

		assert (cost(Long.MAX_VALUE) == cost) : cost(Long.MAX_VALUE) + " != "
				+ cost;

	}

	private int analyzeArc(Arc arc, int costLimit) {
		assert (arc.capacity > 0);

		// Remove arc from graph
		if (arc.index == TREE_ARC) {
			if (!dualPivot(arc.sister)) {
				// This is the last arc in the cut, prune all remaining capacity
				return 0;
			}
		}
		removeArc(arc);

		// perform sensitivity analysis
		int flow = 0;
		int capacity = arc.capacity;
		Node source = arc.head;
		Node sink = arc.tail();

		/*
		 * int baseFlow = arc.getCompanion().flowOffset; if (arc.forward)
		 * baseFlow += arc.sister.capacity; else baseFlow += arc.capacity; int
		 * maxWeight = (baseFlow > 0) ? costLimit / baseFlow :
		 * Integer.MAX_VALUE; int flowAtMaxWeight = baseFlow;
		 */

		while (capacity > 0) {
			int unitCost = arc.reducedCost(); // + arc.cost;
			assert (unitCost >= 0);
			if (unitCost > 0) {
				int maxCapacity = costLimit / unitCost;
				if (capacity > maxCapacity) {
					capacity = maxCapacity;
					if (capacity == 0) {
						break;
					}
				}
			}

			int delta = augmentFlow(source, sink, capacity);
			flow += delta;
			capacity -= delta;
			costLimit -= unitCost * delta;
			// costLimit -= arc.cost * delta;

			/*
			 * int currentFlow = baseFlow + ((arc.forward) ? flow : -flow); if
			 * (currentFlow > 0) { int deltaWeight = costLimit / currentFlow; if
			 * (maxWeight < deltaWeight) { maxWeight = deltaWeight;
			 * flowAtMaxWeight = currentFlow; } }
			 */

			if (capacity == 0 || !dualPivot(blocking)) {
				break;
			}
		}

		IntVar wVar = arc.getCompanion().wVar;

		if (arc.cost != -arc.sister.cost)
			throw new AssertionError();
		if (wVar != null) {
			if (arc.forward && wVar.min() != arc.cost)
				throw new AssertionError();
			if (!arc.forward && wVar.min() != -arc.cost)
				throw new AssertionError();
		}
		/*
		 * if (maxWeight != Integer.MAX_VALUE || wVar != null) { // if
		 * (flowAtMaxWeight != baseFlow || !arc.forward) { // if
		 * (flowAtMaxWeight > baseFlow && arc.forward) { // int max = wVar.min()
		 * + maxWeight; // wVar.domain.inMax(store.level, wVar, max); //
		 * System.out.println("LOL"); // } if (flowAtMaxWeight > baseFlow &&
		 * !arc.forward) { int max = wVar.min() + maxWeight;
		 * wVar.domain.inMax(store.level, wVar, max); System.out.println("LOL");
		 * } }
		 */

		arc.addFlow(flow);
		// if (SHOW_ANALYSIS && getStoreLevel() >= 5)
		// System.out.println("New flow " + arc);

		return flow;
	}

	private void pruneArc(int capacity, int residual, boolean forward,
			ArcCompanion companion) {
		assert (capacity > 0);

		// int level = store.level;
		if (forward) {
			// prune upper capacity bound
			if (companion.xVar != null) {
				int maxFlow = companion.flowOffset + residual;

				// System.out.println(level + ": " + companion.xVar
				// + " prune max to " + maxFlow);
				// companion.xVar.domain.inMax(level, companion.xVar, maxFlow);
				xVarInMax(companion, maxFlow);
				companion.changeMaxCapacity(maxFlow);
				modified(companion);
			}
			DomainStructure structure = companion.structure;
			if (companion.structure != null
					&& !structure.isGrounded(companion.arcID)) {
				int arcID = companion.arcID;

				if (structure.behavior != Behavior.PRUNE_INACTIVE) {
					Domain arcDomainC = structure.domains[arcID].complement();
					sVarInDom(companion, arcDomainC);
				}
			}
		} else {
			// prune lower capacity bound
			if (companion.xVar != null) {
				int minFlow = companion.flowOffset + capacity;

				// System.out.println(level + ": " + companion.xVar
				// + " prune min to " + minFlow);
				// companion.xVar.domain.inMin(level, companion.xVar, minFlow);
				xVarInMin(companion, minFlow);
				companion.changeMinCapacity(minFlow);
				modified(companion);
			}
			DomainStructure structure = companion.structure;
			if (companion.structure != null
					&& !structure.isGrounded(companion.arcID)) {
				int arcID = companion.arcID;

				if (structure.behavior != Behavior.PRUNE_ACTIVE) {
					Domain arcDomain = structure.domains[arcID];
					sVarInDom(companion, arcDomain);
				}
			}
		}
	}
}
