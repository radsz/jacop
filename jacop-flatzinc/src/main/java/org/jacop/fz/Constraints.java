/*
 * Constraints.java
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

package org.jacop.fz;

import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.UncheckedIOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Set;
import org.jacop.constraints.lp.TimeIndexedBound;
import org.jacop.core.BooleanVar;
import org.jacop.core.FailException;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.core.FloatVar;
import org.jacop.fz.constraints.AffineFolding;
import org.jacop.fz.constraints.AgreementCountDetector;
import org.jacop.fz.constraints.AlldiffChannels;
import org.jacop.fz.constraints.AlldifferentDetector;
import org.jacop.fz.constraints.AntichainDetector;
import org.jacop.fz.constraints.ArgMaxFunctionDetector;
import org.jacop.fz.constraints.BalanceDetector;
import org.jacop.fz.constraints.CardinalityDetector;
import org.jacop.fz.constraints.CircuitCostDetector;
import org.jacop.fz.constraints.ClampedBounds;
import org.jacop.fz.constraints.ClausalCompiler;
import org.jacop.fz.constraints.ColouredTreeDetector;
import org.jacop.fz.constraints.CommonSubexpressions;
import org.jacop.fz.constraints.ConjunctionSumDetector;
import org.jacop.fz.constraints.ConstraintFncs;
import org.jacop.fz.constraints.ConvexAllocationDetector;
import org.jacop.fz.constraints.CostNetworkDetector;
import org.jacop.fz.constraints.CountPartnersDetector;
import org.jacop.fz.constraints.CyclicDistanceDetector;
import org.jacop.fz.constraints.DifferenceBoundsDetector;
import org.jacop.fz.constraints.DifferenceCyclesDetector;
import org.jacop.fz.constraints.DisjunctiveCliqueDetector;
import org.jacop.fz.constraints.ElementTableDetector;
import org.jacop.fz.constraints.EnforcementInliner;
import org.jacop.fz.constraints.ExactCoverDetector;
import org.jacop.fz.constraints.GiantTourDetector;
import org.jacop.fz.constraints.IncreasingDetector;
import org.jacop.fz.constraints.IndexDisjunctionDetector;
import org.jacop.fz.constraints.IndexFunctionDetector;
import org.jacop.fz.constraints.IntensionTableDetector;
import org.jacop.fz.constraints.KnapsackDetector;
import org.jacop.fz.constraints.LinearOverlapDetector;
import org.jacop.fz.constraints.LinearRelaxationCheck;
import org.jacop.fz.constraints.LinearSystemDetector;
import org.jacop.fz.constraints.ListsDifferDetector;
import org.jacop.fz.constraints.LoadFunctionDetector;
import org.jacop.fz.constraints.MaxCliqueDetector;
import org.jacop.fz.constraints.MinOfSumsDetector;
import org.jacop.fz.constraints.NumberedPathDetector;
import org.jacop.fz.constraints.ObjectiveScaling;
import org.jacop.fz.constraints.PairCoverDetector;
import org.jacop.fz.constraints.PartialCopyDetector;
import org.jacop.fz.constraints.PermutedTasksDetector;
import org.jacop.fz.constraints.PrecedenceCostDetector;
import org.jacop.fz.constraints.PrecedenceDetector;
import org.jacop.fz.constraints.ProductOfSumsDetector;
import org.jacop.fz.constraints.ProgressionTilingDetector;
import org.jacop.fz.constraints.RegularFlowDetector;
import org.jacop.fz.constraints.RoutesDetector;
import org.jacop.fz.constraints.SaturatedProducts;
import org.jacop.fz.constraints.SequenceDetector;
import org.jacop.fz.constraints.SequenceMddDetector;
import org.jacop.fz.constraints.SetUnionDetector;
import org.jacop.fz.constraints.StockingCostDetector;
import org.jacop.fz.constraints.SuccessorForestDetector;
import org.jacop.fz.constraints.Support;
import org.jacop.fz.constraints.SymmetricGCCDetector;
import org.jacop.fz.constraints.TableCoverDetector;
import org.jacop.fz.constraints.TableScopeMerger;
import org.jacop.fz.constraints.TableVariableElimination;
import org.jacop.fz.constraints.TranslationTilingDetector;
import org.jacop.fz.constraints.WeightedCompletionDetector;
import org.jacop.fz.constraints.XorSystemDetector;
import org.jacop.fz.constraints.ZeroSumDetector;
import org.jacop.jasat.lcg.LcgSolver;
import org.jacop.lcg.AtomicTrail;
import org.jacop.satwrapper.SatTranslation;

/**
 * The part of the parser responsible for parsing constraints.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class Constraints implements ParserTreeConstants {

  static final int EQ = 0;
  static final int NE = 1;
  static final int LT = 2;
  static final int GT = 3;
  static final int LE = 4;
  static final int GE = 5;
  final ConstraintFncs cf;
  final Tables dictionary;
  final Store store;
  // ============ SAT solver interface ==============
  final float satThreshold = 1.0f; // 1.0 pure SAT problem, 0.85 good heuristic ;)
  final SatTranslation sat;
  final Support support;
  String p;

  // constraint generators by name; getMethod scans every public method on each call
  final Map<String, java.lang.reflect.Method> generators = new HashMap<>();
  boolean debug;
  long boolClauses;
  long noConstraints;
  long bool2Int;

  /**
   * It creates an object to parse the constraint part of the flatzinc file.
   *
   * @param store the constraint store in which the constraints are being created.
   * @param dict the current dictionary (tables of all variables and constants)
   */
  public Constraints(Store store, Tables dict) {
    this.store = store;
    this.dictionary = dict;

    sat = new SatTranslation(store);
    // impose SAT-solver
    sat.impose();

    support = new Support(store, dict, sat);

    cf = new ConstraintFncs(support);
  }

  void setOptions(Options options) {
    support.options = options;
    debug = options.debug();
  }

  void generateAllConstraints(SimpleNode astTree) throws Throwable {

    // an objective declared beyond the integer range is divided by the factor its definition
    // forces on it, instead of being narrowed
    ObjectiveScaling.apply(support, astTree);
    if (dictionary.domainsClamped()) {
      if (dictionary.boundedDomainsClamped()) {
        System.err.println(dictionary.clampedDomainsWarning());
      }
      dictionary.recordDeclaredDomains();
      dictionary.setSaturationCandidates(
          SaturatedProducts.find(
              support, astTree, ObjectiveScaling.objective(dictionary, astTree)));
      // reads the rows as declared, before the detectors replace constraints, to show the
      // narrowing of domains harmless at the end or when the model fails while it is translated
      dictionary.setClampedBounds(
          new ClampedBounds(
              support,
              astTree,
              dictionary.narrowedVariables(),
              dictionary::declaredBounds,
              dictionary.saturatedProducts()));
    }

    Options options = support.options;
    boolean manySolutions =
        (options.getAll() || options.getNumberSolutions() > 1) && satisfaction(astTree);
    // the exchanges of values that symmetry breaking breaks in a satisfaction problem compare the
    // domains of inverse channels as declared
    if (options.symmetry()
        && ConditionalValueSwaps.ENABLED
        && !options.freeSearch()
        && !manySolutions
        && satisfaction(astTree)) {
      support.recordChannelDomains(astTree);
    }
    if (hasFloatVariables()) {
      // the model is built as without LCG, also when --lcg was given: LcgSolver has no atoms for
      // float variables, and a model built for LCG (clauses, split sums, no views) and then solved
      // by search is not the model solved without --lcg
      options.dropLcg("the model has float variables");
    } else if (manySolutions && options.lcgEnumerates()) {
      // LCG enumerates the solutions with blocking clauses over the output variables (see
      // LcgSolver.setEnumeration); the reformulations that lose solutions are off, as without LCG
      if (options.debug()) {
        FzConsole.println("% many solutions: enumerated by LCG");
      }
    } else if (options.getAll() && satisfaction(astTree)) {
      options.dropLcg("all solutions are not supported");
    } else if (manySolutions) {
      // LCG on by default is left out where it would be ignored; the model is solved as before
      options.dropDefaultLcg();
    } else if (options.lcg()
        && MaxCliqueDetector.enabled()
        && !MaxCliqueDetector.keepsLcg()
        && options.proof() == null
        && new MaxCliqueDetector(support).pure(astTree)) {
      // maximum clique alone: branch and bound with the coloring bound, without learning
      options.dropDefaultLcg();
      if (options.debug()) {
        FzConsole.println("% maximum clique model: LCG on by default left out");
      }
    }
    if (options.lcg() || options.useSat() && options.presolve() != Options.Presolve.OFF) {
      // Boolean constraints become clauses of the LCG solver, or of the SAT solver of -sat once
      // presolve has preprocessed them; Solve posts them
      sat.collectClauses();
    }
    // a satisfaction model over small domains under free search is also compiled into one CNF,
    // which Solve gives to JaSAT; the store is built as usual, to check the solution
    if (ClausalCompiler.enabled()
        && options.lcg()
        && options.proof() == null
        && !manySolutions
        && satisfaction(astTree)
        && freeSearchModel(astTree, options)) {
      dictionary.clausalModel = ClausalCompiler.compile(support, astTree);
    }
    if (options.proof() != null && options.lcg()) {
      // the constraints propagate as they are imposed; the proof derives their changes from the
      // domains the model states
      dictionary.rootTrail = new AtomicTrail(store);
      store.recentlyFailedConstraint = null;
    }
    try {

      if (support.options.debug()) {
        FzConsole.println(
            "% bool constraints = "
                + boolClauses
                + " of "
                + (noConstraints - bool2Int)
                + " p = "
                + (float) boolClauses / (float) (noConstraints - bool2Int));
      }

      if ((float) boolClauses / (float) (noConstraints - bool2Int) >= satThreshold) {
        support.options.setSat();
      }

      sat.setDebug(debug);

      // disequalities that are part of a detected all-different constraint, and the constraints of
      // merged copies of partial function results
      Set<SimpleNode> replaced = Set.of();
      Set<IntVar> tabled = Set.of();
      // the conflicts of a model of maximum clique alone are enforced by its bound
      boolean pureClique = false;
      if (MaxCliqueDetector.enabled() && options.proof() == null) {
        Set<SimpleNode> pairs = new MaxCliqueDetector(support).replacedPairs(astTree);
        if (!pairs.isEmpty()) {
          replaced = new HashSet<>(pairs);
          pureClique = true;
        }
      }
      cf.setClauseModel(clauseModel(astTree));
      // a search variable that became an alias is searched as its Boolean
      dictionary.searchAliasTargets(dictionary.binaryEqAliases);
      // the same function of the same inputs is computed once; --proof encodes the model as given
      if (CommonSubexpressions.enabled() && options.proof() == null) {
        Set<IntVar> pinned = solveItemVariables(astTree);
        dictionary.addDeclaredEqualities(pinned);
        CommonSubexpressions cse = new CommonSubexpressions(support, pinned);
        cse.detect(astTree);
        if (!cse.replaced().isEmpty()) {
          replaced = new HashSet<>(cse.replaced());
        }
      }
      // variables that are affine functions of others and only terms of linear rows are folded
      // into those rows, which the later detectors then read
      if (AffineFolding.enabled() && options.proof() == null) {
        AffineFolding folding = new AffineFolding(support, keptVariables(astTree));
        folding.detect(astTree, replaced);
        if (!folding.replaced().isEmpty()) {
          replaced = new HashSet<>(replaced);
          replaced.addAll(folding.replaced());
          dictionary.removeFromDefaultSearch(folding.removed());
          dictionary.unusedVariables.addAll(folding.removed());
        }
      }
      if (PartialCopyDetector.enabled()) {
        Set<SimpleNode> copies = new PartialCopyDetector(support).detect(astTree);
        if (replaced.isEmpty()) {
          replaced = copies;
        } else {
          replaced.addAll(copies);
        }
        dictionary.removeAliasFromSearch();
      }
      if (AlldifferentDetector.enabled()) {
        AlldifferentDetector alldifferent = new AlldifferentDetector(support);
        alldifferent.detect(astTree);
        if (replaced.isEmpty()) {
          replaced = alldifferent.replaced();
        } else {
          replaced = new HashSet<>(replaced);
          replaced.addAll(alldifferent.replaced());
        }
      }

      // small expressions flattened into several constraints become the table of their solutions
      // over the model's variables; solutions that differ only in internal variables would merge,
      // so not when all solutions are searched for, and --proof does not encode tables
      if (IntensionTableDetector.enabled()
          && options.proof() == null
          && (!manySolutions || IntensionTableDetector.forced())) {
        IntensionTableDetector intensions = new IntensionTableDetector(support);
        intensions.detect(astTree, replaced);
        if (!intensions.replaced().isEmpty()) {
          replaced = new HashSet<>(replaced);
          replaced.addAll(intensions.replaced());
          dictionary.removeFromDefaultSearch(intensions.unconstrained());
          dictionary.unusedVariables.addAll(intensions.unconstrained());
          tabled = intensions.tabled();
        }
      }

      // the tables check their rows against the domains, and --proof does not encode them
      if (ElementTableDetector.enabled() && options.proof() == null) {
        ElementTableDetector elements = new ElementTableDetector(support);
        elements.detect(astTree);
        if (!elements.replaced().isEmpty()) {
          replaced = new HashSet<>(replaced);
          replaced.addAll(elements.replaced());
        }
      }

      // the tables over the same variables become one, before the parts of each are posted
      if (TableScopeMerger.enabled() && options.proof() == null) {
        TableScopeMerger tables = new TableScopeMerger(support);
        tables.detect(astTree);
        if (!tables.replaced().isEmpty()) {
          replaced = new HashSet<>(replaced);
          replaced.addAll(tables.replaced());
        }
      }

      // short tables saying that two lists differ become AllDifferentLists over groups of lists
      if (ListsDifferDetector.enabled() && options.proof() == null) {
        ListsDifferDetector lists = new ListsDifferDetector(support);
        lists.detect(astTree);
        if (!lists.replaced().isEmpty()) {
          replaced = new HashSet<>(replaced);
          replaced.addAll(lists.replaced());
        }
      }

      // a Hamiltonian path written as a numbering gets its successor model with a circuit
      if (NumberedPathDetector.enabled() && options.proof() == null) {
        new NumberedPathDetector(support).detect(astTree);
      }

      // the variables of degree two between tables and elements are joined out of the model, and
      // given values again when a solution is printed
      if (TableVariableElimination.enabled() && options.proof() == null && !manySolutions) {
        TableVariableElimination elimination =
            new TableVariableElimination(support, replaced, solveItemVariables(astTree));
        elimination.detect(astTree);
        if (!elimination.replaced().isEmpty()) {
          replaced = new HashSet<>(replaced);
          replaced.addAll(elimination.replaced());
          dictionary.removeFromDefaultSearch(elimination.eliminated());
          dictionary.unusedVariables.addAll(elimination.eliminated());
          dictionary.tableElimination = elimination;
          for (Map.Entry<IntVar[], int[][]> t : elimination.tables()) {
            cf.poseTable(t.getKey(), t.getValue());
          }
        }
      }

      // index variables that only pick the position where a relation holds become a disjunction
      // over the positions, and get their values again when a solution is printed
      if (IndexDisjunctionDetector.enabled()
          && options.proof() == null
          && options.presolve() == Options.Presolve.OFF
          && !manySolutions) {
        IndexDisjunctionDetector disjunctions =
            new IndexDisjunctionDetector(support, cf, replaced, solveItemVariables(astTree));
        disjunctions.detect(astTree);
        if (!disjunctions.replaced().isEmpty()) {
          replaced = new HashSet<>(replaced);
          replaced.addAll(disjunctions.replaced());
          dictionary.removeFromDefaultSearch(disjunctions.eliminated());
          dictionary.unusedVariables.addAll(disjunctions.eliminated());
          dictionary.indexDisjunctions = disjunctions.values();
        }
      }

      // an arg_max over functions of other variables runs on those variables, whose bounds its
      // explanations then share across arg_max constraints
      if (ArgMaxFunctionDetector.enabled() && options.proof() == null) {
        ArgMaxFunctionDetector argMax = new ArgMaxFunctionDetector(support, replaced);
        argMax.detect(astTree);
        if (!argMax.replaced().isEmpty()) {
          replaced = new HashSet<>(replaced);
          replaced.addAll(argMax.replaced());
        }
      }

      // the membership clauses replace set unions, which --proof encodes as they are
      if (SetUnionDetector.enabled() && options.proof() == null) {
        SetUnionDetector unions = new SetUnionDetector(support);
        unions.detect(astTree);
        if (!unions.replaced().isEmpty()) {
          replaced = new HashSet<>(replaced);
          replaced.addAll(unions.replaced());
          dictionary.removeFromDefaultSearch(unions.unconstrained());
          dictionary.unusedVariables.addAll(unions.unconstrained());
        }
      }

      if (MinOfSumsDetector.enabled()) {
        MinOfSumsDetector minOfSums = new MinOfSumsDetector(support);
        Set<SimpleNode> merged = minOfSums.detect(astTree);
        if (!merged.isEmpty()) {
          replaced = new HashSet<>(replaced);
          replaced.addAll(merged);
          dictionary.removeFromDefaultSearch(minOfSums.removed());
          dictionary.unusedVariables.addAll(minOfSums.removed());
        }
      }

      // a cyclic distance min(|e|, c - |e|) also as |e + c * k|, which a bound narrows
      if (CyclicDistanceDetector.enabled() && options.proof() == null) {
        CyclicDistanceDetector cyclic = new CyclicDistanceDetector(support);
        Set<SimpleNode> distances = cyclic.detect(astTree);
        if (!distances.isEmpty()) {
          replaced = new HashSet<>(replaced);
          replaced.addAll(distances);
          dictionary.removeFromDefaultSearch(cyclic.removed());
          dictionary.unusedVariables.addAll(cyclic.removed());
        }
      }

      // a product of two functions of one index variable as a sum over the index's value literals
      if (IndexFunctionDetector.enabled() && options.proof() == null) {
        Set<SimpleNode> products = new IndexFunctionDetector(support).detect(astTree);
        if (!products.isEmpty()) {
          replaced = new HashSet<>(replaced);
          replaced.addAll(products);
        }
      }

      IncreasingDetector increasing = null;
      if (IncreasingDetector.sumEnabled() || IncreasingDetector.nvalueEnabled()) {
        increasing = new IncreasingDetector(support);
        increasing.scan(astTree);
        if (IncreasingDetector.nvalueEnabled()) {
          Set<SimpleNode> nvalues = increasing.replaceNValues();
          if (!nvalues.isEmpty()) {
            replaced = new HashSet<>(replaced);
            replaced.addAll(nvalues);
          }
        }
      }

      // a redundant Sequence over sliding-window sums, which --proof does not encode
      // its window rows are still posted, but marked implied: local search evaluates the sequence
      Set<SimpleNode> impliedRows = Set.of();
      if (SequenceDetector.enabled() && options.proof() == null && !pureClique) {
        SequenceDetector sequences = new SequenceDetector(support);
        sequences.detect(astTree);
        impliedRows = sequences.impliedRows();
      }

      // before any constraint propagates: bounds propagation creeps round a negative cycle
      if (DifferenceBoundsDetector.enabled() && support.options.proof() == null) {
        new DifferenceBoundsDetector(support).detect(astTree);
      }

      // half-reified sums at their least value become implications on their terms, before the
      // sums are factored; --proof encodes the rows as given
      Set<SimpleNode> zeroSumNodes = Set.of();
      if (ZeroSumDetector.enabled() && options.proof() == null) {
        ZeroSumDetector zeroSums =
            new ZeroSumDetector(
                support, cf, replaced, keptVariables(astTree), solveItemVariables(astTree));
        zeroSums.detect(astTree);
        if (!zeroSums.replaced().isEmpty()) {
          zeroSumNodes = zeroSums.replaced();
          replaced = new HashSet<>(replaced);
          replaced.addAll(zeroSums.replaced());
          dictionary.removeFromDefaultSearch(zeroSums.unconstrained());
          dictionary.unusedVariables.addAll(zeroSums.unconstrained());
          if (!zeroSums.outputSums().isEmpty()) {
            dictionary.zeroSums = zeroSums.outputSums();
          }
        }
      }

      // a sum of conjunctions over all pairs of two sets of Booleans as the product of their
      // counts;
      // --proof encodes the rows as given
      if (ProductOfSumsDetector.enabled() && options.proof() == null) {
        ProductOfSumsDetector productOfSums = new ProductOfSumsDetector(support, replaced);
        Set<SimpleNode> conjunctions = productOfSums.detect(astTree);
        if (!conjunctions.isEmpty()) {
          replaced = new HashSet<>(replaced);
          replaced.addAll(conjunctions);
          dictionary.removeFromDefaultSearch(productOfSums.removed());
          dictionary.unusedVariables.addAll(productOfSums.removed());
        }
      }

      // common sub-sums of linear constraints become variables, not of the rows zero-sum detection
      // took out; --proof encodes the rows as given
      if (LinearOverlapDetector.enabled() && options.proof() == null) {
        new LinearOverlapDetector(support, zeroSumNodes).detect(astTree);
      }

      // the unary and binary cost functions the objective sums, for the cost network bound that
      // Solve imposes once the objective is known; it reads the model as it is
      if (CostNetworkDetector.enabled() && options.proof() == null) {
        CostNetworkDetector costNetwork = new CostNetworkDetector(support);
        costNetwork.collect(astTree);
        dictionary.costNetwork = costNetwork;
      }

      // controls of half-reified constraints that only clauses want true are replaced by literals
      EnforcementInliner inliner = null;
      if (EnforcementInliner.enabled() && options.proof() == null && !manySolutions) {
        inliner = new EnforcementInliner(support, replaced, keptVariables(astTree));
        inliner.detect(astTree, cf);
        if (!inliner.replaced().isEmpty()) {
          replaced = new HashSet<>(replaced);
          replaced.addAll(inliner.replaced());
        }
      }

      if (!"false".equals(AlldiffChannels.rule())) {
        support.alldiffChannels = AlldiffChannels.collect(support, astTree);
        support.alldiffChannels.addAll(tabled);
      }

      int n = astTree.jjtGetNumChildren();

      for (int i = 0; i < n; i++) {
        SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
        // go for ConstraintItems
        if (node.getId() == JJTCONSTRAINTITEMS) {

          int k = node.jjtGetNumChildren();
          for (int j = 0; j < k; j++) {
            if (support.options.timeOutPassed()) {
              throw new ModelTimeOut();
            }
            SimpleNode snode = (SimpleNode) node.jjtGetChild(j);
            if (!replaced.contains(snode.jjtGetChild(0))) {
              Support.ControlSubstitution control =
                  support.controlSubstitution((SimpleNode) snode.jjtGetChild(0));
              if (control == null) {
                generateConstraint(snode, impliedRows.contains(snode.jjtGetChild(0)));
              } else {
                support.beginControlSubstitution(control);
                try {
                  generateConstraint(snode, impliedRows.contains(snode.jjtGetChild(0)));
                } finally {
                  support.endControlSubstitution();
                }
              }
            }
          }
        }
      }

      if (inliner != null && !inliner.eliminated().isEmpty()) {
        Set<Var> free = inliner.unconstrained();
        dictionary.removeFromDefaultSearch(free);
        dictionary.unusedVariables.addAll(free);
      }

      support.releaseLinearRewrites();
      support.reportAlldiffChannels();
      cf.poseCounts();
      cf.poseDiffnProjections();

      // the constraints the detectors below add are redundant: local search does not evaluate them
      store.imposingImplied(true);
      // its cost constraints are redundant, with bounds a proof does not derive
      if (CircuitCostDetector.enabled() && options.proof() == null) {
        new CircuitCostDetector(support).detect(astTree);
      }

      // a relaxed decision diagram over a circuit whose arcs carry times
      if (SequenceMddDetector.enabled() && options.proof() == null) {
        new SequenceMddDetector(support).detect(astTree);
      }

      // a redundant Routes over 0/1 arcs, whose rules a proof does not derive
      if (RoutesDetector.enabled() && options.proof() == null) {
        new RoutesDetector(support).detect(astTree);
        // and over the successors of a giant tour, with the rows that tie its arcs to the costs
        if (GiantTourDetector.enabled()) {
          new GiantTourDetector(support).detect(astTree);
        }
      } else if (options.freeSearch()
          && !"0".equals(options.freeConfig("lns-routes", "1"))
          && !"0".equals(options.freeConfig("lns", "1"))) {
        // the routes only guide the neighbourhoods of LNS; Solve passes them on
        new RoutesDetector(support, false).detect(astTree);
      }

      if ((DisjunctiveCliqueDetector.enabled() || DisjunctiveCliqueDetector.inferredEnabled())
          && options.proof() == null) {
        // the unary resources it adds explain by rules a proof's unit propagation does not reach
        new DisjunctiveCliqueDetector(support).detect(astTree);
      }

      if (DifferenceCyclesDetector.enabled() && options.proof() == null) {
        // fails on a negative cycle of the difference constraints that hold, with the cycle as
        // reason
        new DifferenceCyclesDetector(support).detect(astTree);
      }

      // energy precedence when enabled, and the reservoirs, which are not redundant
      store.imposingImplied(false);
      new PrecedenceDetector(support).detect(astTree);
      store.imposingImplied(true);
      // the weighted completion bound it adds is redundant, and --proof does not encode it
      if (WeightedCompletionDetector.enabled() && options.proof() == null) {
        new WeightedCompletionDetector(support).detect(astTree);
      }

      // the unary resource of a chain of tasks over permuted resources (the job view of an open
      // shop), redundant; --proof does not encode it
      if (PermutedTasksDetector.enabled() && options.proof() == null) {
        new PermutedTasksDetector(support).detect(astTree);
      }

      if (CardinalityDetector.enabled()) {
        new CardinalityDetector(support).detect(astTree);
      }

      // the bound of the terms of a sum of conjunctions that wait for one variable, redundant;
      // --proof does not encode it
      if (ConjunctionSumDetector.enabled() && options.proof() == null) {
        new ConjunctionSumDetector(support).detect(astTree);
      }

      // the coloring bound of a maximized sum of 0/1 variables with pairwise conflicts (maximum
      // clique), redundant; --proof does not encode it
      if (MaxCliqueDetector.enabled() && options.proof() == null) {
        new MaxCliqueDetector(support).detect(astTree);
      }

      // each variable whose values are all counted at least twice equals one of its few partners
      if (CountPartnersDetector.enabled() && options.proof() == null) {
        new CountPartnersDetector(support).detect(astTree);
      }

      // the aggregated flow of a regular constraint over the residue classes its cardinality
      // constraints count, redundant; --proof does not encode it
      if (RegularFlowDetector.enabled() && options.proof() == null) {
        new RegularFlowDetector(support).detect(astTree);
      }

      // the least number of bins of each item whose pairs must share a bin (SONET rings),
      // redundant; --proof does not encode it
      if (PairCoverDetector.enabled() && options.proof() == null) {
        new PairCoverDetector(support).detect(astTree);
      }

      // the pigeonhole bound on the equal pairs of variables whose pairs all have equality
      // indicators, redundant; --proof does not encode it
      if (AgreementCountDetector.enabled() && options.proof() == null) {
        AgreementCountDetector agreements = new AgreementCountDetector(support);
        agreements.detect(astTree);
        if (agreements.infeasible()) {
          throw Store.failException;
        }
      }

      // the LYM inequality of pairwise incomparable vectors (Sperner's theorem), redundant;
      // --proof does not encode it
      if (AntichainDetector.enabled() && options.proof() == null) {
        AntichainDetector antichains = new AntichainDetector(support);
        antichains.detect(astTree);
        antichains.failIfInfeasible();
      }

      if (increasing != null && IncreasingDetector.sumEnabled()) {
        increasing.postSums();
      }

      Set<ASTConstElem> balanced = Set.of();
      if (BalanceDetector.enabled()) {
        BalanceDetector balance = new BalanceDetector(support);
        balance.detect(astTree);
        balanced = balance.handled();
      }

      // the allocations it adds are redundant, and --proof does not encode them
      if (ConvexAllocationDetector.enabled(options.lcg()) && options.proof() == null) {
        new ConvexAllocationDetector(support, balanced).detect(astTree);
      }

      if (TimeIndexedBound.ARC_FLOW) {
        dictionary.loadFunctions = new LoadFunctionDetector(support).detect(astTree);
      }

      // the stocking cost it adds is redundant, and --proof does not encode it
      if (StockingCostDetector.enabled() && options.proof() == null) {
        new StockingCostDetector(support).detect(astTree);
      }

      if (KnapsackDetector.enabled()) {
        new KnapsackDetector(support).detect(astTree);
      }

      // Gauss-Jordan elimination over the parity constraints, redundant; --proof does not encode it
      if (XorSystemDetector.enabled() && options.proof() == null) {
        new XorSystemDetector(support).detect(astTree);
      }

      // exact covers of the equalities x_1 + ... + x_k = 1, redundant and opt-in; --proof does not
      // encode them
      if (ExactCoverDetector.enabled() && options.proof() == null) {
        new ExactCoverDetector(support).detect(astTree);
      }

      // flows over 0/1 matrices whose row and column sums are bounded, redundant and opt-in;
      // --proof does not encode them
      if (SymmetricGCCDetector.enabled() && options.proof() == null) {
        new SymmetricGCCDetector(support).detect(astTree);
      }

      // tilings written as tables and an all different, redundant, by default without LCG (the
      // --lcg off thread of -p); --proof does not encode them
      if (TableCoverDetector.enabled(options.lcg()) && options.proof() == null) {
        new TableCoverDetector(support).detect(astTree);
      }
      // the exact cover of a tiling by translation written as an all different of shifted terms,
      // redundant; --proof does not encode it
      if (TranslationTilingDetector.enabled() && options.proof() == null) {
        new TranslationTilingDetector(support).detect(astTree);
      }
      // tilings by arithmetic progressions with ordered starts: a branching for the search, no
      // constraint
      if (ProgressionTilingDetector.enabled()) {
        dictionary.progressionTiling = new ProgressionTilingDetector(support).detect(astTree);
      }
      store.imposingImplied(false);

      // the lattices of the equalities: congruences, and the reformulation of market split
      // systems; --proof derives neither
      if (LinearSystemDetector.enabled() && options.proof() == null) {
        LinearSystemDetector lattice = new LinearSystemDetector(support);
        lattice.detect(astTree, options.lp());
        dictionary.searchFirst(lattice.lattice());
      }

      // earliness and tardiness costs under precedences, redundant; --proof does not encode it
      boolean precedenceCost = PrecedenceCostDetector.enabled(options.freeSearch());
      boolean unaryCost = PrecedenceCostDetector.unaryEnabled(options.freeSearch());
      if ((precedenceCost || unaryCost) && options.proof() == null) {
        support.implied(
            () -> new PrecedenceCostDetector(support, precedenceCost, unaryCost).detect(astTree));
      }

      // spanning trees with limits on the edges of disjoint sets (common bases of two matroids),
      // redundant; --proof does not encode it
      if (ColouredTreeDetector.enabled() && options.proof() == null) {
        support.implied(() -> new ColouredTreeDetector(support).detect(astTree));
      }

      support.detectBinPackingCliques();

      support.poseDelayedConstraints();

      // to be sure that all constraints queues are empty and the
      // model is consistent; it can happen that search will not
      // find out inconsistency if all variables are ground
      if (!store.consistency()) {
        throw Store.failException;
      }
    } catch (FailException e) {
      // a constraint failed as it propagated (a domain the translation emptied has no reason)
      if (dictionary.rootTrail != null && store.recentlyFailedConstraint != null) {
        proveRootFailure(support.options.proof());
      }
      throw e;
    }

    if (LinearRelaxationCheck.enabled() && new LinearRelaxationCheck(support).infeasible(astTree)) {
      throw Store.failException;
    }

    if (!support.probeDiffnKHandles()) {
      throw Store.failException;
    }

    // the forest of the successor arcs along which positions grow, redundant, for the subtour
    // elimination cuts of the linear relaxation; --proof does not encode it
    if (SuccessorForestDetector.enabled() && options.proof() == null) {
      new SuccessorForestDetector(support).detect(astTree);
    }
    dictionary.releaseConstantArrays();
    support.releaseControlSubstitutions();
    support.releaseUnitSums();
    support.releaseChannelMaps();
  }

  // a constraint item, imposed as implied by the others when implied is true
  /** The integer variables named by the solve item: the objective and the search annotations. */
  private static final Set<String> CLAUSE_CONSTRAINTS =
      Set.of(
          "jacop_negative_table_int",
          "bool_clause",
          "array_bool_or",
          "array_bool_and",
          "bool2int",
          "bool_not",
          "bool_eq",
          "bool_le",
          "bool_lt",
          "bool_or",
          "bool_and");

  /* Whether every constraint of the model is a clause or a negative table, which over 0/1
   * variables is a set of clauses. */
  private static boolean clauseModel(SimpleNode astTree) {
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() != JJTCONSTRAINTITEMS) {
        continue;
      }
      for (int j = 0; j < node.jjtGetNumChildren(); j++) {
        SimpleNode item = (SimpleNode) ((SimpleNode) node.jjtGetChild(j)).jjtGetChild(0);
        if (item.getId() != JJTCONSTELEM
            || !CLAUSE_CONSTRAINTS.contains(((ASTConstElem) item).getName())) {
          return false;
        }
      }
    }
    return true;
  }

  private Set<IntVar> solveItemVariables(SimpleNode astTree) {
    Set<IntVar> vars = Collections.newSetFromMap(new IdentityHashMap<>());
    for (int i = 0; i < astTree.jjtGetNumChildren(); i++) {
      SimpleNode node = (SimpleNode) astTree.jjtGetChild(i);
      if (node.getId() == JJTMODELEND) {
        namedVariables(node, vars);
      }
    }
    return vars;
  }

  /** The variables of the solve item and the output variables, with the Booleans of aliases. */
  private Set<IntVar> keptVariables(SimpleNode astTree) {
    Set<IntVar> vars = solveItemVariables(astTree);
    for (Var v : dictionary.outputVariables) {
      if (v instanceof IntVar x) {
        vars.add(x);
      }
    }
    for (Var[] a : dictionary.outputArrays()) {
      for (Var v : a) {
        if (v instanceof IntVar x) {
          vars.add(x);
        }
      }
    }
    for (IntVar v : new ArrayList<>(vars)) {
      vars.add(dictionary.getAlias(v));
    }
    // the equality posted for var x = y stays on those variables
    dictionary.addDeclaredEqualities(vars);
    return vars;
  }

  private void namedVariables(Node node, Set<IntVar> vars) {
    String ident =
        switch (node) {
          case ASTScalarFlatExpr e -> e.getIdent();
          case ASTVariableExpr e -> e.getIdent();
          case ASTSolveExpr e -> e.getIdent();
          case ASTAnnExpr e -> e.getIdent();
          default -> null;
        };
    if (ident != null) {
      IntVar v = dictionary.variableTable.get(ident);
      if (v != null) {
        vars.add(v);
      }
      IntVar[] a = dictionary.variableArrayTable.get(ident);
      if (a != null) {
        Collections.addAll(vars, a);
      }
    }
    for (int i = 0; i < node.jjtGetNumChildren(); i++) {
      namedVariables(node.jjtGetChild(i), vars);
    }
  }

  private void generateConstraint(SimpleNode constraintWithAnnotations, boolean implied)
      throws Throwable {
    store.imposingImplied(implied);
    try {
      generateConstraint(constraintWithAnnotations);
    } finally {
      store.imposingImplied(false);
    }
  }

  void generateConstraint(SimpleNode constraintWithAnnotations) throws Throwable {

    // default consistency - bounds
    support.boundsConsistency = true;
    support.domainConsistency = false;
    support.definedVar = null;

    int numberChildren = constraintWithAnnotations.jjtGetNumChildren();
    if (numberChildren > 1) {
      support.parseAnnotations(constraintWithAnnotations);
    }

    SimpleNode node = (SimpleNode) constraintWithAnnotations.jjtGetChild(0);

    // Generate constraint
    if (node.getId() == JJTCONSTELEM) {

      p = ((ASTConstElem) node).getName();

      try {

        java.lang.reflect.Method method = generators.get(p);
        if (method == null) {
          method = cf.getClass().getMethod(p, SimpleNode.class);
          generators.put(p, method);
        }
        method.invoke(cf, node);

      } catch (NoSuchMethodException _) {
        throw new IllegalArgumentException(
            "JaCoP flatzinc back-end: constraint " + p + " is not supported.");
      } catch (IllegalAccessException e) {
        FzConsole.println(e);
      } catch (java.lang.reflect.InvocationTargetException e) {
        Throwable cause = e.getCause();
        if (cause instanceof FailException) {
          // the comment explains an unsatisfiable model; other errors go to stderr
          FzConsole.println("%% problem detected for " + p);
        } else {
          FzConsole.printlnErr("%% problem detected for " + p);
        }
        throw cause;
      }
    }
  }

  void generateAlias(SimpleNode constraintWithAnnotations) {

    SimpleNode node = (SimpleNode) constraintWithAnnotations.jjtGetChild(0);

    if (node.getId() != JJTCONSTELEM) {
      return;
    }

    p = ((ASTConstElem) node).getName();
    noConstraints++;

    if (isBoolClauseConstraint(p)) {
      boolClauses++;
      return;
    }
    if (p.startsWith("bool2int") || p.startsWith("int2bool")) {
      handleBool2IntAlias(node);
      return;
    }
    if (p.startsWith("int_eq_reif")) {
      handleIntEqReif(node);
      return;
    }
    if (p.startsWith("int_eq_imp")) {
      handleIntEqImp(node);
    }
  }

  private boolean isBoolClauseConstraint(String name) {
    return name.startsWith("bool_clause")
        || name.startsWith("bool_not")
        || name.startsWith("bool_eq")
        || name.startsWith("array_bool_or");
  }

  private void handleBool2IntAlias(SimpleNode node) {
    bool2Int++;
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    IntVar v1 = support.getVariable(p1);
    IntVar v2 = support.getVariable(p2);
    if (v1 == v2 || dictionary.isAliasTarget(v2) || dictionary.isDeclaredEqual(v2)) {
      // the integer variable is already the alias of a Boolean, or a declaration made it equal to
      // another variable on its own object; gen_bool2int posts the equality
      return;
    }
    dictionary.addAlias(v1, v2);
    // v1 stands for v2 from now on, so it takes the declared domain of v2 (var 2..20: i)
    v1.domain.in(store.level, v1, v2.domain);
    v2.domain.in(store.level, v2, v1.domain);
    if (debug) {
      FzConsole.println("% Alias: " + v1 + " == " + v2);
    }
  }

  private void handleIntEqReif(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);
    IntVar b = support.getVariable(p3);
    IntVarAndValue xv = extractIntVarAndValue(p1, p2);
    if (xv == null) {
      return;
    }
    if (binaryEqAlias && xv.v == 1 && binaryAlias(xv.x, b)) {
      return;
    }
    support.addReified(xv.x, xv.v, b);
  }

  /*
   * Whether int_eq_reif(x, 1, b) of a 0..1 variable x, which states x = b, makes x an alias of b,
   * as bool2int(b, x) does. MiniZinc writes a Boolean grid used in sums as 0..1 integers channelled
   * to Booleans this way (ma-path-finding: 141,000 of them), and each kept pair was two variables,
   * their atoms and an equality. Off by default; the system property
   * org.jacop.fz.binaryEqAlias=true turns it on.
   */
  private final boolean binaryEqAlias = Boolean.getBoolean("org.jacop.fz.binaryEqAlias");

  private boolean binaryAlias(IntVar x, IntVar b) {
    if (!(b instanceof BooleanVar)
        || x instanceof BooleanVar
        || x.min() < 0
        || x.max() > 1
        || dictionary.aliasTable.containsKey(x)
        || dictionary.isAliasTarget(x)
        || dictionary.isDeclaredEqual(x)
        || dictionary.aliasTable.containsKey(b)) {
      return false;
    }
    dictionary.addAlias(b, x);
    dictionary.binaryEqAliases.add(x);
    if (x.singleton() || b.singleton()) {
      x.domain.in(store.level, x, b.domain);
      b.domain.in(store.level, b, x.domain);
    }
    if (debug) {
      FzConsole.println("% Alias: " + b + " == " + x);
    }
    return true;
  }

  private void handleIntEqImp(SimpleNode node) {
    ASTScalarFlatExpr p1 = (ASTScalarFlatExpr) node.jjtGetChild(0);
    ASTScalarFlatExpr p2 = (ASTScalarFlatExpr) node.jjtGetChild(1);
    ASTScalarFlatExpr p3 = (ASTScalarFlatExpr) node.jjtGetChild(2);
    IntVar b = support.getVariable(p3);
    IntVarAndValue xv = extractIntVarAndValue(p1, p2);
    if (xv != null) {
      support.addImplied(xv.x, xv.v, b);
    }
  }

  /**
   * Extracts an IntVar and integer value from two scalar expressions. One must be a variable and
   * the other an integer constant.
   *
   * @param p1 first expression
   * @param p2 second expression
   * @return IntVarAndValue if extraction successful, null otherwise
   */
  private IntVarAndValue extractIntVarAndValue(ASTScalarFlatExpr p1, ASTScalarFlatExpr p2) {
    IntVar x;
    int v;

    if (p2.getType() == 0) { // second argument integer
      x = support.getVariable(p1);
      v = support.getInt(p2);
    } else if (p1.getType() == 0) { // first argument integer
      x = support.getVariable(p2);
      v = support.getInt(p1);
    } else { // no integers
      return null;
    }

    return new IntVarAndValue(x, v);
  }

  /** Helper record for IntVar and integer value pair. */
  private record IntVarAndValue(IntVar x, int v) {}

  private boolean hasFloatVariables() {
    for (int i = 0; i < store.size(); i++) {
      if (store.vars[i] instanceof FloatVar) {
        return true;
      }
    }
    return false;
  }

  // whether the model is solved by free search: -f, or no search annotation (as Solve decides)
  private static boolean freeSearchModel(Node node, Options options) {
    if (options.freeSearch()) {
      return true;
    }
    if (!options.freeSearchWithoutAnnotation() || options.complementarySearch()) {
      return false;
    }
    for (int i = node.jjtGetNumChildren() - 1; i >= 0; i--) {
      Node child = node.jjtGetChild(i);
      if (child instanceof ASTSolveItem item) {
        return item.jjtGetNumChildren() == 1;
      }
      if (child instanceof ASTModelEnd && freeSearchModel(child, options)) {
        return true;
      }
    }
    return false;
  }

  /** Whether the solve item, a child of the model's end, is "solve satisfy". */
  private static boolean satisfaction(Node node) {
    for (int i = node.jjtGetNumChildren() - 1; i >= 0; i--) {
      Node child = node.jjtGetChild(i);
      if (child instanceof ASTSolveItem item) {
        return item.jjtGetChild(item.jjtGetNumChildren() - 1) instanceof ASTSolveKind kind
            && "satisfy".equals(kind.getKind());
      }
      if (child instanceof ASTModelEnd && satisfaction(child)) {
        return true;
      }
    }
    return false;
  }

  // --proof: the model fails at the root, which the proof derives
  private void proveRootFailure(String prefix) {
    try (OutputStream model = new FileOutputStream(prefix + ".opb");
        OutputStream proof = new FileOutputStream(prefix + ".pbp")) {
      LcgSolver.proveRootFailure(store, dictionary.rootTrail, model, proof);
      dictionary.rootTrail = null;
      dictionary.rootFailureProved = true;
    } catch (IOException e) {
      throw new UncheckedIOException(e);
    }
  }
}
