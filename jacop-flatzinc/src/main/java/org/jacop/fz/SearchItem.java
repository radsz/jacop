/*
 * SearchItem.java
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.core.FloatVar;
import org.jacop.floats.search.LargestDomainFloat;
import org.jacop.floats.search.LargestMaxFloat;
import org.jacop.floats.search.MaxRegretFloat;
import org.jacop.floats.search.SmallestDomainFloat;
import org.jacop.floats.search.SmallestMinFloat;
import org.jacop.floats.search.SplitRandomSelectFloat;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.search.ActivityMax;
import org.jacop.search.ActivityMaxDeg;
import org.jacop.search.ActivityMin;
import org.jacop.search.ActivityMinDeg;
import org.jacop.search.AfcMax;
import org.jacop.search.AfcMaxDeg;
import org.jacop.search.AfcMin;
import org.jacop.search.AfcMinDeg;
import org.jacop.search.ComparatorVariable;
import org.jacop.search.Indomain;
import org.jacop.search.IndomainDefaultValue;
import org.jacop.search.IndomainMax;
import org.jacop.search.IndomainMedian;
import org.jacop.search.IndomainMiddle;
import org.jacop.search.IndomainMin;
import org.jacop.search.IndomainRandom;
import org.jacop.search.InputOrderSelect;
import org.jacop.search.LargestDomain;
import org.jacop.search.LargestMax;
import org.jacop.search.MaxRegret;
import org.jacop.search.MostConstrainedStatic;
import org.jacop.search.RandomSelect;
import org.jacop.search.RandomVar;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import org.jacop.search.SmallestMax;
import org.jacop.search.SmallestMin;
import org.jacop.search.SplitRandomSelect;
import org.jacop.search.SplitSelect;
import org.jacop.search.WeightedDegree;
import org.jacop.search.restart.Calculator;
import org.jacop.search.restart.ConstantCalculator;
import org.jacop.search.restart.GeometricCalculator;
import org.jacop.search.restart.LinearCalculator;
import org.jacop.search.restart.LubyCalculator;
import org.jacop.set.core.SetVar;
import org.jacop.set.search.IndomainSetMax;
import org.jacop.set.search.IndomainSetMin;
import org.jacop.set.search.IndomainSetRandom;
import org.jacop.set.search.MaxCardDiff;
import org.jacop.set.search.MaxLubCard;
import org.jacop.set.search.MinCardDiff;
import org.jacop.set.search.MinGlbCard;

/**
 * The part of the parser responsible for parsing search part of the flatzinc specification.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class SearchItem<T extends Var> implements ParserTreeConstants {

  final Tables dictionary;
  final Store store;

  final ArrayList<SearchItem<T>> searchSeq = new ArrayList<>();
  Var[] searchVariables;
  String searchType;
  String explore = COMPLETE;
  String indomain;
  String varSelectionHeuristic;

  boolean floatSearch;
  double precision = 0.0; // for float_search

  int ldsValue;
  int creditValue;
  int bbsValue;

  ComparatorsVar<T> selVars;
  ComparatorVariable<IntVar> tieBreakingInt;
  ComparatorVariable<SetVar> tieBreakingSet;
  ComparatorVariable<FloatVar> tieBreakingFloat;

  Calculator restartCalculator;

  boolean prioritySearch;

  Map<IntVar, Integer> preferedValues;

  // Exploration and search type literals
  private static final String COMPLETE = "complete";
  private static final String SEQ_SEARCH = "seq_search";
  private static final String WARM_START = "warm_start";
  private static final String INPUT_ORDER = "input_order";
  private static final String INDOMAIN_MIN = "indomain_min";
  private static final String INDOMAIN_MAX = "indomain_max";
  // AST annotation IDs
  private static final String ANN_VECTOR = "$vector";
  private static final String ANN_EXPR = "$expr";
  // Variable selection heuristics
  private static final String RANDOM = "random";
  private static final String FIRST_FAIL = "first_fail";
  private static final String ANTI_FIRST_FAIL = "anti_first_fail";
  private static final String MOST_CONSTRAINED = "most_constrained";
  private static final String OCCURRENCE = "occurrence";
  private static final String SMALLEST = "smallest";
  private static final String LARGEST = "largest";
  private static final String IMPACT = "impact";
  private static final String DOM_W_DEG = "dom_w_deg";
  private static final String AFC_MAX = "afc_max";
  private static final String AFC_MIN = "afc_min";
  private static final String AFC_MAX_DEG = "afc_max_deg";
  private static final String AFC_MIN_DEG = "afc_min_deg";
  private static final String ACTIVITY_MAX = "activity_max";
  private static final String ACTIVITY_MIN = "activity_min";
  private static final String ACTIVITY_MAX_DEG = "activity_max_deg";
  private static final String ACTIVITY_MIN_DEG = "activity_min_deg";
  // Warning message fragments
  private static final String WARNING_EXPLORATION_USE_COMPLETE =
      "Warning: not recognized search exploration type; use \"complete\"";
  private static final String WARNING_VAR_HEURISTIC_PREFIX =
      "Warning: Not implemented variable selection heuristic \"";
  private static final String WARNING_VAR_HEURISTIC_SUFFIX = "\"; used input_order";
  private static final String WARNING_INDOMAIN_USED_MIN =
      "Warning: Not implemented indomain method \"";

  // relax and reconstruct
  IntVar[] relaxAndReconstructVariables;
  int probability;

  /**
   * It constructs search part parsing object based on dictionaries provided as well as store object
   * within which the search will take place.
   *
   * @param store the finite domain store within which the search will take place.
   * @param table the holder of all the objects present in the flatzinc file.
   */
  public SearchItem(Store store, Tables table) {
    this.dictionary = table;
    this.store = store;
  }

  /**
   * Parses search parameters from the parse tree node.
   *
   * @param node the parse tree node containing search annotations
   * @param n the index of the child node to process
   */
  void searchParameters(SimpleNode node, int n) {

    ASTAnnotation ann = (ASTAnnotation) node.jjtGetChild(n);
    searchType = ann.getAnnId();

    switch (searchType) {
      case "int_search", "bool_search" -> {
        SimpleNode expr1 = (SimpleNode) ann.jjtGetChild(0);
        searchVariables = getVarArray(expr1);

        ASTAnnotation expr2 = (ASTAnnotation) ann.jjtGetChild(1);
        varSelectionHeuristic = getVarSelectHeuristic(expr2);

        ASTAnnExpr expr3 = (ASTAnnExpr) ann.jjtGetChild(2).jjtGetChild(0);
        indomain = ((ASTScalarFlatExpr) expr3.jjtGetChild(0)).getIdent();

        ASTAnnotation expr4 = (ASTAnnotation) ann.jjtGetChild(3);
        explorationType(expr4);
      }
      case "set_search" -> {
        SimpleNode expr1 = (SimpleNode) ann.jjtGetChild(0);
        searchVariables = getSetVarArray(expr1);

        ASTAnnotation expr2 = (ASTAnnotation) ann.jjtGetChild(1);
        varSelectionHeuristic = getVarSelectHeuristic(expr2);

        ASTAnnExpr expr3 = (ASTAnnExpr) ann.jjtGetChild(2).jjtGetChild(0);
        indomain = ((ASTScalarFlatExpr) expr3.jjtGetChild(0)).getIdent();

        ASTAnnotation expr4 = (ASTAnnotation) ann.jjtGetChild(3);
        explorationType(expr4);
      }
      case "float_search" -> {
        floatSearch = true;

        SimpleNode expr1 = (SimpleNode) ann.jjtGetChild(0);
        searchVariables = getFloatVarArray(expr1);

        ASTAnnotation expr2 = (ASTAnnotation) ann.jjtGetChild(2);
        varSelectionHeuristic = getVarSelectHeuristic(expr2);

        ASTAnnExpr expr3 = (ASTAnnExpr) ann.jjtGetChild(3).jjtGetChild(0);
        indomain = ((ASTScalarFlatExpr) expr3.jjtGetChild(0)).getIdent();

        ASTAnnotation expr4 = (ASTAnnotation) ann.jjtGetChild(4);
        explorationType(expr4);

        ASTAnnExpr expr5 = (ASTAnnExpr) ann.jjtGetChild(1).jjtGetChild(0);
        precision = ((ASTScalarFlatExpr) expr5.jjtGetChild(0)).getFloat();
      }
      case SEQ_SEARCH -> {
        SimpleNode body = (SimpleNode) ann.jjtGetChild(0);
        searchType = SEQ_SEARCH;

        makeVectorOfSearches(body);
      }
      case WARM_START -> handleWarmStart(ann);
      case "priority_search" -> {
        prioritySearch = true;

        SimpleNode expr1 = (SimpleNode) ann.jjtGetChild(0);
        searchVariables = getVarArray(expr1);

        SimpleNode searches = (SimpleNode) ann.jjtGetChild(1);
        makeVectorOfSearches(searches);

        ASTAnnotation expr2 = (ASTAnnotation) ann.jjtGetChild(2);
        varSelectionHeuristic = getVarSelectHeuristic(expr2);

        ASTAnnotation expr3 = (ASTAnnotation) ann.jjtGetChild(3);
        explorationType(expr3);
        if (!COMPLETE.equals(explore)) {
          System.err.println(WARNING_EXPLORATION_USE_COMPLETE);
        }
      }
      case "restart_none" -> {}
      case "restart_constant" -> handleRestartConstant(ann);
      case "restart_linear" -> handleRestartLinear(ann);
      case "restart_luby" -> handleRestartLuby(ann);
      case "restart_geometric" -> handleRestartGeometric(ann);
      case "relax_and_reconstruct" -> {
        SimpleNode expr1 = (SimpleNode) ann.jjtGetChild(0);
        relaxAndReconstructVariables = getVarArray(expr1);
        ASTAnnExpr expr2 = (ASTAnnExpr) ann.jjtGetChild(1).jjtGetChild(0);
        probability = ((ASTScalarFlatExpr) expr2.jjtGetChild(0)).getInt();
      }
      case null, default -> IO.println("% Warning: Ignored search annotation " + searchType);
    }

    // compilation aborted.");
  }

  private void handleWarmStart(ASTAnnotation ann) {
    SimpleNode expr1 = (SimpleNode) ann.jjtGetChild(0);
    searchVariables = getVarArray(expr1);
    SimpleNode expr2 = (SimpleNode) ann.jjtGetChild(1);
    int[] values;
    try {
      values = getIntArray(expr2);
    } catch (IllegalArgumentException _) {
      throw new IllegalArgumentException(
          "%Not supported types of values in warm_start; compilation aborted");
    }
    if (searchVariables == null || values == null) {
      throw new IllegalArgumentException(
          "Not supported variable and/or value type in warm_start; compilation aborted.");
    }
    preferedValues = new HashMap<>();
    int max = 0;
    int min = 0;
    for (int i = 0; i < values.length; i++) {
      IntVar v = (IntVar) searchVariables[i];
      int val = values[i];
      if (v.domain.contains(val)) {
        if (preferedValues.get(v) != null && preferedValues.get(v) != val) {
          IO.println(
              "% Warning: Double defintion on warm_start for variable "
                  + v
                  + "("
                  + preferedValues.get(v)
                  + ", "
                  + val
                  + "), the first value is used.");
        } else {
          if ((v.max() - val) > (val - v.min())) {
            max++;
          } else {
            min++;
          }
          preferedValues.put(v, val);
        }
      } else {
        IO.println(
            "% Warning: warm_start value " + val + " is not in domain of " + v + "; ignored");
      }
    }
    varSelectionHeuristic = INPUT_ORDER;
    indomain = max > min ? INDOMAIN_MAX : INDOMAIN_MIN;
  }

  private void handleRestartConstant(ASTAnnotation ann) {
    ASTAnnExpr expr = (ASTAnnExpr) ann.jjtGetChild(0).jjtGetChild(0);
    int scale = ((ASTScalarFlatExpr) expr.jjtGetChild(0)).getInt();
    restartCalculator = new ConstantCalculator(scale);
  }

  private void handleRestartLinear(ASTAnnotation ann) {
    ASTAnnExpr expr = (ASTAnnExpr) ann.jjtGetChild(0).jjtGetChild(0);
    int scale = ((ASTScalarFlatExpr) expr.jjtGetChild(0)).getInt();
    restartCalculator = new LinearCalculator(scale);
  }

  private void handleRestartLuby(ASTAnnotation ann) {
    ASTAnnExpr expr = (ASTAnnExpr) ann.jjtGetChild(0).jjtGetChild(0);
    int scale = ((ASTScalarFlatExpr) expr.jjtGetChild(0)).getInt();
    restartCalculator = new LubyCalculator(scale);
  }

  private void handleRestartGeometric(ASTAnnotation ann) {
    ASTAnnExpr expr1 = (ASTAnnExpr) ann.jjtGetChild(0).jjtGetChild(0);
    double base = ((ASTScalarFlatExpr) expr1.jjtGetChild(0)).getFloat();
    ASTAnnExpr expr2 = (ASTAnnExpr) ann.jjtGetChild(1).jjtGetChild(0);
    int scale = ((ASTScalarFlatExpr) expr2.jjtGetChild(0)).getInt();
    restartCalculator = new GeometricCalculator(base, scale);
  }

  /**
   * Creates a vector of search items from a parse tree node.
   *
   * @param body the parse tree node containing the search vector
   */
  void makeVectorOfSearches(SimpleNode body) {

    if (Objects.equals(((ASTAnnotation) body).getAnnId(), ANN_VECTOR)) {

      int count = body.jjtGetNumChildren();

      for (int i = 0; i < count; i++) {
        SearchItem<T> subSearch = new SearchItem<>(store, dictionary);

        ASTAnnotation ann = (ASTAnnotation) body.jjtGetChild(i);
        // priority_search not supported; execution aborted");

        subSearch.searchParameters(body, i);

        if (SEQ_SEARCH.equals(ann.getAnnId())) {
          searchSeq.add(subSearch);
          continue;
        }

        if (subSearch.searchVariables != null && subSearch.searchVariables.length > 0) {
          searchSeq.add(subSearch);
        }
      }
    } else {
      throw new RuntimeException(
          "Error: Non vector definitionion in seq_search; execution aborted");
    }
  }

  /**
   * Determines the exploration type from an annotation node.
   *
   * @param expr4 the annotation node containing exploration type
   */
  void explorationType(ASTAnnotation expr4) {
    switch (expr4.getAnnId()) {
      case ANN_EXPR ->
          explore = ((ASTScalarFlatExpr) expr4.jjtGetChild(0).jjtGetChild(0)).getIdent();
      case "credit" -> handleCreditExploration(expr4);
      case "lds" -> handleLdsExploration(expr4);
      case null, default ->
          throw new RuntimeException(
              "Error: not recognized search exploration type; execution aborted");
    }
  }

  private void handleCreditExploration(ASTAnnotation expr4) {
    explore = "credit";
    parseCreditValue(expr4);
    if (parseBbsValue(expr4)) {
      return;
    }
    explore = COMPLETE;
    System.err.println(WARNING_EXPLORATION_USE_COMPLETE);
  }

  private void parseCreditValue(ASTAnnotation expr4) {
    if (expr4.jjtGetNumChildren() < 2) {
      return;
    }
    if (!ANN_EXPR.equals(((ASTAnnotation) expr4.jjtGetChild(0)).getAnnId())) {
      return;
    }
    ASTAnnExpr cp = (ASTAnnExpr) expr4.jjtGetChild(0).jjtGetChild(0);
    if (cp.jjtGetNumChildren() == 1) {
      creditValue = ((ASTScalarFlatExpr) cp.jjtGetChild(0)).getInt();
    }
  }

  private boolean parseBbsValue(ASTAnnotation expr4) {
    if (expr4.jjtGetNumChildren() < 2) {
      return false;
    }
    ASTAnnotation bbs = (ASTAnnotation) expr4.jjtGetChild(1);
    if (bbs.getId() != JJTANNOTATION || !"bbs".equals(bbs.getAnnId())) {
      return false;
    }
    if (bbs.jjtGetChild(0).jjtGetNumChildren() != 1) {
      return false;
    }
    SimpleNode child = (SimpleNode) bbs.jjtGetChild(0).jjtGetChild(0);
    if (child.getId() != JJTANNEXPR) {
      return false;
    }
    ASTAnnExpr bv = (ASTAnnExpr) child;
    if (bv.jjtGetNumChildren() == 1) {
      bbsValue = ((ASTScalarFlatExpr) bv.jjtGetChild(0)).getInt();
      return true;
    }
    return false;
  }

  private void handleLdsExploration(ASTAnnotation expr4) {
    explore = "lds";
    if (parseLdsValue(expr4)) {
      return;
    }
    explore = COMPLETE;
    System.err.println(WARNING_EXPLORATION_USE_COMPLETE);
  }

  private boolean parseLdsValue(ASTAnnotation expr4) {
    if (expr4.jjtGetNumChildren() != 1) {
      return false;
    }
    if (!ANN_EXPR.equals(((ASTAnnotation) expr4.jjtGetChild(0)).getAnnId())) {
      return false;
    }
    SimpleNode child = (SimpleNode) expr4.jjtGetChild(0).jjtGetChild(0);
    if (child.getId() != JJTANNEXPR) {
      return false;
    }
    ASTAnnExpr ae = (ASTAnnExpr) child;
    if (ae.jjtGetNumChildren() == 1) {
      ldsValue = ((ASTScalarFlatExpr) ae.jjtGetChild(0)).getInt();
      return true;
    }
    return false;
  }

  /**
   * Parses search parameters from multiple annotations.
   *
   * @param node the parse tree node containing multiple search annotations
   * @param n the index parameter (currently unused)
   */
  void searchParametersForSeveralAnnotations(SimpleNode node, int n) {

    int count = node.jjtGetNumChildren();

    for (int i = 0; i < count - 1; i++) {
      SearchItem<T> subSearch = new SearchItem<>(store, dictionary);
      subSearch.searchParameters(node, i);

      if (searchType == null && WARM_START.equals(subSearch.searchType)) {
        searchSeq.addFirst(subSearch);
      } else {
        searchSeq.add(subSearch);
      }
    }

    searchType = SEQ_SEARCH;
  }

  /**
   * Creates a select choice point for warm start search.
   *
   * @return the select choice point for warm start
   */
  SelectChoicePoint<IntVar> getWarmStartSelect() {

    Indomain<IntVar> indom =
        INDOMAIN_MIN.equals(indomain)
            ? new IndomainDefaultValue<>(preferedValues, new IndomainMin<>())
            : new IndomainDefaultValue<>(preferedValues, new IndomainMax<>());
    ArrayList<IntVar> sv = new ArrayList<>();
    for (Var searchVariable : searchVariables) {
      if (preferedValues.containsKey(searchVariable)) {
        sv.add((IntVar) searchVariable);
      }
    }
    IntVar[] searchVars;
    if (sv.isEmpty()) {
      searchVars = new IntVar[1];
      searchVars[0] = dictionary.getConstant(0); // needed for SimpleSelect to not fail
    } else {
      searchVars = sv.toArray(new IntVar[0]);
    }

    ComparatorsVar<IntVar> vs = getVarSelect();
    ComparatorVariable<IntVar> varSel = vs.getVarSel();

    return new SimpleSelect<>(searchVars, varSel, indom);
  }

  /**
   * Creates a select choice point for integer variable search.
   *
   * @return the select choice point for integer variables
   */
  SelectChoicePoint<IntVar> getIntSelect() {

    if (RANDOM.equals(varSelectionHeuristic)) {
      Indomain<IntVar> indom = getIndomain(indomain);
      return new RandomSelect<>(copyToIntVarArray(), indom);
    }

    ComparatorsVar<IntVar> vs = getVarSelect();
    ComparatorVariable<IntVar> varSel = vs.getVarSel();
    ComparatorVariable<IntVar> tieBreaking =
        tieBreakingInt == null ? vs.getTieSel() : tieBreakingInt;
    IntVar[] searchVars = copyToIntVarArray();

    SelectChoicePoint<IntVar> splitSelect =
        getIntSelectForSplitIndomain(searchVars, varSel, tieBreaking);
    if (splitSelect != null) {
      return splitSelect;
    }
    if (INPUT_ORDER.equals(varSelectionHeuristic)) {
      return new InputOrderSelect<>(store, (IntVar[]) searchVariables, getIndomain(indomain));
    }
    Indomain<IntVar> indom = getIndomain(indomain);
    if (tieBreaking == null) {
      return new SimpleSelect<>((IntVar[]) searchVariables, varSel, indom);
    }
    return new SimpleSelect<>((IntVar[]) searchVariables, varSel, tieBreaking, indom);
  }

  private IntVar[] copyToIntVarArray() {
    IntVar[] searchVars = new IntVar[searchVariables.length];
    for (int i = 0; i < searchVariables.length; i++) {
      searchVars[i] = (IntVar) searchVariables[i];
    }
    return searchVars;
  }

  private SelectChoicePoint<IntVar> getIntSelectForSplitIndomain(
      IntVar[] searchVars,
      ComparatorVariable<IntVar> varSel,
      ComparatorVariable<IntVar> tieBreaking) {
    if ("indomain_split".equals(indomain)) {
      return tieBreaking == null
          ? new SplitSelect<>(searchVars, varSel, new IndomainMiddle<>())
          : new SplitSelect<>(searchVars, varSel, tieBreaking, new IndomainMiddle<>());
    }
    if ("indomain_split_random".equals(indomain)) {
      return tieBreaking == null
          ? new SplitRandomSelect<>(searchVars, varSel, new IndomainMiddle<>())
          : new SplitRandomSelect<>(searchVars, varSel, tieBreaking, new IndomainMiddle<>());
    }
    if ("indomain_reverse_split".equals(indomain)) {
      SplitSelect<IntVar> sel =
          tieBreaking == null
              ? new SplitSelect<>(searchVars, varSel, new IndomainMiddle<>())
              : new SplitSelect<>(searchVars, varSel, tieBreaking, new IndomainMiddle<>());
      sel.leftFirst = false;
      return sel;
    }
    if ("outdomain_max".equals(indomain)) {
      return tieBreaking == null
          ? new SplitSelect<>(searchVars, varSel, new IndomainMax<>())
          : new SplitSelect<>(searchVars, varSel, tieBreaking, new IndomainMax<>());
    }
    if ("outdomain_min".equals(indomain)) {
      SplitSelect<IntVar> sel =
          tieBreaking == null
              ? new SplitSelect<>(searchVars, varSel, new IndomainMin<>())
              : new SplitSelect<>(searchVars, varSel, tieBreaking, new IndomainMin<>());
      sel.leftFirst = false;
      return sel;
    }
    return null;
  }

  /**
   * Creates a select choice point for float variable search.
   *
   * @return the select choice point for float variables
   */
  SelectChoicePoint<FloatVar> getFloatSelect() {

    ComparatorsVar<FloatVar> vs = getFloatVarSelect();
    ComparatorVariable<FloatVar> varSel = vs.getVarSel();
    ComparatorVariable<FloatVar> tieBreaking =
        tieBreakingFloat == null ? vs.getTieSel() : tieBreakingFloat;
    FloatVar[] searchVars = copyToFloatVarArray();

    return createFloatSelectForIndomain(searchVars, varSel, tieBreaking);
  }

  private FloatVar[] copyToFloatVarArray() {
    FloatVar[] searchVars = new FloatVar[searchVariables.length];
    for (int i = 0; i < searchVariables.length; i++) {
      searchVars[i] = (FloatVar) searchVariables[i];
    }
    return searchVars;
  }

  private SelectChoicePoint<FloatVar> createFloatSelectForIndomain(
      FloatVar[] searchVars,
      ComparatorVariable<FloatVar> varSel,
      ComparatorVariable<FloatVar> tieBreaking) {
    return switch (indomain) {
      case "indomain_split" -> createSplitSelectFloat(searchVars, varSel, tieBreaking);
      case "indomain_split_random" -> createSplitRandomSelectFloat(searchVars, varSel, tieBreaking);
      case "indomain_reverse_split" ->
          createReverseSplitSelectFloat(searchVars, varSel, tieBreaking);
      case null, default ->
          throw new IllegalArgumentException(
              "Wrong parameters for float_search. Only indomain_split, indomain_reverse_split or indomain_split_random are allowed.");
    };
  }

  private SelectChoicePoint<FloatVar> createSplitSelectFloat(
      FloatVar[] searchVars,
      ComparatorVariable<FloatVar> varSel,
      ComparatorVariable<FloatVar> tieBreaking) {
    return tieBreaking == null
        ? new SplitSelectFloat<>(store, searchVars, varSel)
        : new SplitSelectFloat<>(store, searchVars, varSel, tieBreaking);
  }

  private SelectChoicePoint<FloatVar> createSplitRandomSelectFloat(
      FloatVar[] searchVars,
      ComparatorVariable<FloatVar> varSel,
      ComparatorVariable<FloatVar> tieBreaking) {
    return tieBreaking == null
        ? new SplitRandomSelectFloat<>(store, searchVars, varSel)
        : new SplitRandomSelectFloat<>(store, searchVars, varSel, tieBreaking);
  }

  private SelectChoicePoint<FloatVar> createReverseSplitSelectFloat(
      FloatVar[] searchVars,
      ComparatorVariable<FloatVar> varSel,
      ComparatorVariable<FloatVar> tieBreaking) {
    SplitSelectFloat<FloatVar> sel =
        tieBreaking == null
            ? new SplitSelectFloat<>(store, searchVars, varSel)
            : new SplitSelectFloat<>(store, searchVars, varSel, tieBreaking);
    sel.leftFirst = false;
    return sel;
  }

  /**
   * Creates a select choice point for set variable search.
   *
   * @return the select choice point for set variables
   */
  SelectChoicePoint<SetVar> getSetSelect() {

    ComparatorsVar<SetVar> vs = getSetVarSelect();
    ComparatorVariable<SetVar> varSel = vs.getVarSel();
    ComparatorVariable<SetVar> tieBreaking =
        tieBreakingSet == null ? vs.getTieSel() : tieBreakingSet;

    Indomain<SetVar> indom = getIndomain4Set(indomain);
    SetVar[] searchVars = new SetVar[searchVariables.length];
    for (int i = 0; i < searchVariables.length; i++) {
      searchVars[i] = (SetVar) searchVariables[i];
    }

    if (tieBreaking == null) {
      return new SimpleSelect<>(searchVars, varSel, indom);
    } else {
      return new SimpleSelect<>(searchVars, varSel, tieBreaking, indom);
    }
  }

  /**
   * Returns the indomain heuristic for set variables.
   *
   * @param indomain the name of the indomain heuristic
   * @return the indomain heuristic for set variables
   */
  Indomain<SetVar> getIndomain4Set(String indomain) {

    if (indomain == null) {
      return new IndomainSetMin<>();
    } else {
      return switch (indomain) {
        case INDOMAIN_MIN -> new IndomainSetMin<>();
        case INDOMAIN_MAX -> new IndomainSetMax<>();
        case "indomain_random" -> new IndomainSetRandom<>();
        default -> {
          System.err.println(WARNING_INDOMAIN_USED_MIN + indomain + "\"; used indomain_min");
          yield new IndomainSetMin<>();
        }
      };
    }
  }

  /**
   * Returns the indomain heuristic for integer variables.
   *
   * @param indomain the name of the indomain heuristic
   * @return the indomain heuristic for integer variables
   */
  Indomain<IntVar> getIndomain(String indomain) {
    if (indomain == null) {
      return new IndomainMin<>();
    } else {
      return switch (indomain) {
        case INDOMAIN_MIN -> new IndomainMin<>();
        case INDOMAIN_MAX -> new IndomainMax<>();
        case "indomain_middle" -> new IndomainMiddle<>();
        case "indomain_median" -> new IndomainMedian<>();
        case "indomain_random" -> new IndomainRandom<>();
        default -> {
          System.err.println(WARNING_INDOMAIN_USED_MIN + indomain + "\"; used indomain_min");
          yield new IndomainMin<>();
        }
      };
    }
  }

  /**
   * Gets the variable selection comparator for integer variables.
   *
   * @return the comparator for variable selection
   */
  public ComparatorsVar<IntVar> getVarSelect() {

    if (varSelectionHeuristic == null) {
      return new ComparatorsVar<>(null);
    } else {
      return switch (varSelectionHeuristic) {
        case INPUT_ORDER -> new ComparatorsVar<>(null);
        case RANDOM -> new ComparatorsVar<>(new RandomVar<>());
        case FIRST_FAIL -> new ComparatorsVar<>(new SmallestDomain<>());
        case ANTI_FIRST_FAIL -> new ComparatorsVar<>(new LargestDomain<>());
        case MOST_CONSTRAINED ->
            new ComparatorsVar<>(new SmallestDomain<>(), new MostConstrainedStatic<>());
        case OCCURRENCE -> new ComparatorsVar<>(new MostConstrainedStatic<>());
        case SMALLEST -> new ComparatorsVar<>(new SmallestMin<>());
        case LARGEST -> new ComparatorsVar<>(new LargestMax<>());
        case "max_regret" -> new ComparatorsVar<>(new MaxRegret<>());
        case IMPACT ->
            new ComparatorsVar<>(new ActivityMax<>(store), new MostConstrainedStatic<>());
        case DOM_W_DEG -> new ComparatorsVar<>(new WeightedDegree<>(store));
        case "smallest_max" -> new ComparatorsVar<>(new SmallestMax<>(), new SmallestDomain<>());
        case "smallest_most_constrained" ->
            new ComparatorsVar<>(new SmallestMin<>(), new MostConstrainedStatic<>());
        case "smallest_first_fail" ->
            new ComparatorsVar<>(new SmallestMin<>(), new SmallestDomain<>());
        case AFC_MAX ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMax<>(store));
        case AFC_MIN ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMin<>(store));
        case AFC_MAX_DEG ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMaxDeg<>(store));
        case AFC_MIN_DEG ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMinDeg<>(store));
        case ACTIVITY_MAX ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMax<>(store));
        case ACTIVITY_MIN ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMin<>(store));
        case ACTIVITY_MAX_DEG ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMaxDeg<>(store));
        case ACTIVITY_MIN_DEG ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMinDeg<>(store));
        default -> {
          System.err.println(
              WARNING_VAR_HEURISTIC_PREFIX + varSelectionHeuristic + WARNING_VAR_HEURISTIC_SUFFIX);

          yield null;
        }
      };
    }
  }

  /**
   * Gets the variable selection comparator for float variables.
   *
   * @return the comparator for float variable selection
   */
  public ComparatorsVar<FloatVar> getFloatVarSelect() {

    if (varSelectionHeuristic == null) {
      return new ComparatorsVar<>(null);
    } else {
      return switch (varSelectionHeuristic) {
        case INPUT_ORDER -> new ComparatorsVar<>(null);
        case FIRST_FAIL -> new ComparatorsVar<>(new SmallestDomainFloat<>());
        case ANTI_FIRST_FAIL -> new ComparatorsVar<>(new LargestDomainFloat<>());
        case MOST_CONSTRAINED ->
            new ComparatorsVar<>(new SmallestDomainFloat<>(), new MostConstrainedStatic<>());
        case OCCURRENCE -> new ComparatorsVar<>(new MostConstrainedStatic<>());
        case SMALLEST -> new ComparatorsVar<>(new SmallestMinFloat<>());
        case LARGEST -> new ComparatorsVar<>(new LargestMaxFloat<>());
        case "max_regret" -> new ComparatorsVar<>(new MaxRegretFloat<>());
        case DOM_W_DEG -> new ComparatorsVar<>(new WeightedDegree<>(store));
        case IMPACT ->
            new ComparatorsVar<>(new ActivityMax<>(store), new MostConstrainedStatic<>());
        case AFC_MAX ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMax<>(store));
        case AFC_MAX_DEG ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMaxDeg<>(store));
        case AFC_MIN ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMin<>(store));
        case AFC_MIN_DEG ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMinDeg<>(store));
        case ACTIVITY_MAX ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMax<>(store));
        case ACTIVITY_MAX_DEG ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMaxDeg<>(store));
        case ACTIVITY_MIN ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMin<>(store));
        case ACTIVITY_MIN_DEG ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMinDeg<>(store));
        // for FloatVar's getSize() is not defined :(
        // afc*_deg and activity*_deg cannot be used
        case RANDOM -> new ComparatorsVar<>(new RandomVar<>());
        default -> {
          System.err.println(
              WARNING_VAR_HEURISTIC_PREFIX + varSelectionHeuristic + WARNING_VAR_HEURISTIC_SUFFIX);

          yield new ComparatorsVar<>(null);
        }
      };
    }
  }

  /**
   * Returns variable selection comparators for set variables.
   *
   * @return the variable selection comparators for set variables
   */
  ComparatorsVar<SetVar> getSetVarSelect() {

    if (varSelectionHeuristic == null) {
      return new ComparatorsVar<>(null);
    } else {
      return switch (varSelectionHeuristic) {
        case INPUT_ORDER -> new ComparatorsVar<>(null);
        case FIRST_FAIL -> new ComparatorsVar<>(new MinCardDiff<>());
        case SMALLEST -> new ComparatorsVar<>(new MinGlbCard<>());
        case OCCURRENCE -> new ComparatorsVar<>(new MostConstrainedStatic<>());
        case ANTI_FIRST_FAIL -> new ComparatorsVar<>(new MaxCardDiff<>());
        case DOM_W_DEG -> new ComparatorsVar<>(new WeightedDegree<>(store));
        case IMPACT ->
            new ComparatorsVar<>(new ActivityMax<>(store), new MostConstrainedStatic<>());
        case AFC_MAX ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMax<>(store));
        case AFC_MIN ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMin<>(store));
        case AFC_MAX_DEG ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMaxDeg<>(store));
        case AFC_MIN_DEG ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMinDeg<>(store));
        case ACTIVITY_MAX ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMax<>(store));
        case ACTIVITY_MIN ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMin<>(store));
        case ACTIVITY_MAX_DEG ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMaxDeg<>(store));
        case ACTIVITY_MIN_DEG ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMinDeg<>(store));
        case MOST_CONSTRAINED ->
            new ComparatorsVar<>(new MinGlbCard<>(), new MostConstrainedStatic<>());
        case LARGEST -> new ComparatorsVar<>(new MaxLubCard<>());
        case RANDOM -> new ComparatorsVar<>(new RandomVar<>());
        default -> {
          System.err.println(
              WARNING_VAR_HEURISTIC_PREFIX + varSelectionHeuristic + WARNING_VAR_HEURISTIC_SUFFIX);

          yield new ComparatorsVar<>(null);
        }
      };
    }
  }

  /**
   * Retrieves an integer variable from a scalar flat expression node.
   *
   * @param node the scalar flat expression node
   * @return the integer variable
   */
  IntVar getVariable(ASTScalarFlatExpr node) {
    if (node.getType() == 0) { // int
      return dictionary.getConstant(
          node.getInt()); // new IntVar(store, node.getInt(), node.getInt());
    } else if (node.getType() == 2) { // ident
      return dictionary.getVariable(node.getIdent());
    } else if (node.getType() == 3) { // array access
      if (node.getInt() > dictionary.getVariableArray(node.getIdent()).length
          || node.getInt() < 0) {
        throw new IllegalArgumentException(
            "Index out of bound for " + node.getIdent() + "[" + node.getInt() + "]");
      } else {
        return dictionary.getVariableArray(node.getIdent())[node.getInt()];
      }
    } else {
      throw new IllegalArgumentException("Wrong parameter " + node);
    }
  }

  /**
   * Retrieves a float variable from a scalar flat expression node.
   *
   * @param node the scalar flat expression node
   * @return the float variable
   */
  FloatVar getFloatVariable(ASTScalarFlatExpr node) {
    if (node.getType() == 5) { // float
      return new FloatVar(store, node.getFloat(), node.getFloat());
    } else if (node.getType() == 2) { // ident
      return dictionary.getFloatVariable(node.getIdent());
    } else if (node.getType() == 3) { // array access
      if (node.getInt() > dictionary.getVariableFloatArray(node.getIdent()).length
          || node.getInt() < 0) {
        throw new IllegalArgumentException(
            "Index out of bound for " + node.getIdent() + "[" + node.getInt() + "]");
      } else {
        return dictionary.getVariableFloatArray(node.getIdent())[node.getInt()];
      }
    } else {
      throw new IllegalArgumentException("Wrong parameter " + node);
    }
  }

  /**
   * Retrieves an integer array from a parse tree node.
   *
   * @param node the parse tree node
   * @return the integer array
   */
  int[] getIntArray(SimpleNode node) {

    if (Objects.equals(((ASTAnnotation) node).getAnnId(), ANN_VECTOR)) {
      int count = node.jjtGetNumChildren();
      int[] aa = new int[count];
      for (int i = 0; i < count; i++) {
        SimpleNode n = (SimpleNode) node.jjtGetChild(i).jjtGetChild(0);
        ASTScalarFlatExpr child = (ASTScalarFlatExpr) n.jjtGetChild(0);
        int el = getInt(child);
        aa[i] = el;
      }
      return aa;
    } else if (Objects.equals(((ASTAnnotation) node).getAnnId(), ANN_EXPR)) {
      SimpleNode n = (SimpleNode) node.jjtGetChild(0).jjtGetChild(0);
      if (((ASTScalarFlatExpr) n).getType() == 2) { // ident
        return dictionary.getIntArray(((ASTScalarFlatExpr) n).getIdent());
      } else {
        throw new IllegalArgumentException(
            "Wrong parameters in integer array; compilation aborted.");
      }
    } else {
      throw new IllegalArgumentException("Wrong parameters integer array; compilation aborted.");
    }
  }

  /**
   * Gets an integer value from a scalar flat expression node.
   *
   * @param node the AST scalar flat expression node
   * @return the integer value
   */
  public int getInt(ASTScalarFlatExpr node) {

    if (node.getType() == 0) { // int
      return node.getInt();
    }
    if (node.getType() == 1) { // bool
      return node.getInt();
    } else if (node.getType() == 2) { // ident
      return dictionary.getInt(node.getIdent());
    } else if (node.getType() == 3) { // array access
      int[] intTable = dictionary.getIntArray(node.getIdent());
      if (intTable == null) {
        throw new IllegalArgumentException("getInt: Table not present " + node);
      } else {
        return intTable[node.getInt()];
      }
    } else {
      throw new IllegalArgumentException("getInt: Wrong parameter " + node);
    }
  }

  /**
   * Retrieves an array of integer variables from a parse tree node.
   *
   * @param node the parse tree node
   * @return the array of integer variables
   */
  IntVar[] getVarArray(SimpleNode node) {

    if (Objects.equals(((ASTAnnotation) node).getAnnId(), ANN_VECTOR)) {
      int count = node.jjtGetNumChildren();
      IntVar[] aa = new IntVar[count];
      for (int i = 0; i < count; i++) {
        SimpleNode n = (SimpleNode) node.jjtGetChild(i).jjtGetChild(0);
        ASTScalarFlatExpr child = (ASTScalarFlatExpr) n.jjtGetChild(0);
        IntVar el = getVariable(child);
        aa[i] = el;
      }
      return aa;
    } else if (Objects.equals(((ASTAnnotation) node).getAnnId(), ANN_EXPR)) {
      ASTAnnExpr m = (ASTAnnExpr) node.jjtGetChild(0);
      if ("ArrayLiteral".equals(m.jjtGetChild(0).toString())
          && m.jjtGetChild(0).jjtGetNumChildren() == 0) {
        // enpty vector
        return new IntVar[0];
      }

      SimpleNode n = (SimpleNode) node.jjtGetChild(0).jjtGetChild(0);

      if (((ASTScalarFlatExpr) n).getType() == 2) { // ident
        return dictionary.getVariableArray(((ASTScalarFlatExpr) n).getIdent());
      } else {
        throw new IllegalArgumentException("Wrong type of variable array; compilation aborted.");
      }
    } else {
      throw new IllegalArgumentException("Wrong type of variable array; compilation aborted.");
    }
  }

  /**
   * Retrieves an array of float variables from a parse tree node.
   *
   * @param node the parse tree node
   * @return the array of float variables
   */
  FloatVar[] getFloatVarArray(SimpleNode node) {

    if (Objects.equals(((ASTAnnotation) node).getAnnId(), ANN_VECTOR)) {
      int count = node.jjtGetNumChildren();
      FloatVar[] aa = new FloatVar[count];
      for (int i = 0; i < count; i++) {
        SimpleNode n = (SimpleNode) node.jjtGetChild(i).jjtGetChild(0);
        ASTScalarFlatExpr child = (ASTScalarFlatExpr) n.jjtGetChild(0);
        FloatVar el = getFloatVariable(child);
        aa[i] = el;
      }
      return aa;
    } else if (Objects.equals(((ASTAnnotation) node).getAnnId(), ANN_EXPR)) {
      SimpleNode n = (SimpleNode) node.jjtGetChild(0).jjtGetChild(0);
      if (((ASTScalarFlatExpr) n).getType() == 2) { // ident
        return dictionary.getVariableFloatArray(((ASTScalarFlatExpr) n).getIdent());
      } else {
        throw new IllegalArgumentException("Wrong type of variable array; compilation aborted.");
      }
    } else {
      throw new IllegalArgumentException("Wrong type of variable array; compilation aborted.");
    }
  }

  /**
   * Retrieves a set variable from a scalar flat expression node.
   *
   * @param node the scalar flat expression node
   * @return the set variable
   */
  SetVar getSetVariable(ASTScalarFlatExpr node) {
    if (node.getType() == 2) { // ident
      return dictionary.getSetVariable(node.getIdent());
    } else if (node.getType() == 3) { // array access
      return dictionary.getSetVariableArray(node.getIdent())[node.getInt()];
    } else {
      throw new IllegalArgumentException("Wrong parameter on list of search set variables" + node);
    }
  }

  /**
   * Retrieves an array of set variables from a parse tree node.
   *
   * @param node the parse tree node
   * @return the array of set variables
   */
  SetVar[] getSetVarArray(SimpleNode node) {

    if (Objects.equals(((ASTAnnotation) node).getAnnId(), ANN_VECTOR)) {
      int count = node.jjtGetNumChildren();
      SetVar[] aa = new SetVar[count];
      for (int i = 0; i < count; i++) {
        SimpleNode n = (SimpleNode) node.jjtGetChild(i).jjtGetChild(0);
        if (((SimpleNode) n.jjtGetChild(0)).getId() == JJTSETLITERAL) {
          SetVar el =
              new SetVar(
                  store); // ground set already defined on variable list; define empty set for
          // search
          aa[i] = el;
        } else {
          ASTScalarFlatExpr child = (ASTScalarFlatExpr) n.jjtGetChild(0);
          SetVar el = getSetVariable(child);
          aa[i] = el;
        }
      }
      return aa;
    } else if (Objects.equals(((ASTAnnotation) node).getAnnId(), ANN_EXPR)) {
      SimpleNode n = (SimpleNode) node.jjtGetChild(0).jjtGetChild(0);
      if (((ASTScalarFlatExpr) n).getType() == 2) { // ident
        return dictionary.getSetVariableArray(((ASTScalarFlatExpr) n).getIdent());
      } else {
        throw new IllegalArgumentException("Wrong type of variable array; compilation aborted.");
      }
    } else {
      throw new IllegalArgumentException("Wrong type of variable array; compilation aborted.");
    }
  }

  /**
   * Returns the search type.
   *
   * @return the search type
   */
  public String type() {
    return searchType;
  }

  /**
   * Sets the search type.
   *
   * @param st the search type to set
   */
  public void setSearchType(String st) {
    searchType = st;
  }

  /**
   * Returns the exploration strategy.
   *
   * @return the exploration strategy
   */
  public String exploration() {
    return explore;
  }

  /**
   * Returns the indomain heuristic name.
   *
   * @return the indomain heuristic name
   */
  public String indomain() {
    return indomain;
  }

  /**
   * Returns the variable selection heuristic name.
   *
   * @return the variable selection heuristic name
   */
  public String varSelection() {
    return varSelectionHeuristic;
  }

  /**
   * Returns the search variables.
   *
   * @return the array of search variables
   */
  public Var[] vars() {
    return searchVariables;
  }

  /**
   * Returns the list of sub-search items.
   *
   * @return the list of search items
   */
  ArrayList<SearchItem<T>> getSearchItems() {
    return searchSeq;
  }

  /**
   * Extracts the variable selection heuristic from an annotation.
   *
   * @param expr the annotation expression
   * @return the variable selection heuristic name
   */
  public String getVarSelectHeuristic(ASTAnnotation expr) {

    if (ANN_EXPR.equals(expr.getAnnId())) {
      return ((ASTScalarFlatExpr) expr.jjtGetChild(0).jjtGetChild(0)).getIdent();
    }
    if (expr.getId() == JJTANNOTATION && "tiebreak".equals(expr.getAnnId())) {
      return getVarSelectHeuristicFromTiebreak(expr);
    }
    throw new IllegalArgumentException(
        "Not supported Variable selection annotation; compilation aborted.");
  }

  private String getVarSelectHeuristicFromTiebreak(ASTAnnotation expr) {
    if (!Objects.equals(((ASTAnnotation) expr.jjtGetChild(0)).getAnnId(), ANN_VECTOR)) {
      throw new IllegalArgumentException(
          "Not supported Variable selection annotation; compilation aborted.");
    }
    int count = expr.jjtGetChild(0).jjtGetNumChildren();
    if (count < 2) {
      throw new IllegalArgumentException(
          "tiebreak annotation must have two variable selection methods; compilation aborted.");
    }
    String varSel1 =
        ((ASTScalarFlatExpr) expr.jjtGetChild(0).jjtGetChild(0).jjtGetChild(0).jjtGetChild(0))
            .getIdent();
    varSelectionHeuristic =
        ((ASTScalarFlatExpr) expr.jjtGetChild(0).jjtGetChild(1).jjtGetChild(0).jjtGetChild(0))
            .getIdent();
    applyTieBreakTieBreaking();
    if (count > 2) {
      System.err.println(
          "% Warning: tiebreak annotation uses only two variable selection methods, the rest is ignored");
    }
    return varSel1;
  }

  private void applyTieBreakTieBreaking() {
    if ("int_search".equals(searchType) || "bool_search".equals(searchType)) {
      tieBreakingInt = getVarSelect().getVarSel();
    } else if ("set_search".equals(searchType)) {
      tieBreakingSet = getSetVarSelect().getVarSel();
    } else if ("float_search".equals(searchType)) {
      tieBreakingFloat = getFloatVarSelect().getVarSel();
    } else if ("priority_search".equals(searchType)) {
      tieBreakingInt = getVarSelect().getVarSel();
    }
  }

  /**
   * Adds a search item to the sequence.
   *
   * @param si the search item to add
   */
  public void addSearch(SearchItem<T> si) {
    searchSeq.add(si);
  }

  /**
   * Returns the size of the search sequence.
   *
   * @return the number of search items in the sequence
   */
  public int searchSeqSize() {
    return searchSeq.size();
  }

  /** {@inheritDoc} */
  @Override
  public String toString() {
    StringBuilder s = new StringBuilder();
    if (searchType == null) {
      s.append("default_search\n");
    } else if (searchSeq.isEmpty()) {
      appendSingleSearchToString(s);
    } else if (prioritySearch) {
      appendPrioritySearchToString(s);
    } else {
      appendSeqSearchToString(s);
    }
    return s.toString();
  }

  private void appendSingleSearchToString(StringBuilder s) {
    s.append(searchType).append("(");
    if (searchVariables == null) {
      s.append("[]");
    } else {
      s.append("array1d(1..")
          .append(searchVariables.length)
          .append(", ")
          .append(Arrays.asList(searchVariables));
      if (WARM_START.equals(searchType)) {
        s.append(", ").append(preferedValues);
      }
    }
    s.append(", ")
        .append(varSelectionHeuristic)
        .append(", ")
        .append(indomain)
        .append(", ")
        .append(explore)
        .append(")");
    if (floatSearch) {
      s.append(", ").append(precision);
    }
  }

  private void appendPrioritySearchToString(StringBuilder s) {
    s.append("priority_search(");
    s.append("array1d(1..")
        .append(searchVariables.length)
        .append(", ")
        .append(Arrays.asList(searchVariables));
    s.append(", [");
    appendSearchSeqItems(s);
    s.append("]");
    s.append(", ").append(varSelectionHeuristic).append(", ").append(explore).append(")");
    s.append(")");
  }

  private void appendSeqSearchToString(StringBuilder s) {
    s.append("seq_search([");
    appendSearchSeqItems(s);
    s.append("])");
  }

  private void appendSearchSeqItems(StringBuilder s) {
    for (int i = 0; i < searchSeq.size(); i++) {
      if (i == searchSeq.size() - 1) {
        s.append(searchSeq.get(i));
      } else {
        s.append(searchSeq.get(i)).append(", ");
      }
    }
  }

  /** Pair of comparator variables for tie-breaking. */
  public static class ComparatorsVar<T extends Var> {
    final ComparatorVariable<T> v1;
    final ComparatorVariable<T> v2;

    /**
     * Creates a pair of variable comparators for variable selection and tie-breaking.
     *
     * @param v1 the primary variable comparator
     * @param v2 the tie-breaking variable comparator
     */
    public ComparatorsVar(ComparatorVariable<T> v1, ComparatorVariable<T> v2) {
      this.v1 = v1;
      this.v2 = v2;
    }

    /**
     * Creates a variable comparator with only a primary comparator.
     *
     * @param v1 the primary variable comparator
     */
    public ComparatorsVar(ComparatorVariable<T> v1) {
      this.v1 = v1;
      this.v2 = null;
    }

    /**
     * Returns the primary variable selector.
     *
     * @return the primary variable comparator
     */
    public ComparatorVariable<T> getVarSel() {
      return v1;
    }

    /**
     * Returns the tie-breaking variable selector.
     *
     * @return the tie-breaking variable comparator
     */
    public ComparatorVariable<T> getTieSel() {
      return v2;
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
      return "(" + v1 + ", " + v2 + ")";
    }
  }
}
