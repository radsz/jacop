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

  final ArrayList<SearchItem<T>> search_seq = new ArrayList<>();
  Var[] search_variables;
  String search_type;
  String explore = "complete";
  String indomain;
  String var_selection_heuristic;

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

  // relax and reconstruct
  IntVar[] relax_and_reconstruct_variables;
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
    search_type = ann.getAnnId();

    switch (search_type) {
      case "int_search", "bool_search" -> {
        SimpleNode expr1 = (SimpleNode) ann.jjtGetChild(0);
        search_variables = getVarArray(expr1);

        ASTAnnotation expr2 = (ASTAnnotation) ann.jjtGetChild(1);
        var_selection_heuristic = getVarSelectHeuristic(expr2);

        ASTAnnExpr expr3 = (ASTAnnExpr) ann.jjtGetChild(2).jjtGetChild(0);
        indomain = ((ASTScalarFlatExpr) expr3.jjtGetChild(0)).getIdent();

        ASTAnnotation expr4 = (ASTAnnotation) ann.jjtGetChild(3);
        explorationType(expr4);
      }
      case "set_search" -> {
        SimpleNode expr1 = (SimpleNode) ann.jjtGetChild(0);
        search_variables = getSetVarArray(expr1);

        ASTAnnotation expr2 = (ASTAnnotation) ann.jjtGetChild(1);
        var_selection_heuristic = getVarSelectHeuristic(expr2);

        ASTAnnExpr expr3 = (ASTAnnExpr) ann.jjtGetChild(2).jjtGetChild(0);
        indomain = ((ASTScalarFlatExpr) expr3.jjtGetChild(0)).getIdent();

        ASTAnnotation expr4 = (ASTAnnotation) ann.jjtGetChild(3);
        explorationType(expr4);
      }
      case "float_search" -> {
        floatSearch = true;

        SimpleNode expr1 = (SimpleNode) ann.jjtGetChild(0);
        search_variables = getFloatVarArray(expr1);

        ASTAnnotation expr2 = (ASTAnnotation) ann.jjtGetChild(2);
        var_selection_heuristic = getVarSelectHeuristic(expr2);

        ASTAnnExpr expr3 = (ASTAnnExpr) ann.jjtGetChild(3).jjtGetChild(0);
        indomain = ((ASTScalarFlatExpr) expr3.jjtGetChild(0)).getIdent();

        ASTAnnotation expr4 = (ASTAnnotation) ann.jjtGetChild(4);
        explorationType(expr4);

        ASTAnnExpr expr5 = (ASTAnnExpr) ann.jjtGetChild(1).jjtGetChild(0);
        precision = ((ASTScalarFlatExpr) expr5.jjtGetChild(0)).getFloat();
      }
      case "seq_search" -> {
        SimpleNode body = (SimpleNode) ann.jjtGetChild(0);
        search_type = "seq_search";

        makeVectorOfSearches(body);
      }
      case "warm_start" -> {
        SimpleNode expr1 = (SimpleNode) ann.jjtGetChild(0);
        search_variables = getVarArray(expr1);

        SimpleNode expr2 = (SimpleNode) ann.jjtGetChild(1);
        int[] values = null;
        try {
          values = getIntArray(expr2);
        } catch (IllegalArgumentException _) {
          throw new IllegalArgumentException(
              "%Not supported types of values in warm_start; compilation aborted");
        }

        if (search_variables == null || values == null) {
          throw new IllegalArgumentException(
              "Not supported variable and/or value type in warm_start; compilation aborted.");
        }
        preferedValues = new HashMap<>();
        int max = 0;
        int min = 0;
        for (int i = 0; i < values.length; i++) {
          IntVar v = (IntVar) search_variables[i];
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

        var_selection_heuristic = "input_order";
        indomain = max > min ? "indomain_max" : "indomain_min";
      }
      case "priority_search" -> {
        prioritySearch = true;

        SimpleNode expr1 = (SimpleNode) ann.jjtGetChild(0);
        search_variables = getVarArray(expr1);

        SimpleNode searches = (SimpleNode) ann.jjtGetChild(1);
        makeVectorOfSearches(searches);

        ASTAnnotation expr2 = (ASTAnnotation) ann.jjtGetChild(2);
        var_selection_heuristic = getVarSelectHeuristic(expr2);

        ASTAnnotation expr3 = (ASTAnnotation) ann.jjtGetChild(3);
        explorationType(expr3);
        if (!"complete".equals(explore)) {
          System.err.println("Warning: not recognized search exploration type; use \"complete\"");
        }
      }
      case "restart_none" -> {}
      case "restart_constant" -> {
        ASTAnnExpr expr = (ASTAnnExpr) ann.jjtGetChild(0).jjtGetChild(0);
        int scale = ((ASTScalarFlatExpr) expr.jjtGetChild(0)).getInt();
        restartCalculator = new ConstantCalculator(scale);
      }
      case "restart_linear" -> {
        ASTAnnExpr expr = (ASTAnnExpr) ann.jjtGetChild(0).jjtGetChild(0);
        int scale = ((ASTScalarFlatExpr) expr.jjtGetChild(0)).getInt();
        restartCalculator = new LinearCalculator(scale);
      }
      case "restart_luby" -> {
        ASTAnnExpr expr = (ASTAnnExpr) ann.jjtGetChild(0).jjtGetChild(0);
        int scale = ((ASTScalarFlatExpr) expr.jjtGetChild(0)).getInt();
        restartCalculator = new LubyCalculator(scale);
      }
      case "restart_geometric" -> {
        ASTAnnExpr expr1 = (ASTAnnExpr) ann.jjtGetChild(0).jjtGetChild(0);
        double base = ((ASTScalarFlatExpr) expr1.jjtGetChild(0)).getFloat();
        ASTAnnExpr expr2 = (ASTAnnExpr) ann.jjtGetChild(1).jjtGetChild(0);
        int scale = ((ASTScalarFlatExpr) expr2.jjtGetChild(0)).getInt();
        restartCalculator = new GeometricCalculator(base, scale);
      }
      case "relax_and_reconstruct" -> {
        SimpleNode expr1 = (SimpleNode) ann.jjtGetChild(0);
        relax_and_reconstruct_variables = getVarArray(expr1);
        ASTAnnExpr expr2 = (ASTAnnExpr) ann.jjtGetChild(1).jjtGetChild(0);
        probability = ((ASTScalarFlatExpr) expr2.jjtGetChild(0)).getInt();
      }
      case null, default -> IO.println("% Warning: Ignored search annotation " + search_type);
    }

    // compilation aborted.");
  }

  /**
   * Creates a vector of search items from a parse tree node.
   *
   * @param body the parse tree node containing the search vector
   */
  void makeVectorOfSearches(SimpleNode body) {

    if (Objects.equals(((ASTAnnotation) body).getAnnId(), "$vector")) {

      int count = body.jjtGetNumChildren();

      for (int i = 0; i < count; i++) {
        SearchItem<T> subSearch = new SearchItem<>(store, dictionary);

        ASTAnnotation ann = (ASTAnnotation) body.jjtGetChild(i);
        // priority_search not supported; execution aborted");

        subSearch.searchParameters(body, i);

        if ("seq_search".equals(ann.getAnnId())) {
          search_seq.add(subSearch);
          continue;
        }

        if (subSearch.search_variables != null && subSearch.search_variables.length > 0) {
          search_seq.add(subSearch);
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
      case "$expr" ->
          explore = ((ASTScalarFlatExpr) expr4.jjtGetChild(0).jjtGetChild(0)).getIdent();
      case "credit" -> {
        explore = "credit";
        if (expr4.jjtGetNumChildren() == 2) {
          if (((ASTAnnotation) expr4.jjtGetChild(0)).getAnnId() == "$expr") {
            ASTAnnExpr cp = (ASTAnnExpr) expr4.jjtGetChild(0).jjtGetChild(0);
            if (cp.jjtGetNumChildren() == 1) {
              creditValue = ((ASTScalarFlatExpr) cp.jjtGetChild(0)).getInt();
            }
          }
          ASTAnnotation bbs = (ASTAnnotation) expr4.jjtGetChild(1);
          if (bbs.getId() == JJTANNOTATION && "bbs".equals(bbs.getAnnId())) {
            if (bbs.jjtGetChild(0).jjtGetNumChildren() == 1) {
              if (((SimpleNode) bbs.jjtGetChild(0).jjtGetChild(0)).getId() == JJTANNEXPR) {
                ASTAnnExpr bv = (ASTAnnExpr) bbs.jjtGetChild(0).jjtGetChild(0);
                if (bv.jjtGetNumChildren() == 1) {
                  bbsValue = ((ASTScalarFlatExpr) bv.jjtGetChild(0)).getInt();
                  return;
                }
              }
            }
          }
        }
        explore = "complete";
        System.err.println("Warning: not recognized search exploration type; use \"complete\"");
      }
      case "lds" -> {
        explore = "lds";

        if (expr4.jjtGetNumChildren() == 1) {
          if (((ASTAnnotation) expr4.jjtGetChild(0)).getAnnId() == "$expr") {
            if (((SimpleNode) expr4.jjtGetChild(0).jjtGetChild(0)).getId() == JJTANNEXPR) {
              ASTAnnExpr ae = (ASTAnnExpr) expr4.jjtGetChild(0).jjtGetChild(0);
              if (ae.jjtGetNumChildren() == 1) {
                ldsValue = ((ASTScalarFlatExpr) ae.jjtGetChild(0)).getInt();
                return;
              }
            }
          }
        }
        explore = "complete";
        System.err.println("Warning: not recognized search exploration type; use \"complete\"");
      }
      case null, default ->
          throw new RuntimeException(
              "Error: not recognized search exploration type; execution aborted");
    }
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

      if (search_type == null && "warm_start".equals(subSearch.search_type)) {
        search_seq.addFirst(subSearch);
      } else {
        search_seq.add(subSearch);
      }
    }

    search_type = "seq_search";
  }

  /**
   * Creates a select choice point for warm start search.
   *
   * @return the select choice point for warm start
   */
  SelectChoicePoint<IntVar> getWarmStartSelect() {

    Indomain<IntVar> indom =
        "indomain_min".equals(indomain)
            ? new IndomainDefaultValue<>(preferedValues, new IndomainMin<>())
            : new IndomainDefaultValue<>(preferedValues, new IndomainMax<>());
    ArrayList<IntVar> sv = new ArrayList<>();
    for (Var searchVariable : search_variables) {
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
    ComparatorVariable<IntVar> var_sel = vs.getVarSel();

    return new SimpleSelect<>(searchVars, var_sel, indom);
  }

  /**
   * Creates a select choice point for integer variable search.
   *
   * @return the select choice point for integer variables
   */
  SelectChoicePoint<IntVar> getIntSelect() {

    if ("random".equals(var_selection_heuristic)) {
      Indomain<IntVar> indom = getIndomain(indomain);
      IntVar[] searchVars = new IntVar[search_variables.length];
      for (int i = 0; i < search_variables.length; i++) {
        searchVars[i] = (IntVar) search_variables[i];
      }
      return new RandomSelect<>(searchVars, indom);
    }

    ComparatorsVar<IntVar> vs = getVarSelect();
    ComparatorVariable<IntVar> var_sel = vs.getVarSel();
    ComparatorVariable<IntVar> tieBreaking =
        tieBreakingInt == null ? vs.getTieSel() : tieBreakingInt;
    IntVar[] searchVars = new IntVar[search_variables.length];
    for (int i = 0; i < search_variables.length; i++) {
      searchVars[i] = (IntVar) search_variables[i];
    }

    if ("indomain_split".equals(indomain)) {
      if (tieBreaking == null) {
        return new SplitSelect<>(searchVars, var_sel, new IndomainMiddle<>());
      } else {
        return new SplitSelect<>(searchVars, var_sel, tieBreaking, new IndomainMiddle<>());
      }
    } else if ("indomain_split_random".equals(indomain)) {
      if (tieBreaking == null) {
        return new SplitRandomSelect<>(searchVars, var_sel, new IndomainMiddle<>());
      } else {
        return new SplitRandomSelect<>(searchVars, var_sel, tieBreaking, new IndomainMiddle<>());
      }
    } else if ("indomain_reverse_split".equals(indomain)) {
      if (tieBreaking == null) {
        SplitSelect<IntVar> sel = new SplitSelect<>(searchVars, var_sel, new IndomainMiddle<>());
        sel.leftFirst = false;
        return sel;
      } else {
        SplitSelect<IntVar> sel =
            new SplitSelect<>(searchVars, var_sel, tieBreaking, new IndomainMiddle<>());
        sel.leftFirst = false;
        return sel;
      }
    } else if ("outdomain_max".equals(indomain)) {
      if (tieBreaking == null) {
        return new SplitSelect<>(searchVars, var_sel, new IndomainMax<>());
      } else {
        return new SplitSelect<>(searchVars, var_sel, tieBreaking, new IndomainMax<>());
      }
    } else if ("outdomain_min".equals(indomain)) {
      if (tieBreaking == null) {
        SplitSelect<IntVar> sel = new SplitSelect<>(searchVars, var_sel, new IndomainMin<>());
        sel.leftFirst = false;
        return sel;
      } else {
        SplitSelect<IntVar> sel =
            new SplitSelect<>(searchVars, var_sel, tieBreaking, new IndomainMin<>());
        sel.leftFirst = false;
        return sel;
      }
    } else if ("input_order".equals(var_selection_heuristic)) {
      Indomain<IntVar> indom = getIndomain(indomain);
      return new InputOrderSelect<>(store, (IntVar[]) search_variables, indom);
    } else {
      Indomain<IntVar> indom = getIndomain(indomain);
      if (tieBreaking == null) {
        return new SimpleSelect<>((IntVar[]) search_variables, var_sel, indom);
      } else {
        return new SimpleSelect<>((IntVar[]) search_variables, var_sel, tieBreaking, indom);
      }
    }
  }

  /**
   * Creates a select choice point for float variable search.
   *
   * @return the select choice point for float variables
   */
  SelectChoicePoint<FloatVar> getFloatSelect() {

    ComparatorsVar<FloatVar> vs = getFloatVarSelect();
    ComparatorVariable<FloatVar> var_sel = vs.getVarSel();
    ComparatorVariable<FloatVar> tieBreaking =
        tieBreakingFloat == null ? vs.getTieSel() : tieBreakingFloat;
    FloatVar[] searchVars = new FloatVar[search_variables.length];
    for (int i = 0; i < search_variables.length; i++) {
      searchVars[i] = (FloatVar) search_variables[i];
    }

    switch (indomain) {
      case "indomain_split" -> {
        if (tieBreaking == null) {
          return new SplitSelectFloat<>(store, searchVars, var_sel);
        } else {
          return new SplitSelectFloat<>(store, searchVars, var_sel, tieBreaking);
        }
      }
      case "indomain_split_random" -> {
        if (tieBreaking == null) {
          return new SplitRandomSelectFloat<>(store, searchVars, var_sel);
        } else {
          return new SplitRandomSelectFloat<>(store, searchVars, var_sel, tieBreaking);
        }
      }
      case "indomain_reverse_split" -> {
        if (tieBreaking == null) {
          SplitSelectFloat<FloatVar> sel = new SplitSelectFloat<>(store, searchVars, var_sel);
          sel.leftFirst = false;
          return sel;
        } else {
          SplitSelectFloat<FloatVar> sel =
              new SplitSelectFloat<>(store, searchVars, var_sel, tieBreaking);
          sel.leftFirst = false;
          return sel;
        }
      }
      case null, default ->
          throw new IllegalArgumentException(
              "Wrong parameters for float_search. Only indomain_split, indomain_reverse_split or indomain_split_random are allowed.");
    }
  }

  /**
   * Creates a select choice point for set variable search.
   *
   * @return the select choice point for set variables
   */
  SelectChoicePoint<SetVar> getSetSelect() {

    ComparatorsVar<SetVar> vs = getSetVarSelect();
    ComparatorVariable<SetVar> var_sel = vs.getVarSel();
    ComparatorVariable<SetVar> tieBreaking =
        tieBreakingSet == null ? vs.getTieSel() : tieBreakingSet;

    Indomain<SetVar> indom = getIndomain4Set(indomain);
    SetVar[] searchVars = new SetVar[search_variables.length];
    for (int i = 0; i < search_variables.length; i++) {
      searchVars[i] = (SetVar) search_variables[i];
    }

    if (tieBreaking == null) {
      return new SimpleSelect<>(searchVars, var_sel, indom);
    } else {
      return new SimpleSelect<>(searchVars, var_sel, tieBreaking, indom);
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
        case "indomain_min" -> new IndomainSetMin<>();
        case "indomain_max" -> new IndomainSetMax<>();
        case "indomain_random" -> new IndomainSetRandom<>();
        default -> {
          System.err.println(
              "Warning: Not implemented indomain method \"" + indomain + "\"; used indomain_min");
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
        case "indomain_min" -> new IndomainMin<>();
        case "indomain_max" -> new IndomainMax<>();
        case "indomain_middle" -> new IndomainMiddle<>();
        case "indomain_median" -> new IndomainMedian<>();
        case "indomain_random" -> new IndomainRandom<>();
        default -> {
          System.err.println(
              "Warning: Not implemented indomain method \"" + indomain + "\"; used indomain_min");
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

    if (var_selection_heuristic == null) {
      return new ComparatorsVar<>(null);
    } else {
      return switch (var_selection_heuristic) {
        case "input_order" -> new ComparatorsVar<>(null);
        case "random" -> new ComparatorsVar<>(new RandomVar<>());
        case "first_fail" -> new ComparatorsVar<>(new SmallestDomain<>());
        case "anti_first_fail" -> new ComparatorsVar<>(new LargestDomain<>());
        case "most_constrained" ->
            new ComparatorsVar<>(new SmallestDomain<>(), new MostConstrainedStatic<>());
        case "occurrence" -> new ComparatorsVar<>(new MostConstrainedStatic<>());
        case "smallest" -> new ComparatorsVar<>(new SmallestMin<>());
        case "largest" -> new ComparatorsVar<>(new LargestMax<>());
        case "max_regret" -> new ComparatorsVar<>(new MaxRegret<>());
        case "impact" ->
            new ComparatorsVar<>(new ActivityMax<>(store), new MostConstrainedStatic<>());
        case "dom_w_deg" -> new ComparatorsVar<>(new WeightedDegree<>(store));
        case "smallest_max" -> new ComparatorsVar<>(new SmallestMax<>(), new SmallestDomain<>());
        case "smallest_most_constrained" ->
            new ComparatorsVar<>(new SmallestMin<>(), new MostConstrainedStatic<>());
        case "smallest_first_fail" ->
            new ComparatorsVar<>(new SmallestMin<>(), new SmallestDomain<>());
        case "afc_max" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMax<>(store));
        case "afc_min" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMin<>(store));
        case "afc_max_deg" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMaxDeg<>(store));
        case "afc_min_deg" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMinDeg<>(store));
        case "activity_max" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMax<>(store));
        case "activity_min" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMin<>(store));
        case "activity_max_deg" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMaxDeg<>(store));
        case "activity_min_deg" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMinDeg<>(store));
        default -> {
          System.err.println(
              "Warning: Not implemented variable selection heuristic \""
                  + var_selection_heuristic
                  + "\"; used input_order");

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

    if (var_selection_heuristic == null) {
      return new ComparatorsVar<>(null);
    } else {
      return switch (var_selection_heuristic) {
        case "input_order" -> new ComparatorsVar<>(null);
        case "first_fail" -> new ComparatorsVar<>(new SmallestDomainFloat<>());
        case "anti_first_fail" -> new ComparatorsVar<>(new LargestDomainFloat<>());
        case "most_constrained" ->
            new ComparatorsVar<>(new SmallestDomainFloat<>(), new MostConstrainedStatic<>());
        case "occurrence" -> new ComparatorsVar<>(new MostConstrainedStatic<>());
        case "smallest" -> new ComparatorsVar<>(new SmallestMinFloat<>());
        case "largest" -> new ComparatorsVar<>(new LargestMaxFloat<>());
        case "max_regret" -> new ComparatorsVar<>(new MaxRegretFloat<>());
        case "dom_w_deg" -> new ComparatorsVar<>(new WeightedDegree<>(store));
        case "impact" ->
            new ComparatorsVar<>(new ActivityMax<>(store), new MostConstrainedStatic<>());
        case "afc_max" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMax<>(store));
        case "afc_max_deg" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMaxDeg<>(store));
        case "afc_min" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMin<>(store));
        case "afc_min_deg" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMinDeg<>(store));
        case "activity_max" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMax<>(store));
        case "activity_max_deg" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMaxDeg<>(store));
        case "activity_min" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMin<>(store));
        case "activity_min_deg" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMinDeg<>(store));
        // for FloatVar's getSize() is not defined :(
        // afc*_deg and activity*_deg cannot be used
        case "random" -> new ComparatorsVar<>(new RandomVar<>());
        default -> {
          System.err.println(
              "Warning: Not implemented variable selection heuristic \""
                  + var_selection_heuristic
                  + "\"; used input_order");

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

    if (var_selection_heuristic == null) {
      return new ComparatorsVar<>(null);
    } else {
      return switch (var_selection_heuristic) {
        case "input_order" -> new ComparatorsVar<>(null);
        case "first_fail" -> new ComparatorsVar<>(new MinCardDiff<>());
        case "smallest" -> new ComparatorsVar<>(new MinGlbCard<>());
        case "occurrence" -> new ComparatorsVar<>(new MostConstrainedStatic<>());
        case "anti_first_fail" -> new ComparatorsVar<>(new MaxCardDiff<>());
        case "dom_w_deg" -> new ComparatorsVar<>(new WeightedDegree<>(store));
        case "impact" ->
            new ComparatorsVar<>(new ActivityMax<>(store), new MostConstrainedStatic<>());
        case "afc_max" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMax<>(store));
        case "afc_min" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMin<>(store));
        case "afc_max_deg" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMaxDeg<>(store));
        case "afc_min_deg" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new AfcMinDeg<>(store));
        case "activity_max" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMax<>(store));
        case "activity_min" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMin<>(store));
        case "activity_max_deg" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMaxDeg<>(store));
        case "activity_min_deg" ->
            // does not follow flatzinc standard (JaCoP specific) ;)
            new ComparatorsVar<>(new ActivityMinDeg<>(store));
        case "most_constrained" ->
            new ComparatorsVar<>(new MinGlbCard<>(), new MostConstrainedStatic<>());
        case "largest" -> new ComparatorsVar<>(new MaxLubCard<>());
        case "random" -> new ComparatorsVar<>(new RandomVar<>());
        default -> {
          System.err.println(
              "Warning: Not implemented variable selection heuristic \""
                  + var_selection_heuristic
                  + "\"; used input_order");

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

    if (Objects.equals(((ASTAnnotation) node).getAnnId(), "$vector")) {
      int count = node.jjtGetNumChildren();
      int[] aa = new int[count];
      for (int i = 0; i < count; i++) {
        SimpleNode n = (SimpleNode) node.jjtGetChild(i).jjtGetChild(0);
        ASTScalarFlatExpr child = (ASTScalarFlatExpr) n.jjtGetChild(0);
        int el = getInt(child);
        aa[i] = el;
      }
      return aa;
    } else if (Objects.equals(((ASTAnnotation) node).getAnnId(), "$expr")) {
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

    if (Objects.equals(((ASTAnnotation) node).getAnnId(), "$vector")) {
      int count = node.jjtGetNumChildren();
      IntVar[] aa = new IntVar[count];
      for (int i = 0; i < count; i++) {
        SimpleNode n = (SimpleNode) node.jjtGetChild(i).jjtGetChild(0);
        ASTScalarFlatExpr child = (ASTScalarFlatExpr) n.jjtGetChild(0);
        IntVar el = getVariable(child);
        aa[i] = el;
      }
      return aa;
    } else if (Objects.equals(((ASTAnnotation) node).getAnnId(), "$expr")) {
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

    if (Objects.equals(((ASTAnnotation) node).getAnnId(), "$vector")) {
      int count = node.jjtGetNumChildren();
      FloatVar[] aa = new FloatVar[count];
      for (int i = 0; i < count; i++) {
        SimpleNode n = (SimpleNode) node.jjtGetChild(i).jjtGetChild(0);
        ASTScalarFlatExpr child = (ASTScalarFlatExpr) n.jjtGetChild(0);
        FloatVar el = getFloatVariable(child);
        aa[i] = el;
      }
      return aa;
    } else if (Objects.equals(((ASTAnnotation) node).getAnnId(), "$expr")) {
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
      throw new IllegalArgumentException("Wrong parameter on list of search set varibales" + node);
    }
  }

  /**
   * Retrieves an array of set variables from a parse tree node.
   *
   * @param node the parse tree node
   * @return the array of set variables
   */
  SetVar[] getSetVarArray(SimpleNode node) {

    if (Objects.equals(((ASTAnnotation) node).getAnnId(), "$vector")) {
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
    } else if (Objects.equals(((ASTAnnotation) node).getAnnId(), "$expr")) {
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
    return search_type;
  }

  /**
   * Sets the search type.
   *
   * @param st the search type to set
   */
  public void setSearchType(String st) {
    search_type = st;
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
  public String var_selection() {
    return var_selection_heuristic;
  }

  /**
   * Returns the search variables.
   *
   * @return the array of search variables
   */
  public Var[] vars() {
    return search_variables;
  }

  /**
   * Returns the list of sub-search items.
   *
   * @return the list of search items
   */
  ArrayList<SearchItem<T>> getSearchItems() {
    return search_seq;
  }

  /**
   * Extracts the variable selection heuristic from an annotation.
   *
   * @param expr the annotation expression
   * @return the variable selection heuristic name
   */
  public String getVarSelectHeuristic(ASTAnnotation expr) {

    if ("$expr".equals(expr.getAnnId())) {
      return ((ASTScalarFlatExpr) expr.jjtGetChild(0).jjtGetChild(0)).getIdent();
    } else if (expr.getId() == JJTANNOTATION && "tiebreak".equals(expr.getAnnId())) {

      if (Objects.equals(((ASTAnnotation) expr.jjtGetChild(0)).getAnnId(), "$vector")) {

        int count = expr.jjtGetChild(0).jjtGetNumChildren();
        if (count >= 2) {
          String varSel1 =
              ((ASTScalarFlatExpr) expr.jjtGetChild(0).jjtGetChild(0).jjtGetChild(0).jjtGetChild(0))
                  .getIdent();

          var_selection_heuristic =
              ((ASTScalarFlatExpr) expr.jjtGetChild(0).jjtGetChild(1).jjtGetChild(0).jjtGetChild(0))
                  .getIdent();

          if ("int_search".equals(search_type) || "bool_search".equals(search_type)) {
            tieBreakingInt = getVarSelect().getVarSel();
          } else if ("set_search".equals(search_type)) {
            tieBreakingSet = getSetVarSelect().getVarSel();
          } else if ("float_search".equals(search_type)) {
            tieBreakingFloat = getFloatVarSelect().getVarSel();
          } else if ("priority_search".equals(search_type)) {
            tieBreakingInt = getVarSelect().getVarSel();
          }

          if (count > 2) {
            System.err.println(
                "% Warning: tiebreak annotation uses only two variable selection methods, the rest is ignored");
          }

          return varSel1;
        } else {
          throw new IllegalArgumentException(
              "tiebreak annotation must have two variable selection methods; compilation aborted.");
        }
      } else {
        throw new IllegalArgumentException(
            "Not supported Variable selection annotation; compilation aborted.");
      }
    } else {
      throw new IllegalArgumentException(
          "Not supported Variable selection annotation; compilation aborted.");
    }
  }

  /**
   * Adds a search item to the sequence.
   *
   * @param si the search item to add
   */
  public void addSearch(SearchItem<T> si) {
    search_seq.add(si);
  }

  /**
   * Returns the size of the search sequence.
   *
   * @return the number of search items in the sequence
   */
  public int search_seqSize() {
    return search_seq.size();
  }

  /** {@inheritDoc} */
  public String toString() {
    StringBuilder s = new StringBuilder();

    if (search_type == null) {
      s.append("defult_search\n");
    } else if (search_seq.isEmpty()) {
      s.append(search_type).append("(");
      if (search_variables == null) {
        s.append("[]");
      } else {
        s.append("array1d(1..")
            .append(search_variables.length)
            .append(", ")
            .append(Arrays.asList(search_variables));

        if ("warm_start".equals(search_type)) {
          s.append(", ").append(preferedValues);
        }
      }

      s.append(", ")
          .append(var_selection_heuristic)
          .append(", ")
          .append(indomain)
          .append(", ")
          .append(explore)
          .append(")");
      if (floatSearch) {
        s.append(", ").append(precision);
      }
    } else if (prioritySearch) {
      s.append("priority_search(");
      s.append("array1d(1..")
          .append(search_variables.length)
          .append(", ")
          .append(Arrays.asList(search_variables));

      s.append(", [");
      for (int i = 0; i < search_seq.size(); i++) {
        if (i == search_seq.size() - 1) {
          s.append(search_seq.get(i));
        } else {
          s.append(search_seq.get(i)).append(", ");
        }
      }
      s.append("]");

      s.append(", ").append(var_selection_heuristic).append(", ").append(explore).append(")");

      s.append(")");
    } else {
      s.append("seq_search([");
      for (int i = 0; i < search_seq.size(); i++) { // SearchItem se : search_seq)
        if (i == search_seq.size() - 1) {
          s.append(search_seq.get(i));
        } else {
          s.append(search_seq.get(i)).append(", ");
        }
      }
      s.append("])");
    }
    return s.toString();
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
    public String toString() {
      return "(" + v1 + ", " + v2 + ")";
    }
  }
}
