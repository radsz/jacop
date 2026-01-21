/*
 * SearchItem.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.fz;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
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
import org.jacop.search.AFCMax;
import org.jacop.search.AFCMaxDeg;
import org.jacop.search.AFCMin;
import org.jacop.search.AFCMinDeg;
import org.jacop.search.ActivityMax;
import org.jacop.search.ActivityMaxDeg;
import org.jacop.search.ActivityMin;
import org.jacop.search.ActivityMinDeg;
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
 * @version 4.10
 */
public class SearchItem<T extends Var> implements ParserTreeConstants {

  Tables dictionary;
  Store store;

  ArrayList<SearchItem<T>> search_seq = new ArrayList<SearchItem<T>>();
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

  // ComparatorVariable tieBreaking = null;
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

  void searchParameters(SimpleNode node, int n) {

    // node.dump("");

    ASTAnnotation ann = (ASTAnnotation) node.jjtGetChild(n);
    search_type = ann.getAnnId();

    if ("int_search".equals(search_type) || "bool_search".equals(search_type)) {
      SimpleNode expr1 = (SimpleNode) ann.jjtGetChild(0);
      search_variables = getVarArray(expr1);

      ASTAnnotation expr2 = (ASTAnnotation) ann.jjtGetChild(1);
      var_selection_heuristic = getVarSelectHeuristic(expr2);

      ASTAnnExpr expr3 = (ASTAnnExpr) ann.jjtGetChild(2).jjtGetChild(0);
      indomain = ((ASTScalarFlatExpr) expr3.jjtGetChild(0)).getIdent();

      ASTAnnotation expr4 = (ASTAnnotation) ann.jjtGetChild(3);
      explorationType(expr4);

    } else if ("set_search".equals(search_type)) {

      SimpleNode expr1 = (SimpleNode) ann.jjtGetChild(0);
      search_variables = getSetVarArray(expr1);

      ASTAnnotation expr2 = (ASTAnnotation) ann.jjtGetChild(1);
      var_selection_heuristic = getVarSelectHeuristic(expr2);

      ASTAnnExpr expr3 = (ASTAnnExpr) ann.jjtGetChild(2).jjtGetChild(0);
      indomain = ((ASTScalarFlatExpr) expr3.jjtGetChild(0)).getIdent();

      ASTAnnotation expr4 = (ASTAnnotation) ann.jjtGetChild(3);
      explorationType(expr4);

    } else if ("float_search".equals(search_type)) {
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

    } else if ("seq_search".equals(search_type)) {
      SimpleNode body = (SimpleNode) ann.jjtGetChild(0);
      search_type = "seq_search";

      makeVectorOfSearches(body);

    } else if ("warm_start".equals(search_type)) {

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
        IntVar var = (IntVar) search_variables[i];
        int val = values[i];

        if (var.domain.contains(val)) {
          if (preferedValues.get(var) != null && preferedValues.get(var) != val) {
            IO.println(
                "% Warning: Double defintion on warm_start for variable "
                    + var
                    + "("
                    + preferedValues.get(var)
                    + ", "
                    + val
                    + "), the first value is used.");
          } else {
            if ((var.max() - val) > (val - var.min())) {
              max++;
            } else {
              min++;
            }
            preferedValues.put(var, val);
          }
        } else {
          IO.println(
              "% Warning: warm_start value " + val + " is not in domain of " + var + "; ignored");
        }
      }

      var_selection_heuristic = "input_order";
      indomain = max > min ? "indomain_max" : "indomain_min";

    } else if ("priority_search".equals(search_type)) {
      // ann.dump("");

      prioritySearch = true;

      SimpleNode expr1 = (SimpleNode) ann.jjtGetChild(0);
      search_variables = getVarArray(expr1);

      SimpleNode searches = (SimpleNode) ann.jjtGetChild(1);
      makeVectorOfSearches(searches);
      // System.out.println(search_seq);

      ASTAnnotation expr2 = (ASTAnnotation) ann.jjtGetChild(2);
      var_selection_heuristic = getVarSelectHeuristic(expr2);

      ASTAnnotation expr3 = (ASTAnnotation) ann.jjtGetChild(3);
      explorationType(expr3);
      // System.out.println(explore);
      if (!"complete".equals(explore)) {
        System.err.println("Warning: not recognized search exploration type; use \"complete\"");
      }

    } else if ("restart_none".equals(search_type)) {
    } else if ("restart_constant".equals(search_type)) {
      ASTAnnExpr expr = (ASTAnnExpr) ann.jjtGetChild(0).jjtGetChild(0);
      int scale = ((ASTScalarFlatExpr) expr.jjtGetChild(0)).getInt();
      restartCalculator = new ConstantCalculator(scale);
    } else if ("restart_linear".equals(search_type)) {
      ASTAnnExpr expr = (ASTAnnExpr) ann.jjtGetChild(0).jjtGetChild(0);
      int scale = ((ASTScalarFlatExpr) expr.jjtGetChild(0)).getInt();
      restartCalculator = new LinearCalculator(scale);
    } else if ("restart_luby".equals(search_type)) {
      ASTAnnExpr expr = (ASTAnnExpr) ann.jjtGetChild(0).jjtGetChild(0);
      int scale = ((ASTScalarFlatExpr) expr.jjtGetChild(0)).getInt();
      restartCalculator = new LubyCalculator(scale);
    } else if ("restart_geometric".equals(search_type)) {
      ASTAnnExpr expr1 = (ASTAnnExpr) ann.jjtGetChild(0).jjtGetChild(0);
      double base = ((ASTScalarFlatExpr) expr1.jjtGetChild(0)).getFloat();
      ASTAnnExpr expr2 = (ASTAnnExpr) ann.jjtGetChild(1).jjtGetChild(0);
      int scale = ((ASTScalarFlatExpr) expr2.jjtGetChild(0)).getInt();
      restartCalculator = new GeometricCalculator(base, scale);
    } else if ("relax_and_reconstruct".equals(search_type)) {
      SimpleNode expr1 = (SimpleNode) ann.jjtGetChild(0);
      relax_and_reconstruct_variables = getVarArray(expr1);
      ASTAnnExpr expr2 = (ASTAnnExpr) ann.jjtGetChild(1).jjtGetChild(0);
      probability = ((ASTScalarFlatExpr) expr2.jjtGetChild(0)).getInt();

    } else {
      IO.println("% Warning: Ignored search annotation " + search_type);
    }

    //      throw new IllegalArgumentException("Not supported search annotation "+search_type+";
    // compilation aborted.");
  }

  void makeVectorOfSearches(SimpleNode body) {

    if (((ASTAnnotation) body).getAnnId() == "$vector") {

      int count = body.jjtGetNumChildren();

      for (int i = 0; i < count; i++) {
        SearchItem<T> subSearch = new SearchItem<>(store, dictionary);

        ASTAnnotation ann = (ASTAnnotation) body.jjtGetChild(i);
        // if (ann.getAnnId().equals("seq_search"))
        //      throw new RuntimeException("Error: Nested seq_search or seq_search in
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

  void explorationType(ASTAnnotation expr4) {
    if (expr4.getAnnId() == "$expr") {
      explore = ((ASTScalarFlatExpr) expr4.jjtGetChild(0).jjtGetChild(0)).getIdent();
    } else if ("credit".equals(expr4.getAnnId())) {
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
                // System.out.println("Credit("+creditValue+", "+bbsValue+")");
                return;
              }
            }
          }
        }
      }
      explore = "complete";
      System.err.println("Warning: not recognized search exploration type; use \"complete\"");
    } else if ("lds".equals(expr4.getAnnId())) {
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
    } else {
      throw new RuntimeException(
          "Error: not recognized search exploration type; execution aborted");
    }
  }

  void searchParametersForSeveralAnnotations(SimpleNode node, int n) {

    // node.dump("");

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

  // SelectChoicePoint getSelect() {
  //     if (search_type.equals("int_search") || search_type.equals("bool_search"))
  //         return getIntSelect();
  //     else if (search_type.equals("set_search"))
  //         return getSetSelect();
  //     else {
  //         throw new IllegalArgumentException("Error: not recognized search type \"" + search_type
  // + "\";");
  //     }
  // }

  @SuppressWarnings("unchecked")
  SelectChoicePoint<IntVar> getWarmStartSelect() {

    Indomain<IntVar> indom =
        "indomain_min".equals(indomain)
            ? new IndomainDefaultValue<IntVar>(preferedValues, new IndomainMin<IntVar>())
            : new IndomainDefaultValue<IntVar>(preferedValues, new IndomainMax<IntVar>());
    ArrayList<IntVar> sv = new ArrayList<>();
    for (int i = 0; i < search_variables.length; i++) {
      if (preferedValues.containsKey(search_variables[i])) {
        sv.add((IntVar) search_variables[i]);
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

    return new SimpleSelect<IntVar>(searchVars, var_sel, indom);
  }

  @SuppressWarnings("unchecked")
  SelectChoicePoint<IntVar> getIntSelect() {

    if ("random".equals(var_selection_heuristic)) {
      Indomain<IntVar> indom = getIndomain(indomain);
      IntVar[] searchVars = new IntVar[search_variables.length];
      for (int i = 0; i < search_variables.length; i++) {
        searchVars[i] = (IntVar) search_variables[i];
      }
      return new RandomSelect<IntVar>(searchVars, indom);
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
        return new SplitSelect<IntVar>(searchVars, var_sel, new IndomainMiddle<IntVar>());
      } else {
        return new SplitSelect<IntVar>(
            searchVars, var_sel, tieBreaking, new IndomainMiddle<IntVar>());
      }
    } else if ("indomain_split_random".equals(indomain)) {
      if (tieBreaking == null) {
        return new SplitRandomSelect<IntVar>(searchVars, var_sel, new IndomainMiddle<IntVar>());
      } else {
        return new SplitRandomSelect<IntVar>(
            searchVars, var_sel, tieBreaking, new IndomainMiddle<IntVar>());
      }
    } else if ("indomain_reverse_split".equals(indomain)) {
      if (tieBreaking == null) {
        SplitSelect<IntVar> sel =
            new SplitSelect<IntVar>(searchVars, var_sel, new IndomainMiddle<IntVar>());
        sel.leftFirst = false;
        return sel;
      } else {
        SplitSelect<IntVar> sel =
            new SplitSelect<IntVar>(searchVars, var_sel, tieBreaking, new IndomainMiddle<IntVar>());
        sel.leftFirst = false;
        return sel;
      }
    } else if ("outdomain_max".equals(indomain)) {
      if (tieBreaking == null) {
        SplitSelect<IntVar> sel =
            new SplitSelect<IntVar>(searchVars, var_sel, new IndomainMax<IntVar>());
        return sel;
      } else {
        SplitSelect<IntVar> sel =
            new SplitSelect<IntVar>(searchVars, var_sel, tieBreaking, new IndomainMax<IntVar>());
        return sel;
      }
    } else if ("outdomain_min".equals(indomain)) {
      if (tieBreaking == null) {
        SplitSelect<IntVar> sel =
            new SplitSelect<IntVar>(searchVars, var_sel, new IndomainMin<IntVar>());
        sel.leftFirst = false;
        return sel;
      } else {
        SplitSelect<IntVar> sel =
            new SplitSelect<IntVar>(searchVars, var_sel, tieBreaking, new IndomainMin<IntVar>());
        sel.leftFirst = false;
        return sel;
      }
    } else if ("input_order".equals(var_selection_heuristic)) {
      Indomain<IntVar> indom = getIndomain(indomain);
      return new InputOrderSelect<IntVar>(store, (IntVar[]) search_variables, indom);
    } else {
      Indomain<IntVar> indom = getIndomain(indomain);
      if (tieBreaking == null) {
        return new SimpleSelect<IntVar>((IntVar[]) search_variables, var_sel, indom);
      } else {
        return new SimpleSelect<IntVar>((IntVar[]) search_variables, var_sel, tieBreaking, indom);
      }
    }
  }

  @SuppressWarnings("unchecked")
  SelectChoicePoint<FloatVar> getFloatSelect() {

    ComparatorsVar<FloatVar> vs = getFloatVarSelect();
    ComparatorVariable<FloatVar> var_sel = vs.getVarSel();
    ComparatorVariable<FloatVar> tieBreaking =
        tieBreakingFloat == null ? vs.getTieSel() : tieBreakingFloat;
    FloatVar[] searchVars = new FloatVar[search_variables.length];
    for (int i = 0; i < search_variables.length; i++) {
      searchVars[i] = (FloatVar) search_variables[i];
    }

    if ("indomain_split".equals(indomain)) {
      if (tieBreaking == null) {
        return new SplitSelectFloat<FloatVar>(store, searchVars, var_sel);
      } else {
        return new SplitSelectFloat<FloatVar>(store, searchVars, var_sel, tieBreaking);
      }
    } else if ("indomain_split_random".equals(indomain)) {
      if (tieBreaking == null) {
        return new SplitRandomSelectFloat<FloatVar>(store, searchVars, var_sel);
      } else {
        return new SplitRandomSelectFloat<FloatVar>(store, searchVars, var_sel, tieBreaking);
      }
    } else if ("indomain_reverse_split".equals(indomain)) {
      if (tieBreaking == null) {
        SplitSelectFloat<FloatVar> sel = new SplitSelectFloat<FloatVar>(store, searchVars, var_sel);
        sel.leftFirst = false;
        return sel;
      } else {
        SplitSelectFloat<FloatVar> sel =
            new SplitSelectFloat<FloatVar>(store, searchVars, var_sel, tieBreaking);
        sel.leftFirst = false;
        return sel;
      }
    } else {
      throw new IllegalArgumentException(
          "Wrong parameters for float_search. Only indomain_split, indomain_reverse_split or indomain_split_random are allowed.");
    }
  }

  @SuppressWarnings("unchecked")
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
      return new SimpleSelect<SetVar>(searchVars, var_sel, indom);
    } else {
      return new SimpleSelect<SetVar>(searchVars, var_sel, tieBreaking, indom);
    }
  }

  Indomain<SetVar> getIndomain4Set(String indomain) {

    if (indomain == null) {
      return new IndomainSetMin<SetVar>();
    } else {
      switch (indomain) {
        case "indomain_min":
          return new IndomainSetMin<SetVar>();
        case "indomain_max":
          return new IndomainSetMax<SetVar>();
        case "indomain_random":
          return new IndomainSetRandom<SetVar>();
        default:
          System.err.println(
              "Warning: Not implemented indomain method \"" + indomain + "\"; used indomain_min");
          return new IndomainSetMin<SetVar>();
      }
    }
  }

  Indomain<IntVar> getIndomain(String indomain) {
    if (indomain == null) {
      return new IndomainMin<IntVar>();
    } else {
      switch (indomain) {
        case "indomain_min":
          return new IndomainMin<IntVar>();
        case "indomain_max":
          return new IndomainMax<IntVar>();
        case "indomain_middle":
          return new IndomainMiddle<IntVar>();
        case "indomain_median":
          return new IndomainMedian<IntVar>();
        case "indomain_random":
          return new IndomainRandom<IntVar>();
        default:
          System.err.println(
              "Warning: Not implemented indomain method \"" + indomain + "\"; used indomain_min");
          return new IndomainMin<IntVar>();
      }
    }
  }

  public ComparatorsVar<IntVar> getVarSelect() {

    if (var_selection_heuristic == null) {
      return new ComparatorsVar<IntVar>(null);
    } else {
      switch (var_selection_heuristic) {
        case "input_order":
          return new ComparatorsVar<IntVar>(null);
        case "random":
          return new ComparatorsVar<IntVar>(new RandomVar<IntVar>());
        case "first_fail":
          return new ComparatorsVar<IntVar>(new SmallestDomain<IntVar>());
        case "anti_first_fail":
          return new ComparatorsVar<IntVar>(new LargestDomain<IntVar>());
        case "most_constrained":
          return new ComparatorsVar<IntVar>(
              new SmallestDomain<IntVar>(), new MostConstrainedStatic<IntVar>());
        case "occurrence":
          return new ComparatorsVar<IntVar>(new MostConstrainedStatic<IntVar>());
        case "smallest":
          return new ComparatorsVar<IntVar>(new SmallestMin<IntVar>());
        case "largest":
          return new ComparatorsVar<IntVar>(new LargestMax<IntVar>());
        case "max_regret":
          return new ComparatorsVar<IntVar>(new MaxRegret<IntVar>());
        case "impact":
          return new ComparatorsVar<IntVar>(
              new ActivityMax<IntVar>(store), new MostConstrainedStatic<IntVar>());
        case "dom_w_deg":
          return new ComparatorsVar<IntVar>(new WeightedDegree<IntVar>(store));
        case "smallest_max":
          return new ComparatorsVar<IntVar>(
              new SmallestMax<IntVar>(), new SmallestDomain<IntVar>());
        case "smallest_most_constrained":
          return new ComparatorsVar<IntVar>(
              new SmallestMin<IntVar>(), new MostConstrainedStatic<IntVar>());
        case "smallest_first_fail":
          return new ComparatorsVar<IntVar>(
              new SmallestMin<IntVar>(), new SmallestDomain<IntVar>());
        case "afc_max":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<IntVar>(new AFCMax<IntVar>(store));
        case "afc_min":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<IntVar>(new AFCMin<IntVar>(store));
        case "afc_max_deg":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<IntVar>(new AFCMaxDeg<IntVar>(store));
        case "afc_min_deg":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<IntVar>(new AFCMinDeg<IntVar>(store));
        case "activity_max":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<IntVar>(new ActivityMax<IntVar>(store));
        case "activity_min":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<IntVar>(new ActivityMin<IntVar>(store));
        case "activity_max_deg":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<IntVar>(new ActivityMaxDeg<IntVar>(store));
        case "activity_min_deg":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<IntVar>(new ActivityMinDeg<IntVar>(store));
        default:
          System.err.println(
              "Warning: Not implemented variable selection heuristic \""
                  + var_selection_heuristic
                  + "\"; used input_order");

          return null; // input_order
      }
    }
  }

  public ComparatorsVar<FloatVar> getFloatVarSelect() {

    if (var_selection_heuristic == null) {
      return new ComparatorsVar<FloatVar>(null);
    } else {
      switch (var_selection_heuristic) {
        case "input_order":
          return new ComparatorsVar<FloatVar>(null);
        case "first_fail":
          return new ComparatorsVar<FloatVar>(new SmallestDomainFloat<FloatVar>());
        case "anti_first_fail":
          return new ComparatorsVar<FloatVar>(new LargestDomainFloat<FloatVar>());
        case "most_constrained":
          return new ComparatorsVar<FloatVar>(
              new SmallestDomainFloat<FloatVar>(), new MostConstrainedStatic<FloatVar>());
        case "occurrence":
          return new ComparatorsVar<FloatVar>(new MostConstrainedStatic<FloatVar>());
        case "smallest":
          return new ComparatorsVar<FloatVar>(new SmallestMinFloat<FloatVar>());
        case "largest":
          return new ComparatorsVar<FloatVar>(new LargestMaxFloat<FloatVar>());
        case "max_regret":
          return new ComparatorsVar<FloatVar>(new MaxRegretFloat<FloatVar>());
        case "dom_w_deg":
          return new ComparatorsVar<FloatVar>(new WeightedDegree<FloatVar>(store));
        case "impact":
          return new ComparatorsVar<FloatVar>(
              new ActivityMax<FloatVar>(store), new MostConstrainedStatic<FloatVar>());
        case "afc_max":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<FloatVar>(new AFCMax<FloatVar>(store));
        case "afc_max_deg":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<FloatVar>(new AFCMaxDeg<FloatVar>(store));
        case "afc_min":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<FloatVar>(new AFCMin<FloatVar>(store));
        case "afc_min_deg":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<FloatVar>(new AFCMinDeg<FloatVar>(store));
        case "activity_max":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<FloatVar>(new ActivityMax<FloatVar>(store));
        case "activity_max_deg":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<FloatVar>(new ActivityMaxDeg<FloatVar>(store));
        case "activity_min":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<FloatVar>(new ActivityMin<FloatVar>(store));
        case "activity_min_deg":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<FloatVar>(new ActivityMinDeg<FloatVar>(store));
        // for FloatVar's getSize() is not defined :(
        // afc*_deg and activity*_deg cannot be used
        case "random":
          return new ComparatorsVar<FloatVar>(new RandomVar<FloatVar>());
        default:
          System.err.println(
              "Warning: Not implemented variable selection heuristic \""
                  + var_selection_heuristic
                  + "\"; used input_order");

          return new ComparatorsVar<FloatVar>(null); // input_order
      }
    }
  }

  ComparatorsVar<SetVar> getSetVarSelect() {

    if (var_selection_heuristic == null) {
      return new ComparatorsVar<SetVar>(null);
    } else {
      switch (var_selection_heuristic) {
        case "input_order":
          return new ComparatorsVar<SetVar>(null);
        case "first_fail":
          return new ComparatorsVar<SetVar>(new MinCardDiff<SetVar>());
        case "smallest":
          return new ComparatorsVar<SetVar>(new MinGlbCard<SetVar>());
        case "occurrence":
          return new ComparatorsVar<SetVar>(new MostConstrainedStatic<SetVar>());
        case "anti_first_fail":
          return new ComparatorsVar<SetVar>(new MaxCardDiff<SetVar>());
        case "dom_w_deg":
          return new ComparatorsVar<SetVar>(new WeightedDegree<SetVar>(store));
        case "impact":
          return new ComparatorsVar<SetVar>(
              new ActivityMax<SetVar>(store), new MostConstrainedStatic<SetVar>());
        case "afc_max":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<SetVar>(new AFCMax<SetVar>(store));
        case "afc_min":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<SetVar>(new AFCMin<SetVar>(store));
        case "afc_max_deg":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<SetVar>(new AFCMaxDeg<SetVar>(store));
        case "afc_min_deg":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<SetVar>(new AFCMinDeg<SetVar>(store));
        case "activity_max":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<SetVar>(new ActivityMax<SetVar>(store));
        case "activity_min":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<SetVar>(new ActivityMin<SetVar>(store));
        case "activity_max_deg":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<SetVar>(new ActivityMaxDeg<SetVar>(store));
        case "activity_min_deg":
          // does not follow flatzinc standard (JaCoP specific) ;)
          return new ComparatorsVar<SetVar>(new ActivityMinDeg<SetVar>(store));
        case "most_constrained":
          return new ComparatorsVar<SetVar>(
              new MinGlbCard<SetVar>(), new MostConstrainedStatic<SetVar>());
        case "largest":
          return new ComparatorsVar<SetVar>(new MaxLubCard<SetVar>());
        //  case"max_regret":
        //      return new ComparatorsVar<SetVar>(new MaxRegret());
        case "random":
          return new ComparatorsVar<SetVar>(new RandomVar<SetVar>());
        default:
          System.err.println(
              "Warning: Not implemented variable selection heuristic \""
                  + var_selection_heuristic
                  + "\"; used input_order");

          return new ComparatorsVar<SetVar>(null); // input_order
      }
    }
  }

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

  int[] getIntArray(SimpleNode node) {

    if (((ASTAnnotation) node).getAnnId() == "$vector") {
      int count = node.jjtGetNumChildren();
      int[] aa = new int[count];
      for (int i = 0; i < count; i++) {
        SimpleNode n = (SimpleNode) node.jjtGetChild(i).jjtGetChild(0);
        ASTScalarFlatExpr child = (ASTScalarFlatExpr) n.jjtGetChild(0);
        int el = getInt(child);
        aa[i] = el;
      }
      return aa;
    } else if (((ASTAnnotation) node).getAnnId() == "$expr") {
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

  IntVar[] getVarArray(SimpleNode node) {

    if (((ASTAnnotation) node).getAnnId() == "$vector") {
      int count = node.jjtGetNumChildren();
      IntVar[] aa = new IntVar[count];
      for (int i = 0; i < count; i++) {
        SimpleNode n = (SimpleNode) node.jjtGetChild(i).jjtGetChild(0);
        ASTScalarFlatExpr child = (ASTScalarFlatExpr) n.jjtGetChild(0);
        IntVar el = getVariable(child);
        aa[i] = el;
      }
      return aa;
    } else if (((ASTAnnotation) node).getAnnId() == "$expr") {
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

  FloatVar[] getFloatVarArray(SimpleNode node) {

    if (((ASTAnnotation) node).getAnnId() == "$vector") {
      int count = node.jjtGetNumChildren();
      FloatVar[] aa = new FloatVar[count];
      for (int i = 0; i < count; i++) {
        SimpleNode n = (SimpleNode) node.jjtGetChild(i).jjtGetChild(0);
        ASTScalarFlatExpr child = (ASTScalarFlatExpr) n.jjtGetChild(0);
        FloatVar el = getFloatVariable(child);
        aa[i] = el;
      }
      return aa;
    } else if (((ASTAnnotation) node).getAnnId() == "$expr") {
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

  SetVar getSetVariable(ASTScalarFlatExpr node) {
    if (node.getType() == 2) { // ident
      return dictionary.getSetVariable(node.getIdent());
    } else if (node.getType() == 3) { // array access
      return dictionary.getSetVariableArray(node.getIdent())[node.getInt()];
    } else {
      throw new IllegalArgumentException("Wrong parameter on list of search set varibales" + node);
    }
  }

  SetVar[] getSetVarArray(SimpleNode node) {

    if (((ASTAnnotation) node).getAnnId() == "$vector") {
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
    } else if (((ASTAnnotation) node).getAnnId() == "$expr") {
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

  public String type() {
    return search_type;
  }

  public void setSearchType(String st) {
    search_type = st;
  }

  public String exploration() {
    return explore;
  }

  public String indomain() {
    return indomain;
  }

  public String var_selection() {
    return var_selection_heuristic;
  }

  public Var[] vars() {
    return search_variables;
  }

  ArrayList<SearchItem<T>> getSearchItems() {
    return search_seq;
  }

  public String getVarSelectHeuristic(ASTAnnotation expr) {

    if ("$expr".equals(expr.getAnnId())) {
      return ((ASTScalarFlatExpr) expr.jjtGetChild(0).jjtGetChild(0)).getIdent();
    } else if (expr.getId() == JJTANNOTATION && "tiebreak".equals(expr.getAnnId())) {

      if (((ASTAnnotation) expr.jjtGetChild(0)).getAnnId() == "$vector") {

        int count = ((ASTAnnotation) expr.jjtGetChild(0)).jjtGetNumChildren();
        if (count >= 2) {
          String varSel1 =
              ((ASTScalarFlatExpr) expr.jjtGetChild(0).jjtGetChild(0).jjtGetChild(0).jjtGetChild(0))
                  .getIdent();
          String varSel2 =
              ((ASTScalarFlatExpr) expr.jjtGetChild(0).jjtGetChild(1).jjtGetChild(0).jjtGetChild(0))
                  .getIdent();

          var_selection_heuristic = varSel2;

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

  public void addSearch(SearchItem<T> si) {
    search_seq.add(si);
  }

  public int search_seqSize() {
    return search_seq.size();
  }

  public String toString() {
    StringBuffer s = new StringBuffer();

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

  public static class ComparatorsVar<T extends Var> {
    ComparatorVariable<T> v1;
    ComparatorVariable<T> v2;

    public ComparatorsVar(ComparatorVariable<T> v1, ComparatorVariable<T> v2) {
      this.v1 = v1;
      this.v2 = v2;
    }

    public ComparatorsVar(ComparatorVariable<T> v1) {
      this.v1 = v1;
      this.v2 = null;
    }

    public ComparatorVariable<T> getVarSel() {
      return v1;
    }

    public ComparatorVariable<T> getTieSel() {
      return v2;
    }

    public String toString() {
      return "(" + v1 + ", " + v2 + ")";
    }
  }
}
