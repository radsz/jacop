/**
 *  SearchItem.java 
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
package org.jacop.fz;

import java.util.ArrayList;
import java.util.Arrays;

import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.floats.core.FloatVar;
import org.jacop.search.ComparatorVariable;
import org.jacop.search.Indomain;
import org.jacop.search.IndomainMax;
import org.jacop.search.IndomainMedian;
import org.jacop.search.IndomainMiddle;
import org.jacop.search.IndomainMin;
import org.jacop.search.IndomainRandom;
import org.jacop.search.LargestDomain;
import org.jacop.search.LargestMax;
import org.jacop.search.MaxRegret;
import org.jacop.search.MostConstrainedStatic;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import org.jacop.search.SmallestMin;
import org.jacop.search.SplitSelect;
import org.jacop.search.WeightedDegree;
import org.jacop.floats.search.SmallestDomainFloat;
import org.jacop.floats.search.LargestDomainFloat;
import org.jacop.floats.search.SmallestMinFloat;
import org.jacop.floats.search.LargestMaxFloat;
import org.jacop.floats.search.SplitSelectFloat;
import org.jacop.set.core.SetVar;
import org.jacop.set.search.IndomainSetMax;
import org.jacop.set.search.IndomainSetMin;
import org.jacop.set.search.MaxCardDiff;
import org.jacop.set.search.MinCardDiff;
import org.jacop.set.search.MinGlbCard;
import org.jacop.set.search.MaxLubCard;


/**
 * 
 * The part of the parser responsible for parsing search part of the flatzinc specification. 
 * 
 * @author Krzysztof Kuchcinski
 *
 */
public class SearchItem implements ParserTreeConstants {

    Tables dictionary;
    Store store;

    ArrayList<SearchItem> search_seq = new ArrayList<SearchItem>();
    Var[] search_variables;
    String search_type, explore="complete", indomain, var_selection_heuristic;

    boolean floatSearch = false;
    double precision = 0.0; // for float_search

    int ldsValue = 0, creditValue = 0, bbsValue = 0;

    ComparatorVariable tieBreaking=null;

    /**
     * It constructs search part parsing object based on dictionaries
     * provided as well as store object within which the search will take place. 
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

	ASTAnnotation ann = (ASTAnnotation)node.jjtGetChild(n);
	search_type = ann.getAnnId();

	if (search_type.equals("int_search") || search_type.equals("bool_search")) {
	    ASTAnnExpr expr1 = (ASTAnnExpr)ann.jjtGetChild(0);
	    search_variables = getVarArray((SimpleNode)expr1.jjtGetChild(0));

	    ASTAnnExpr expr2 = (ASTAnnExpr)ann.jjtGetChild(1);
	    var_selection_heuristic = ((ASTScalarFlatExpr)expr2.jjtGetChild(0)).getIdent();

	    ASTAnnExpr expr3 = (ASTAnnExpr)ann.jjtGetChild(2);
	    indomain = ((ASTScalarFlatExpr)expr3.jjtGetChild(0)).getIdent();

	    ASTAnnExpr expr4 = (ASTAnnExpr)ann.jjtGetChild(3);
	    if (! expr4.idPresent()) //(expr4.jjtGetNumChildren() == 1)
		explore = ((ASTScalarFlatExpr)expr4.jjtGetChild(0)).getIdent();
	    else if (expr4.getIdent().equals("credit")) {
		explore = "credit";
		if (expr4.jjtGetNumChildren() == 2) {
		    if (((SimpleNode)expr4.jjtGetChild(0)).getId() == JJTANNEXPR) {
			ASTAnnExpr cp = (ASTAnnExpr)expr4.jjtGetChild(0);
			if (cp.jjtGetNumChildren() == 1) {
			    creditValue = ((ASTScalarFlatExpr)cp.jjtGetChild(0)).getInt();
			}
		    }
		    ASTAnnExpr bbs = (ASTAnnExpr)expr4.jjtGetChild(1);
		    if (bbs.getId() == JJTANNEXPR && bbs.getIdent().equals("bbs")) {
			if (bbs.jjtGetNumChildren() == 1) {
			    if (((SimpleNode)bbs.jjtGetChild(0)).getId() == JJTANNEXPR) {
				ASTAnnExpr bv = (ASTAnnExpr)bbs.jjtGetChild(0);
				if (bv.jjtGetNumChildren() == 1) {
				    bbsValue = ((ASTScalarFlatExpr)bv.jjtGetChild(0)).getInt();
				    //  				    System.out.println("Credit("+creditValue+", "+bbsValue+")");
				    return;
				}
			    }
			}
		    }
		}
		explore = "complete";
		System.err.println("Warning: not recognized search exploration type; use \"complete\"");
	    }
	    else if  (expr4.getIdent().equals("lds")) {
		explore = "lds";
		if (expr4.jjtGetNumChildren() == 1) {
		    if (((SimpleNode)expr4.jjtGetChild(0)).getId() == JJTANNEXPR) {
			ASTAnnExpr ae = (ASTAnnExpr)expr4.jjtGetChild(0);
			if (ae.jjtGetNumChildren() == 1) {
			    ldsValue = ((ASTScalarFlatExpr)ae.jjtGetChild(0)).getInt();
			    return;
			}
		    }
		}
		explore = "complete";
		System.err.println("Warning: not recognized search exploration type; use \"complete\"");
	    }
	    else {
		System.err.println("Error: not recognized search exploration type; execution aborted");
		System.exit(0);
	    }
	}
	else if (search_type.equals("set_search")) {

	    ASTAnnExpr expr1 = (ASTAnnExpr)ann.jjtGetChild(0);
	    search_variables = getSetVarArray((SimpleNode)expr1.jjtGetChild(0));

	    ASTAnnExpr expr2 = (ASTAnnExpr)ann.jjtGetChild(1);
	    var_selection_heuristic = ((ASTScalarFlatExpr)expr2.jjtGetChild(0)).getIdent();

	    ASTAnnExpr expr3 = (ASTAnnExpr)ann.jjtGetChild(2);
	    indomain = ((ASTScalarFlatExpr)expr3.jjtGetChild(0)).getIdent();

	    ASTAnnExpr expr4 = (ASTAnnExpr)ann.jjtGetChild(3);
	    if (! expr4.idPresent())  //(expr4.jjtGetNumChildren() == 1)
		explore = ((ASTScalarFlatExpr)expr4.jjtGetChild(0)).getIdent();
	    else if  (expr4.getIdent().equals("credit")) {
		// 		explore = expr4.getIdent();
		explore = "complete";
		System.err.println("Warning: not recognized search exploration type; use \"complete\"");
		// 		System.exit(0);
	    }
	    else if  (expr4.getIdent().equals("lds")){
		explore = "lds";
		if (expr4.jjtGetNumChildren() == 1) {
		    if (((SimpleNode)expr4.jjtGetChild(0)).getId() == JJTANNEXPR) {
			ASTAnnExpr ae = (ASTAnnExpr)expr4.jjtGetChild(0);
			if (ae.jjtGetNumChildren() == 1) {
			    ldsValue = ((ASTScalarFlatExpr)ae.jjtGetChild(0)).getInt();
			    return;
			}
		    }
		}
		explore = "complete";
		System.err.println("Warning: not recognized search exploration type; use \"complete\"");
	    }
	    else {
		System.err.println("Error: not recognized search exploration type; execution aborted");
		System.exit(0);
	    }
	}

	if (search_type.equals("float_search")) {
	    floatSearch = true;

	    ASTAnnExpr expr1 = (ASTAnnExpr)ann.jjtGetChild(0);
	    search_variables = getFloatVarArray((SimpleNode)expr1.jjtGetChild(0));

	    ASTAnnExpr expr2 = (ASTAnnExpr)ann.jjtGetChild(2);
	    var_selection_heuristic = ((ASTScalarFlatExpr)expr2.jjtGetChild(0)).getIdent();

	    ASTAnnExpr expr3 = (ASTAnnExpr)ann.jjtGetChild(3);
	    indomain = ((ASTScalarFlatExpr)expr3.jjtGetChild(0)).getIdent();


	    ASTAnnExpr expr4 = (ASTAnnExpr)ann.jjtGetChild(4);
	    if (! expr4.idPresent()) //(expr4.jjtGetNumChildren() == 1)
		explore = ((ASTScalarFlatExpr)expr4.jjtGetChild(0)).getIdent();
	    else if (expr4.getIdent().equals("credit")) {
		explore = "credit";
		if (expr4.jjtGetNumChildren() == 2) {
		    if (((SimpleNode)expr4.jjtGetChild(0)).getId() == JJTANNEXPR) {
			ASTAnnExpr cp = (ASTAnnExpr)expr4.jjtGetChild(0);
			if (cp.jjtGetNumChildren() == 1) {
			    creditValue = ((ASTScalarFlatExpr)cp.jjtGetChild(0)).getInt();
			}
		    }
		    ASTAnnExpr bbs = (ASTAnnExpr)expr4.jjtGetChild(1);
		    if (bbs.getId() == JJTANNEXPR && bbs.getIdent().equals("bbs")) {
			if (bbs.jjtGetNumChildren() == 1) {
			    if (((SimpleNode)bbs.jjtGetChild(0)).getId() == JJTANNEXPR) {
				ASTAnnExpr bv = (ASTAnnExpr)bbs.jjtGetChild(0);
				if (bv.jjtGetNumChildren() == 1) {
				    bbsValue = ((ASTScalarFlatExpr)bv.jjtGetChild(0)).getInt();
				    //  				    System.out.println("Credit("+creditValue+", "+bbsValue+")");
				    return;
				}
			    }
			}
		    }
		}
		explore = "complete";
		System.err.println("Warning: not recognized search exploration type; use \"complete\"");
	    }
	    else if  (expr4.getIdent().equals("lds")) {
		explore = "lds";
		if (expr4.jjtGetNumChildren() == 1) {
		    if (((SimpleNode)expr4.jjtGetChild(0)).getId() == JJTANNEXPR) {
			ASTAnnExpr ae = (ASTAnnExpr)expr4.jjtGetChild(0);
			if (ae.jjtGetNumChildren() == 1) {
			    ldsValue = ((ASTScalarFlatExpr)ae.jjtGetChild(0)).getInt();
			    return;
			}
		    }
		}
		explore = "complete";
		System.err.println("Warning: not recognized search exploration type; use \"complete\"");
	    }
	    else {
		System.err.println("Error: not recognized search exploration type; execution aborted");
		System.exit(0);
	    }

	    ASTAnnExpr expr5 = (ASTAnnExpr)ann.jjtGetChild(1);
	    precision = ((ASTScalarFlatExpr)expr5.jjtGetChild(0)).getFloat();

	}
	else if (search_type.equals("seq_search")) {
	    int count = ann.jjtGetNumChildren();
	    for (int i=0; i<count; i++) {
		SearchItem subSearch = new SearchItem(store, dictionary);
		subSearch.searchParameters(ann, i);
		search_seq.add(subSearch);
	    }
	}
    }

    void searchParametersForSeveralAnnotations(SimpleNode node, int n) {
	
//  	node.dump("");

	int count = node.jjtGetNumChildren();

	for (int i=0; i<count-1; i++) {
	    SearchItem subSearch = new SearchItem(store, dictionary);
	    subSearch.searchParameters(node, i);
	    search_seq.add(subSearch);
	}
    }

    SelectChoicePoint getSelect() {
	if (search_type.equals("int_search") || search_type.equals("bool_search"))
	    return getIntSelect();
	else if (search_type.equals("set_search"))
	    return getSetSelect();
	else {
	    System.err.println("Error: not recognized search type \""+ search_type+"\";");
	    System.exit(0);
	    return null;
	}
    }

    SelectChoicePoint getIntSelect() {
	ComparatorVariable<IntVar> var_sel = getVarSelect();
	IntVar[] searchVars = new IntVar[search_variables.length];
	for (int i = 0; i < search_variables.length; i++)
		searchVars[i] = (IntVar) search_variables[i];

	if (indomain != null && indomain.equals("indomain_split")) {
	    if (tieBreaking == null)
		return new SplitSelect<IntVar>(searchVars, var_sel, new IndomainMiddle<IntVar>());
	    else
		return new SplitSelect<IntVar>( searchVars, var_sel, tieBreaking, new IndomainMiddle<IntVar>());
	}
	else if (indomain != null && indomain.equals("indomain_reverse_split")) {
	    if (tieBreaking == null) {
		SplitSelect<IntVar> sel = new SplitSelect<IntVar>(searchVars, var_sel, new IndomainMiddle<IntVar>());
		sel.leftFirst = false;
		return sel;
	    }
	    else {
		SplitSelect<IntVar> sel = new SplitSelect<IntVar>( searchVars, var_sel, tieBreaking, new IndomainMiddle<IntVar>());
		sel.leftFirst = false;
		return sel;
	    }
	}
	else {
	    Indomain indom = getIndomain(indomain);
	    if (tieBreaking == null)
		return new SimpleSelect(search_variables, var_sel, indom);
	    else
		return new SimpleSelect(search_variables, var_sel, tieBreaking, indom);
	}
    }

    SelectChoicePoint getFloatSelect() {
	ComparatorVariable<FloatVar> var_sel = getFloatVarSelect();
	FloatVar[] searchVars = new FloatVar[search_variables.length];
	for (int i = 0; i < search_variables.length; i++)
		searchVars[i] = (FloatVar) search_variables[i];

	if (indomain.equals("indomain_split")) {
	    if (tieBreaking == null)
		return new SplitSelectFloat<FloatVar>(store, searchVars, var_sel);
	    else
		return new SplitSelectFloat<FloatVar>(store,  searchVars, var_sel, tieBreaking);
	}
	else if (indomain.equals("indomain_reverse_split")) {
	    if (tieBreaking == null) {
		SplitSelectFloat<FloatVar> sel = new SplitSelectFloat<FloatVar>(store, searchVars, var_sel);
		sel.leftFirst = false;
		return sel;
	    }
	    else {
		SplitSelectFloat<FloatVar> sel = new SplitSelectFloat<FloatVar>(store,  searchVars, var_sel, tieBreaking);
		sel.leftFirst = false;
		return sel;
	    }
	}
	else {
	    System.err.println("Wrong parameters for float_search. Only indomain_split or indomain_reverse_split are allowed.");
	    System.exit(0);
	    return null;
	}
    }


    SelectChoicePoint getSetSelect() {
	ComparatorVariable<SetVar> var_sel = getsetVarSelect();
	Indomain<SetVar> indom = getIndomain4Set(indomain);
	SetVar[] searchVars = new SetVar[search_variables.length];
	for (int i = 0; i < search_variables.length; i++)
		searchVars[i] = (SetVar) search_variables[i];
	
	if (tieBreaking == null)
	    return new SimpleSelect<SetVar>((SetVar[])searchVars, var_sel, indom);
	else
	    return new SimpleSelect<SetVar>((SetVar[])searchVars, var_sel, tieBreaking, indom);
    }

    Indomain<SetVar> getIndomain4Set(String indomain) {

	if (indomain == null)
	    return new IndomainSetMin<SetVar>();
	else if (indomain.equals("indomain_min")) 
	    return new IndomainSetMin<SetVar>();
	else if (indomain.equals("indomain_max")) 
	    return new IndomainSetMax();
// 	else if (indomain.equals("indomain_middle")) 
// 	    return new IndomainSetMiddle();
// 	else if (indomain.equals("indomain_random")) 
// 	    return new IndomainSetRandom();
	else 
	    System.err.println("Warning: Not implemented indomain method \""+ 
			       indomain +"\"; used indomain_min");
	return new IndomainSetMin<SetVar>();
    }

    
    
    Indomain getIndomain(String indomain) {
	if (indomain == null)
	    return new IndomainMin();
	else if (indomain.equals("indomain_min")) 
	    return new IndomainMin();
	else if (indomain.equals("indomain_max")) 
	    return new IndomainMax();
	else if (indomain.equals("indomain_middle")) 
	    return new IndomainMiddle();
	else if (indomain.equals("indomain_median")) 
	    return new IndomainMedian();
	else if (indomain.equals("indomain_random")) 
	    return new IndomainRandom();
	else
	    System.err.println("Warning: Not implemented indomain method \""+ 
			       indomain +"\"; used indomain_min");
	return new IndomainMin();
    }

    
    public ComparatorVariable getVarSelect() {

	tieBreaking = null;
	if (var_selection_heuristic == null)
	    return null;
	else if (var_selection_heuristic.equals("input_order"))
	    return null;
	else if (var_selection_heuristic.equals("first_fail")) 
 	    return new SmallestDomain();
	else if (var_selection_heuristic.equals("anti_first_fail")) {
	    // does not follow flatzinc definition but may give better results ;)
	    //tieBreaking = new MostConstrainedStatic();
	    return new LargestDomain();
	}
	else if (var_selection_heuristic.equals("most_constrained")) {
	    //tieBreaking = new MostConstrainedStatic();
	    return new SmallestDomain();
	}
	else if (var_selection_heuristic.equals("occurrence"))
	    return new MostConstrainedStatic();
	else if (var_selection_heuristic.equals("smallest")) {
	    // does not follow flatzinc definition but may give better results ;)
 	    // tieBreaking = new MostConstrainedStatic(); 
	    //tieBreaking = new SmallestDomain();
	    return new SmallestMin();
	}
	else if (var_selection_heuristic.equals("largest"))
	    return new LargestMax();
	else if (var_selection_heuristic.equals("max_regret"))
	    return new MaxRegret();
	else if (var_selection_heuristic.equals("weighted_degree")) {
	    store.variableWeightManagement = true;
	    return new WeightedDegree();
	}
	else 
	    System.err.println("Warning: Not implemented variable selection heuristic \""+
			       var_selection_heuristic +"\"; used input_order");

	return null; // input_order
    }

    public ComparatorVariable getFloatVarSelect() {

	tieBreaking = null;
	if (var_selection_heuristic == null)
	    return null;
	else if (var_selection_heuristic.equals("input_order"))
	    return null;
	else if (var_selection_heuristic.equals("first_fail")) 
 	    return new SmallestDomainFloat();
	else if (var_selection_heuristic.equals("anti_first_fail")) {
	    // does not follow flatzinc definition but may give better results ;)
	    //tieBreaking = new MostConstrainedStatic();
	    return new LargestDomainFloat();
	}
	// else if (var_selection_heuristic.equals("most_constrained")) {
	//     //tieBreaking = new MostConstrainedStatic();
	//     return new SmallestDomainFloat();
	// }
	else if (var_selection_heuristic.equals("occurrence"))
	    return new MostConstrainedStatic();
	else if (var_selection_heuristic.equals("smallest")) {
	    // does not follow flatzinc definition but may give better results ;)
 	    // tieBreaking = new MostConstrainedStatic(); 
	    //tieBreaking = new SmallestDomain();
	    return new SmallestMinFloat();
	}
	else if (var_selection_heuristic.equals("largest"))
	    return new LargestMaxFloat();
	// else if (var_selection_heuristic.equals("max_regret"))
	//     return new MaxRegret();
	// else if (var_selection_heuristic.equals("weighted_degree")) {
	//     store.variableWeightManagement = true;
	//     return new WeightedDegree();
	// }
	else 
	    System.err.println("Warning: Not implemented variable selection heuristic \""+
			       var_selection_heuristic +"\"; used input_order");

	return null; // input_order
    }

    ComparatorVariable getsetVarSelect() {

	tieBreaking = null;
	if (var_selection_heuristic == null)
	    return null;
	else if (var_selection_heuristic.equals("input_order"))
	    return null;
	else if (var_selection_heuristic.equals("first_fail"))
	    return new MinCardDiff();
	else if (var_selection_heuristic.equals("smallest"))
	    return new MinGlbCard();
	else if (var_selection_heuristic.equals("occurrence"))
	    return new MostConstrainedStatic();
	else if (var_selection_heuristic.equals("anti_first_fail"))
	    return new MaxCardDiff();
	else if (var_selection_heuristic.equals("weighted_degree")) {
	    store.variableWeightManagement = true;
	    return new WeightedDegree();
	}
	//  	else if (var_selection_heuristic.equals("most_constrained")) {
	// 	    tieBreaking = new MostConstrainedStatic();
	//  	    return new SmallestDomain();
	// 	}
	else if (var_selection_heuristic.equals("largest"))
	    return new MaxLubCard();
	// 	else if (var_selection_heuristic.equals("max_regret"))
	// 	    return new MaxRegret();
	else 
	    System.err.println("Warning: Not implemented variable selection heuristic \""+
			       var_selection_heuristic +"\"; used input_order");

	return null; // input_order
    }

    IntVar getVariable(ASTScalarFlatExpr node) {
	if (node.getType() == 0) //int
	    return new IntVar(store, node.getInt(), node.getInt());
	else if (node.getType() == 2) // ident
	    return dictionary.getVariable(node.getIdent());
	else if (node.getType() == 3) {// array access
	    if (node.getInt() > dictionary.getVariableArray(node.getIdent()).length ||
		node.getInt() < 0) {
		System.out.println("Index out of bound for " + node.getIdent() + "["+node.getInt()+"]");
		System.exit(0);
		return new IntVar(store);
	    }
	    else
		return dictionary.getVariableArray(node.getIdent())[node.getInt()];
	}
	else {
	    System.err.println("Wrong parameter " + node);
	    System.exit(0);
	    return new IntVar(store);
	}
    }

    FloatVar getFloatVariable(ASTScalarFlatExpr node) {
	if (node.getType() == 5) //float
	    return new FloatVar(store, node.getFloat(), node.getFloat());
	else if (node.getType() == 2) // ident
	    return dictionary.getFloatVariable(node.getIdent());
	else if (node.getType() == 3) {// array access
	    if (node.getInt() > dictionary.getVariableFloatArray(node.getIdent()).length ||
		node.getInt() < 0) {
		System.out.println("Index out of bound for " + node.getIdent() + "["+node.getInt()+"]");
		System.exit(0);
		return new FloatVar(store);
	    }
	    else
		return dictionary.getVariableFloatArray(node.getIdent())[node.getInt()];
	}
	else {
	    System.err.println("Wrong parameter " + node);
	    System.exit(0);
	    return new FloatVar(store);
	}
    }

    IntVar[] getVarArray(SimpleNode node) {
	if (node.getId() == JJTARRAYLITERAL) {
	    int count = node.jjtGetNumChildren();
	    IntVar[] aa = new IntVar[count];
	    for (int i=0;i<count;i++) {
		ASTScalarFlatExpr child = (ASTScalarFlatExpr)node.jjtGetChild(i);
		IntVar el = getVariable(child);
		aa[i] = el;
	    }
	    return aa;
	}
	else if (node.getId() == JJTSCALARFLATEXPR) {
	    if (((ASTScalarFlatExpr)node).getType() == 2) // ident
		return dictionary.getVariableArray(((ASTScalarFlatExpr)node).getIdent());
	    else {
		System.err.println("Wrong type of Variable array; compilation aborted."); 
		System.exit(0);
		return new IntVar[] {};
	    }
	}
	else {
	    System.err.println("Wrong type of Variable array; compilation aborted."); 
	    System.exit(0);
	    return new IntVar[] {};
	}
    }

    FloatVar[] getFloatVarArray(SimpleNode node) {
	if (node.getId() == JJTARRAYLITERAL) {
	    int count = node.jjtGetNumChildren();
	    FloatVar[] aa = new FloatVar[count];
	    for (int i=0;i<count;i++) {
		ASTScalarFlatExpr child = (ASTScalarFlatExpr)node.jjtGetChild(i);
		FloatVar el = (FloatVar)getFloatVariable(child);
		aa[i] = el;
	    }
	    return aa;
	}
	else if (node.getId() == JJTSCALARFLATEXPR) {
	    if (((ASTScalarFlatExpr)node).getType() == 2) // ident
		return dictionary.getVariableFloatArray(((ASTScalarFlatExpr)node).getIdent());
	    else {
		System.err.println("Wrong type of Variable array; compilation aborted."); 
		System.exit(0);
		return new FloatVar[] {};
	    }
	}
	else {
	    System.err.println("Wrong type of Variable array; compilation aborted."); 
	    System.exit(0);
	    return new FloatVar[] {};
	}
    }


    SetVar getSetVariable(ASTScalarFlatExpr node) {
	if (node.getType() == 2) // ident
	    return dictionary.getSetVariable(node.getIdent());
	else if (node.getType() == 3) // array access
	    return dictionary.getSetVariableArray(node.getIdent())[node.getInt()];
	else {
	    System.err.println("Wrong parameter on list of search set varibales" + node);
	    System.exit(0);
	    // FIXME, why not return null?
	    return new SetVar(store);
	}
    }

    SetVar[] getSetVarArray(SimpleNode node) {
	if (node.getId() == JJTARRAYLITERAL) {
	    int count = node.jjtGetNumChildren();
	    SetVar[] aa = new SetVar[count];
	    for (int i=0;i<count;i++) {
		ASTScalarFlatExpr child = (ASTScalarFlatExpr)node.jjtGetChild(i);
		SetVar el = getSetVariable(child);
		aa[i] = el;
	    }
	    return aa;
	}
	else if (node.getId() == JJTSCALARFLATEXPR) {
	    if (((ASTScalarFlatExpr)node).getType() == 2) // ident
		return dictionary.getSetVariableArray(((ASTScalarFlatExpr)node).getIdent());
	    else {
		System.err.println("Wrong type of Variable array; compilation aborted."); 
		System.exit(0);
		return new SetVar[] {};
	    }
	}
	else {
	    System.err.println("Wrong type of Variable array; compilation aborted."); 
	    System.exit(0);
	    return new SetVar[] {};
	}
    }

    public String type() {
	return search_type;
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

    ArrayList<SearchItem> getSearchItems() {
	return search_seq;
    }

    public void addSearch(SearchItem si) {
	search_seq.add(si);
    }

    public int search_seqSize() {
	return search_seq.size();
    }

    public String toString() {
	String s="";
	if (search_type == null)
	    s += "defult_search\n";
	else if (search_seq.size() == 0) {
	    s = search_type + ", ";
	    if (search_variables == null)
		s += "[]";
	    else 
		s += Arrays.asList(search_variables);
	    s += ", "+explore + ", " + var_selection_heuristic+", "+indomain;
	    if (floatSearch)
		s += ", " + precision;
	}
	else {
	    for (SearchItem se : search_seq)
		s += se +"\n";
	}
	return s;
    }
}
