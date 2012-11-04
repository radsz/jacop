/**
 * test for SatSum
 */

package org.jacop.satwrapper.examples;

import java.util.ArrayList;

import org.jacop.constraints.Alldifferent;
import org.jacop.constraints.Sum;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.examples.fd.ExampleFD;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMiddle;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;

/**
 * 
 * It is quite complex logic puzzle about flowers.
 * 
 * @author Tomasz Szwed, Wojciech Krupa, and Radoslaw Szymanek
 *
 * Each of four women in our office was delighted to receive a floral delivery at her desk this month. Each of the 
 * women (Emma, Kristin, Lynn, and Toni) received flowers from her husband (Doug, Justin, Shane, or Theo) for a 
 * different special occasion. Each bouquet consisted of a different type of flower, and each was delivered 
 * during the first four weeks of February. From the following clues, can you match each woman with her husband 
 * and determine the date on which each woman received flowers, the occasion for the flowers, and the type of 
 * flowers in each bouquet?
 * 
 *
 * Calendar for February
 *
 * Mon  Tue   Wed   Thu   Fri
 * -     1     2     3     4
 * 7    8     9    10    11
 * 14   15    16    17    18
 * 21   22    23    24    25
 *
 * 1. No two women received flowers on the same day of the week, and no two received flowers during the same week.
 *
 * 2. The woman who received flowers for Valentine's Day had them delivered on either Friday the 11th or 
 * Monday the 14th.
 *
 * 3. Emma received flowers one day later in the week than the woman who received flowers to celebrate a promotion.
 *
 * 4. Lynn received flowers either the week before or the week after the woman who received violets.
 *
 * 5. Justin's wife received flowers on either Monday the 7th (in which case she is the one who received white roses) 
 * or on Thursday the 24th (in which case she is the woman who received flowers to celebrate her birthday).
 *
 * 6. Theo's wife didn't receive flowers exactly eight days before the woman who received chrysanthemums.
 *
 * 7. Toni's husband is either Doug or Shane.
 *
 * 8. One woman received either chrysanthemums or white roses for her wedding anniversary.
 *
 * 9. Kristin received flowers on either Tuesday the 1st (in which case she is 
 * the one who received daisies) or Friday the 18th (in which case she received them from Doug).
 *
 * 10. Shane's wife received flowers during the second week of the month.
 *
 * Determine: woman, husband, date, occasion, type of flowers
 *
 */
@SuppressWarnings("unused")
public class SimpleSum extends ExampleFD {
		
	@Override
	public void model() {

		System.out.println("begin model");
		
		store = new Store();
		vars = new ArrayList<IntVar>();
		
		IntVar x1, x2, x3, x4, sum;
		x1 = new IntVar(store, "x1", 1, 3);
		x2 = new IntVar(store, "x2", 1, 3);
		x3 = new IntVar(store, "x3",1, 3);
		// x4 = new SatIntVar(store, "x4",1, 2);
		sum = new IntVar(store, "sum", 1, 6);
		
		//store.impose(new XneqC(x1, 2));
		//store.impose(new XneqC(x2, 2));
		
		// special order for search
		//vars.add(x4);
		vars.add(sum);
		vars.add(x1);
		vars.add(x2);
		vars.add(x3);
		// choose to translate the domains of those vars in clauses
		
		// sum constraint
		IntVar[] left = { x1, x2, x3 };
		store.impose(new Sum(left, sum));
		store.impose(new Alldifferent(left));
		//store.impose(new Sum(left, sum));
		//store.impose(new Alldifferent(left));
	}

	
	/**
	 * It executes the program which solves this logic puzzle.
	 * @param args no argument is used.
	 */
	public static void main(String args[]) {

		SimpleSum example = new SimpleSum();
		
		example.model();
		System.out.println("end model");

//		// add debug and stat modules
//		StatModule mod = new StatModule(false);
//		example.wrapper.addSolverComponent(mod);
//		example.wrapper.core.verbosity = 3;
		
//		// debug module
//		WrapperDebugModule debug = new WrapperDebugModule();
//		example.wrapper.addWrapperComponent(debug);
		
		System.out.println("consistency");
		example.store.consistency();
		System.out.println("search");
		if (example.search())
			System.out.println("Solution(s) found");
		
		// prints stats
		//mod.logStats();
		
	}	
	
	

	@SuppressWarnings({ "rawtypes", "unchecked" })
	@Override
	public boolean searchAllAtOnce() {
		
		long T1, T2;
		T1 = System.currentTimeMillis();		
		
		SelectChoicePoint select = new SimpleSelect(vars.toArray(new Var[1]),
				null, new IndomainMiddle<IntVar>());
	
		search = new DepthFirstSearch();
		
		search.getSolutionListener().searchAll(true);
		search.getSolutionListener().recordSolutions(true);
		search.setAssignSolution(true);
		
		boolean result = search.labeling(store, select);
	
		T2 = System.currentTimeMillis();
	
		if (result) {
			System.out.println("Number of solutions " + search.getSolutionListener().solutionsNo());
		//	search.printAllSolutions();
		} 
		else
			System.out.println("Failed to find any solution");
	
		System.out.println("\n\t*** Execution time = " + (T2 - T1) + " ms");
	
		return result;
	}


	/**
	 * It specifies simple search method based on input order and lexigraphical 
	 * ordering of values. 
	 * 
	 * @return true if there is a solution, false otherwise.
	 */
	@SuppressWarnings({ "rawtypes", "unchecked" })
	public boolean search() {
		
		long T1, T2;
		T1 = System.currentTimeMillis();
		
		SelectChoicePoint select = new SimpleSelect(vars.toArray(new Var[1]), null,
				new IndomainMiddle<IntVar>());
	
		search = new DepthFirstSearch();
	
		boolean result = search.labeling(store, select);
	
		if (result)
			store.print();
	
		T2 = System.currentTimeMillis();
	
		System.out.println("\n\t*** Execution time = " + (T2 - T1) + " ms");
		
		System.out.println();
		System.out.print(search.getNodes() + "\t");
		System.out.print(search.getDecisions() + "\t");
		System.out.print(search.getWrongDecisions() + "\t");
		System.out.print(search.getBacktracks() + "\t");
		System.out.print(search.getMaximumDepth() + "\t");
		
		return result;
		
	}	
	
}
