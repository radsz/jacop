package org.jacop.examples.cpviz;

import org.jacop.constraints.netflow.NetworkBuilder;
import org.jacop.constraints.netflow.NetworkFlow;
import org.jacop.constraints.netflow.simplex.Node;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.search.TraceGenerator;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The class Run is used to run test programs for JaCoP package.
 * It is used for test purpose only.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.2
 */

public class CPvizNetworkFlow{ private static Logger logger = LoggerFactory.getLogger(CPvizNetworkFlow.class);
    Store store;
    IntVar[] vars;
    IntVar COST;

    public static void main (String args[]) {

      CPvizNetworkFlow run = new CPvizNetworkFlow();

      run.transportationProblem();
    }

    CPvizNetworkFlow() {}


    void transportationProblem() {
      long T1, T2, T;
      T1 = System.currentTimeMillis();

      store = new Store();

      NetworkBuilder net = new NetworkBuilder();
      Node A = net.addNode("A", 0);
      Node B = net.addNode("B", 0);
      Node C = net.addNode("C", 0);
      Node D = net.addNode("D", 0);
      Node E = net.addNode("E", 0);
      Node F = net.addNode("F", 0);


      Node source = net.addNode("source", 9);  // should ne 5+3+3=11 but it does not work...

      Node sinkD = net.addNode("sinkD", -3);
      Node sinkE = net.addNode("sinkE", -3);
      Node sinkF = net.addNode("sinkF", -3);

      IntVar[] x = new IntVar[13];

      x[0] = new IntVar(store, "x_0", 0, 5);
      x[1] = new IntVar(store, "x_1", 0, 3);
      x[2] = new IntVar(store, "x_2", 0, 3);
      net.addArc(source, A, 0, x[0]);
      net.addArc(source, B, 0, x[1]);
      net.addArc(source, C, 0, x[2]);

      x[3] = new IntVar(store, "a->d", 0, 5);
      x[4] = new IntVar(store, "a->e", 0, 5);
      net.addArc(A, D, 3, x[3]);
      net.addArc(A, E, 1, x[4]);

      x[5] = new IntVar(store, "b->d", 0, 3);
      x[6] = new IntVar(store, "b->e", 0, 3);
      x[7] = new IntVar(store, "b->f", 0, 3);
      net.addArc(B, D, 4, x[5]);
      net.addArc(B, E, 2, x[6]);
      net.addArc(B, F, 4, x[7]);

      x[8] = new IntVar(store, "c->e", 0, 3);
      x[9] = new IntVar(store, "c->f", 0, 3);
      net.addArc(C, E, 3, x[8]);
      net.addArc(C, F, 3, x[9]);

      x[10] = new IntVar(store, "x_10", 3, 3);
      x[11] = new IntVar(store, "x_11", 3, 3);
      x[12] = new IntVar(store, "x_12", 3, 3);
      net.addArc(D, sinkD, 0, x[10]);
      net.addArc(E, sinkE, 0, x[11]);
      net.addArc(F, sinkF, 0, x[12]);

      IntVar cost = new IntVar(store, "cost", 0, 1000);
      net.setCostVariable(cost);

      vars = x;
      COST = cost;

      store.impose(new NetworkFlow(net));

      logger.info( "\nIntVar store size: "+ store.size()+
			  "\nNumber of constraints: " + store.numberConstraints()
			  );

      boolean Result = true;
      Search<IntVar> label = new DepthFirstSearch<IntVar>();
      SelectChoicePoint<IntVar> varSelect = new SimpleSelect<IntVar>(x, null,
						  new IndomainMin<IntVar>());
      // Trace --->
      SelectChoicePoint<IntVar> select = new TraceGenerator<IntVar>(label, varSelect);

//      SelectChoicePoint<IntVar> select = new TraceGenerator<IntVar>(varSelect, false);
//      label.setConsistencyListener((ConsistencyListener)select);
//      label.setExitChildListener((ExitChildListener)select);
//      label.setExitListener((ExitListener)select);
      // <---

      DepthFirstSearch<IntVar> costSearch = new DepthFirstSearch<IntVar>();
      SelectChoicePoint<IntVar> costSelect = new SimpleSelect<IntVar>(new IntVar[] {cost}, null, new IndomainMin<IntVar>());
      costSearch.setSelectChoicePoint(costSelect);
      costSearch.setPrintInfo(false);
      costSearch.setSolutionListener(new NetListener<IntVar>());
      label.addChildSearch(costSearch);

      label.setAssignSolution(true);
      label.setPrintInfo(true);

      Result = label.labeling(store, select, cost);


      if (Result) {
	  logger.info("*** Yes");
	  logger.info(cost.toString());
      }
      else
	  logger.info("*** No");

      T2 = System.currentTimeMillis();
      T = T2 - T1;
      logger.info("\n\t*** Execution time = "+ T + " ms");
    }

public class NetListener<T extends Var> extends SimpleSolutionListener<T> { private Logger logger = LoggerFactory.getLogger(NetListener.class);

	public boolean executeAfterSolution(Search<T> search, SelectChoicePoint<T> select) {

	    boolean returnCode = super.executeAfterSolution(search, select);

	    logger.info("Solution cost cost = " + COST.value());

	    logger.info ("[");

	    for ( Var var : vars) {
	    	logger.info(var + " ");
	    }

	    logger.info ("]");

	    return returnCode;
	}
    }

}
