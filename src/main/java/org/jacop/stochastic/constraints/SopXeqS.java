package org.jacop.stochastic.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

import org.jacop.constraints.Constraint;
import org.jacop.core.IntDomain;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.stochastic.core.DiscreteStochasticDomain;
import org.jacop.stochastic.core.Link;
import org.jacop.stochastic.core.Operator;
import org.jacop.stochastic.core.Operator.ArithOp;
import org.jacop.stochastic.core.Operator.CompOp;
import org.jacop.stochastic.core.ProbabilityRange;
import org.jacop.stochastic.core.StochasticDomain;
import org.jacop.stochastic.core.StochasticVar;

/**
 * Implements the constraint Slhs op X = Srhs where Slhs and Srhs are 
 * StochasticVars and X is an IntVar. 
 * The operation op can be "+", "-", "*" or "/" .
 */
public class SopXeqS extends Constraint {

	static int IdNumber = 1;

	/**
	 * StochasticVar on the left hand side.
	 */
	public StochasticVar Slhs;
	
	/**
	 * StochasticVar on the right hand side.
	 */
	public StochasticVar Srhs;
	
	/**
	 * Specified IntVar.
	 */
	public IntVar X;
		

    /**
	 * Desired operation : "+", "-", "*" or "/".
	 */
	public Operator op;

	/**
	 * Mapping of Slhs values to Srhs values.
	 */
	private HashMap<Integer, ArrayList<Link>> l2r;
	
	/**
	 * Mapping of Slhs values to Srhs values for the current invocation of
	 * Consistency.
	 */
	private HashMap<Integer, ArrayList<Link>> l2rCurrent;
	
	/**
	 * Mapping of Srhs values to Slhs values.
	 */
	private HashMap<Integer, ArrayList<Link>> r2l;
	
	/**
	 * Mapping of Srhs values to Slhs values for the current invocation of
	 * Consistency.
	 */
	private HashMap<Integer, ArrayList<Link>> r2lCurrent;
	
	/**
	 * This constructor creates a new SopXeqS constraint.
	 * @param Slhs : StochasticVar on the left hand side
	 * @param op : Desired operation
	 * @param X : Specified IntVar
	 * @param Srhs : StochasticVar on the right hand side
	 */
	public SopXeqS(StochasticVar Slhs, Operator op, IntVar X, StochasticVar Srhs) {

        assert (op.aOp != ArithOp.INVALID): "Invalid Operation";

		
		this.queueIndex = 1;
		this.numberId = IdNumber++;
		this.numberArgs = (short)(3) ;
		this.Slhs = Slhs;
		this.op = op;
		this.X = X;
		this.Srhs = Srhs;	
		
		computeMappings();

	}

	/**
	 * Computes the mappings between the values of Slhs and Srhs in both
	 * directions.
	 */
	private void computeMappings() {
		
		l2r = new HashMap<Integer, ArrayList<Link>>(Slhs.getSize());
		
		for (int i : Slhs.dom().values){
			
			ArrayList<Link> map = new ArrayList<Link>(0);
			
			for (int j : Srhs.dom().values){

                for (ValueEnumeration e = X.dom().valueEnumeration(); e.hasMoreElements();) {
                    int k = e.nextElement();

                    if (op.doArithOp(i, k) == j)
						map.add(new Link(k, j));
				}
			}
			l2r.put(i, map);
		}
		
		r2l = new HashMap<Integer, ArrayList<Link>>(Srhs.getSize());
		
		for (int i : Srhs.dom().values){
			
			ArrayList<Link> map = new ArrayList<Link>(0);
			
			for (int j : Slhs.dom().values){
				
                for (ValueEnumeration e = X.dom().valueEnumeration(); e.hasMoreElements();) {
                    int k = e.nextElement();

					if ( op.doArithOp(j, k) == i)
						map.add(new Link(k, j));
				}
			}
			r2l.put(i, map);
		}

		// System.out.println (l2r);
		// System.out.println (r2l);

	}

	@Override
	public ArrayList<Var> arguments() {

		ArrayList<Var> variables = new ArrayList<Var>(3);
		variables.add(Slhs);
		variables.add(X);
		variables.add(Srhs);

		return variables;
	}

	@Override
	public void consistency(Store store) {
		
		// TODO, RADEK
		// What about a different approach? 
		// do not create and modify l2rCurrent, but instead of create a program that will 
		// use appropriate edges in the graph
		// loop over elements from two sets (S_l, X, S_r) 
		// out of three sets and find if there exists value for the 
		// remaining set. If there is a triplet that makes constraint satisfy then use 
		// probability range to properly compute the union of possible probabilities.
		// checking for element in X, method contains(int). 
		// checking for element in S_r(S_l) using binary search. 
		// it is possible to early terminate the computation of union if that already results in 
		// being sure that no pruning occurrs. (e.g. range is 0.5..0.7] and range is already [0.3..1.0]
		// can help in early termination of one loop body execution).
		// Maybe is not a huge improvement as X would be close to at least one S_?. 
		do {
			store.propagationHasOccurred = false;
			
			IntDomain XdomCopy = X.dom().cloneLight();
			
			DiscreteStochasticDomain[] SlhsDomCopy = new DiscreteStochasticDomain[X.getSize()];
			DiscreteStochasticDomain[] SrhsDomCopy = new DiscreteStochasticDomain[X.getSize()];
			
			// TODO, RADEK, here the code assumes that X has low cardinality. X is always one 
			// of the smallest cardinalities, it can not have large cardinality while S_l, S_r have small one.

			for (int i=0; i < XdomCopy.getSize(); i++) {

				boolean remove = true;
				removeDeadLinks(XdomCopy.getElementAt(i)); // TODO, Radek, instead of removing dead link, why not compute/find alive ones?
				
				SlhsDomCopy[i] = Slhs.dom().cloneLight();
				
				for (int j=0; j < Slhs.getSize(); j++) {

					// TODO, Radek, at this point we know X element, we know Slhs element, so we can compute Srhs element value.
					ArrayList<Link> map = l2rCurrent.get(new Integer(Slhs.dom().values[j]));
					ProbabilityRange r = new ProbabilityRange(0);
					
					if (map.size() > 0) {
						
						remove = false;
						for (int k = 0; k < map.size(); k++){
							int index = Arrays.binarySearch(Srhs.dom().values, map.get(k).leaf);
							r.add(Srhs.dom().ProbRanges[index]);
						}
			
					}

					// TODO, in case of || better to reverse arguments as the second one computes faster.
					// TODO, maybe this case should be just disallowed.
					if (XdomCopy.getElementAt(i) != 0 || op.aOp != ArithOp.MULTIPLY)
						SlhsDomCopy[i].ProbRanges[j].inWithoutFail(r);

				}
				
				SrhsDomCopy[i] = Srhs.dom().cloneLight();
				
				for (int j=0; j < Srhs.getSize(); j++) {
					
					// TODO, Radek, at this point we know X element, we know Srhs element, so we can compute Slhs element value.
					ArrayList<Link> map = r2lCurrent.get(new Integer(Srhs.dom().values[j]));
					//System.out.println ("r2lCurrent = " + r2lCurrent);

					ProbabilityRange r = new ProbabilityRange(0);

					if (map.size() > 0) {
						
						remove = false;
						for (int k = 0; k < map.size(); k++) {
							int index = Arrays.binarySearch(Slhs.dom().values, map.get(k).leaf);
							r.add(Slhs.dom().ProbRanges[index]);
						}
					}

					SrhsDomCopy[i].ProbRanges[j].inWithoutFail(r);

				}

				if (remove)
					X.dom().inComplement(store.level, X, XdomCopy.getElementAt(i));
			}
			
			DiscreteStochasticDomain SlhsResult = Slhs.dom().cloneLight();
			
			for (int i=0; i < SlhsResult.getSize(); i++)
				SlhsResult.ProbRanges[i] = new ProbabilityRange(1,0);
			
			DiscreteStochasticDomain SrhsResult = Srhs.dom().cloneLight();
			
			for (int i=0; i < SrhsResult.getSize(); i++)
				SrhsResult.ProbRanges[i] = new ProbabilityRange(1,0);

			for (int i = 0; i < XdomCopy.getSize(); i++) {
				
			    for (int j = 0; j < SlhsDomCopy[i].getSize(); j++) 				
					SlhsResult.ProbRanges[j].union(SlhsDomCopy[i].ProbRanges[j]);

			    for (int j = 0; j < SrhsDomCopy[i].getSize(); j++)
					SrhsResult.ProbRanges[j].union(SrhsDomCopy[i].ProbRanges[j]);
			}
			
			// CHANGE, Krzysztof,
			// Replacing setElement with inElement that is natural in consistency
			// Moreover setElement will cause infinite loop when domain will not change
			// Slhs.dom().setElement(store.level, Slhs, SlhsResult.values, SlhsResult.ProbRanges);
			// Srhs.dom().setElement(store.level, Srhs, SrhsResult.values, SrhsResult.ProbRanges);

			Slhs.dom().inElement(store.level, Slhs, SlhsResult.values, SlhsResult.ProbRanges);
			Srhs.dom().inElement(store.level, Srhs, SrhsResult.values, SrhsResult.ProbRanges);

		} while(store.propagationHasOccurred);
	}
	

	/**
	 * This method removes links in l2rCurrent and r2lCurrent which do not
	 * have an edge corresponding to the specified X domain value.
     * @param Xval : link to be removed for this value
     *
	 */
	private void removeDeadLinks(int Xval) {

		l2rCurrent = new HashMap<Integer, ArrayList<Link>>(Slhs.getSize());

		for (int i : Slhs.dom().values){
			
			ArrayList<Link> mapOrig = l2r.get(new Integer(i));
			ArrayList<Link> mapCurr = new ArrayList<Link>();
			
			// TODO, this loop gets very expensive for X with large domain. 
			for (int j = 0; j < mapOrig.size(); j++)
				if (mapOrig.get(j).edge == Xval)
					mapCurr.add(mapOrig.get(j));
			
			l2rCurrent.put(i, mapCurr);
		}
		
		r2lCurrent = new HashMap<Integer, ArrayList<Link>>(Srhs.getSize());

		for (int i : Srhs.dom().values){
			
			ArrayList<Link> mapOrig = r2l.get(new Integer(i));
			ArrayList<Link> mapCurr = new ArrayList<Link>();
			
			for (int j = 0; j < mapOrig.size(); j++)
				if (mapOrig.get(j).edge == Xval)
					mapCurr.add(mapOrig.get(j));
			
			r2lCurrent.put(i, mapCurr);
		}

	}

	@Override
	public int getConsistencyPruningEvent(Var var) {
		
		// If consistency function mode
		if (consistencyPruningEvents != null) {
			Integer possibleEvent = consistencyPruningEvents.get(var);
			if (possibleEvent != null)
				return possibleEvent;
		}
		return StochasticDomain.BOUND;
	}

	@Override
	public String id() {
		
		if (id != null)
			return id;
		else
			return this.getClass().getSimpleName() + numberId;
	}

	@Override
	public void impose(Store store) {

		Slhs.putModelConstraint(this, getConsistencyPruningEvent(Slhs));
		X.putModelConstraint(this, getConsistencyPruningEvent(X));
		Srhs.putModelConstraint(this, getConsistencyPruningEvent(Srhs));

		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void removeConstraint() {

		Slhs.removeConstraint(this);
		X.removeConstraint(this);
		Srhs.removeConstraint(this);
	}

	@Override
	public boolean satisfied() {

        return false;

        //TODO: KRZYSZTOF
        // The same comment as for SopCrelS

        /*
		for (int i=0; i < X.getSize(); i++) {
		
			removeDeadLinks(X.dom().getElementAt(i));
			
			for (int j=0; j < Slhs.getSize(); j++) {
				
				ArrayList<Link> map = l2rCurrent.get(new Integer(Slhs.dom().values[j]));
				ProbabilityRange r = new ProbabilityRange(0);
				
				if (map.size() > 0) {
					
					for (int k = 0; k < map.size(); k++){
						int index = Arrays.binarySearch(Srhs.dom().values, map.get(k).leaf);
						r.add(Srhs.dom().ProbRanges[index]);
					}
		
				}
				
				if (!Slhs.dom().ProbRanges[j].eq(r))
					return false;
			}
			
			for (int j=0; j < Srhs.getSize(); j++) {
				
				ArrayList<Link> map = r2lCurrent.get(new Integer(Srhs.dom().values[j]));
				ProbabilityRange r = new ProbabilityRange(0);
				
				if (map.size() > 0) {
					
					for (int k = 0; k < map.size(); k++) {
						int index = Arrays.binarySearch(Slhs.dom().values, map.get(k).leaf);
						r.add(Slhs.dom().ProbRanges[index]);
					}
				}
				
				if (!Srhs.dom().ProbRanges[j].eq(r))
					return false;
			}
		}
		return true;
		*/
	}

	@Override
	public String toString() {

		StringBuffer result = new StringBuffer( id() );
		
		result.append(" : SopXeqS( " + Slhs + " " + op.aOp + " " + X
				+ " == " + Srhs + ")");
		
		return result.toString();
	}

	@Override
	public void increaseWeight() {

		if (increaseWeight) {
			Slhs.weight++;
			X.weight++;
			Srhs.weight++;
		}
	}
}