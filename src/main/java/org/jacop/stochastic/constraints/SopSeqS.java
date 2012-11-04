package org.jacop.stochastic.constraints;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

import org.jacop.constraints.Constraint;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.stochastic.core.Link;
import org.jacop.stochastic.core.Operator;
import org.jacop.stochastic.core.Operator.ArithOp;
import org.jacop.stochastic.core.ProbabilityRange;
import org.jacop.stochastic.core.StochasticDomain;
import org.jacop.stochastic.core.StochasticVar;

import javax.swing.plaf.basic.BasicInternalFrameTitlePane;

/**
 * Implements the constraint Slhs1 op Slhs2 = Srhs where Slhs1, Slhs2 and Srhs 
 * are StochasticVars. The operation op can be "+", "-", "*" or "/" .
 */
public class SopSeqS extends Constraint{

    final boolean trace = false;

    static int IdNumber = 1;

    /**
     * StochasticVar 1 on the left hand side.
     */
    public StochasticVar Slhs1;

    /**
     * StochasticVar 2 on the left hand side.
     */
    public StochasticVar Slhs2;

    /**
     * StochasticVar on the right hand side.
     */
    public StochasticVar Srhs;

    /**
     * Desired operation : "+", "-", "*" or "/".
     */
    public Operator op;

    /**
     * Mapping from left to right w.r.t Slhs1.
     */
    private HashMap<Integer, ArrayList<Link>> l2r1;

    /**
     * Mapping from left to right w.r.t. Slhs2.
     */
    private HashMap<Integer, ArrayList<Link>> l2r2;

    /**
     * Mapping from right to left.
     */
    private HashMap<Integer, ArrayList<Link>> r2l;

    /**
     * This constructor creates a new SopSeqS constraint.
     * @param Slhs1 : StochasticVar 1 on the left hand side
     * @param op : Desired operation
     * @param Slhs2 : StochasticVar 2 on the left hand side
     * @param Srhs : StochasticVar on the right hand side
     */
    public SopSeqS(StochasticVar Slhs1, Operator op, StochasticVar Slhs2, StochasticVar Srhs) {

        assert (op.aOp != ArithOp.INVALID): "Invalid Operation";

        this.queueIndex = 1;
        this.numberId = IdNumber++;
        this.numberArgs = (short)(3) ;
        this.Slhs1 = Slhs1;
        this.op = op;
        this.Slhs2 = Slhs2;
        this.Srhs = Srhs;

        computeMappings();
    }

    /**
     * Computes the mappings between the values of Slhs1, Slhs2 and Srhs in 
     * both directions.
     */
    private void computeMappings() {

        l2r1 = new HashMap<Integer, ArrayList<Link>>(Slhs1.getSize());

        for (int i : Slhs1.dom().values){

            ArrayList<Link> map = new ArrayList<Link>(0);

            for (int j : Srhs.dom().values){

                for (int k : Slhs2.dom().values){

                    if (op.doArithOp(i, k) == j )
                        map.add(new Link(k, j));

                }
            }
            l2r1.put(i, map);
        }

        l2r2 = new HashMap<Integer, ArrayList<Link>>(Slhs2.getSize());

        for (int i : Slhs2.dom().values){

            ArrayList<Link> map = new ArrayList<Link>(0);

            for (int j : Srhs.dom().values){

                for (int k : Slhs1.dom().values){

                    if (op.doArithOp(k, i) == j )
                        map.add(new Link(k, j));

                }
            }
            l2r2.put(i, map);
        }

        r2l = new HashMap<Integer, ArrayList<Link>>(Srhs.getSize());

        for (int i : Srhs.dom().values){

            ArrayList<Link> map = new ArrayList<Link>(0);

            for (int j : Slhs1.dom().values){

                for (int k : Slhs2.dom().values){
                    if (op.doArithOp(j, k) == i ) {
                        map.add(new Link(k, j));
		    }
                }
            }
            r2l.put(i, map);
        }
	
	if (trace) 
	    System.out.println("l2r1 [Slhs1 -> (Slhs2, Srhs) ] = " + l2r1 + "\n" +
			       "l2r2 [Slhs2 -> (Slhs1, Srhs) ] = " + l2r2 + "\n" +
			       "r2l [Srhs -> (Slhs2, Slhs1) ] = " + r2l);
    }

    @Override
    public ArrayList<Var> arguments() {

        ArrayList<Var> variables = new ArrayList<Var>(3);
        variables.add(Slhs1);
        variables.add(Slhs2);
        variables.add(Srhs);

        return variables;
    }

    @Override
    public void consistency(Store store) {

	do {
	    store.propagationHasOccurred = false;

        //        System.out.println(this.id());

        // TO_DO, RADEK, What if all stochastic variables are singletons to start with?
        // There must be an initial failure flag if this type of efficiency trick
        // is used.
        // DONE, KRZYSZTOF, It is even worth and this check needs to be removed since
        // one of the variables can be set by other constraints and it is not consistent with
        // this constraint. It has to be checked and fail generated!!!

        //if (Slhs1.singleton() && Slhs2.singleton() && Srhs.singleton()) {

        //    return;
        //} else {

        // TODO, RADEK, if some of the stochastic variables become constants then there
        // should be possibility for reuse of some previous computation or avoidance of
        // some computation. An example is what XplusYeqZ constraint is doing when one
        // of the variables is a singleton.
	for (int i=0; i < Slhs1.getSize(); i++){

            ArrayList<Link> map = l2r1.get(new Integer(Slhs1.dom().values[i]));
            ProbabilityRange r = null; //new ProbabilityRange(0);

            if (map.size() > 0){

                for (Link aMap : map) {

                    // ================
		    if (trace) 
			System.out.println(Slhs1.dom().values[i] + " "+ op.aOp +" " + aMap.edge + " = " + aMap.leaf + "\n" +
					   "Other that give " + aMap.leaf + " = " + r2l.get(aMap.leaf) );

		    ProbabilityRange pr = computeRange(true, Slhs1, Slhs2, aMap, i);

		    if (trace)
			System.out.println ("*** pr = " + pr);

		    if (r == null)
			r = pr;
		    else
			r.inWithoutFail(pr);

		    if (trace) 
			System.out.println ("*** r = " + r);

                }
            }
            else
                r = new ProbabilityRange(0);

            if (trace) 
		System.out.println(Slhs1 + "["+i+"]" + " ### " + Slhs1.dom().ProbRanges[i] + " <- " + r);

            Slhs1.dom().inElement(store.level, Slhs1, Slhs1.dom().values[i], r);
        }

        for (int i=0; i < Slhs2.getSize(); i++){

            ArrayList<Link> map = l2r2.get(new Integer(Slhs2.dom().values[i]));
            ProbabilityRange r = null; //new ProbabilityRange(0);

	    // System.out.println ("Checking " + map);

            if (map.size() > 0){

                for (Link aMap : map) {

                    // ================
                    // System.out.println(Slhs2.dom().values[i] + " "+ op.aOp + " " + aMap.edge + " = " + aMap.leaf);
                    // System.out.println("Other that give " + aMap.leaf + " = " + r2l.get(aMap.leaf) );

		    ProbabilityRange pr = computeRange(false, Slhs2, Slhs1, aMap, i);

		    if (r == null)
			r = pr;
		    else
			r.inWithoutFail(pr);
                }
            }
            else
                r = new ProbabilityRange(0);

            if (trace)
		System.out.println(Slhs2 + "["+i+"]" + " ### " + Slhs2.dom().ProbRanges[i] + " <- " + r);

            Slhs2.dom().inElement(store.level, Slhs2, Slhs2.dom().values[i], r);
        }

        for (int i=0; i < Srhs.getSize(); i++){

            ArrayList<Link> map = r2l.get(new Integer(Srhs.dom().values[i]));
            ProbabilityRange r = new ProbabilityRange(0);

            if (map.size() > 0) {

                for (Link aMap : map) {

                    int indexLeaf = Arrays.binarySearch(Slhs1.dom().values, aMap.leaf);
                    int indexEdge = Arrays.binarySearch(Slhs2.dom().values, aMap.edge);

                    double minTmp = (Slhs1.dom().ProbRanges[indexLeaf].min) * (Slhs2.dom().ProbRanges[indexEdge].min);
                    double maxTmp = (Slhs1.dom().ProbRanges[indexLeaf].max) * (Slhs2.dom().ProbRanges[indexEdge].max);

                    r.add(new ProbabilityRange(minTmp, maxTmp));
                }
            }

            if (trace)
		System.out.println(this.id() + ": " + Srhs + "["+i+"]" + " ### " + Srhs.dom().ProbRanges[i] + " <- " + r);

            Srhs.dom().inElement(store.level, Srhs, Srhs.dom().values[i], r);

        }
	} while(store.propagationHasOccurred);


    }

    private ProbabilityRange computeRange(boolean first, StochasticVar mainVar, StochasticVar biVar, Link aMap, int i) {

	// System.out.println ("*** " + mainVar + " and " + biVar);
	// System.out.println ("computeRangeForSameOutput( " + aMap+ ", " + i +")");
	// System.out.println ("??? "+ r2l.get(aMap.leaf) +" and "+  mainVar.dom().values[i]);

	double minProb = 0, maxProb = 0;

	ArrayList<Link> notMap = (first) 
	    ? computeMappingsToSubtract1(r2l.get(aMap.leaf), mainVar.dom().values[i])
	    : computeMappingsToSubtract2(r2l.get(aMap.leaf), mainVar.dom().values[i]);

	// System.out.println("to subtract" + notMap);

	for (Link aNotMap : notMap) {
	    // System.out.println("computing " + aNotMap.edge +", " + aNotMap.leaf);
	    
	    int indexmainVar = (first) 
		? Arrays.binarySearch(mainVar.dom().values, aNotMap.leaf)
		: Arrays.binarySearch(mainVar.dom().values, aNotMap.edge);
	    int indexbiVar = (first) 
		? Arrays.binarySearch(biVar.dom().values, aNotMap.edge) 
		: Arrays.binarySearch(biVar.dom().values, aNotMap.leaf);

	    //System.out.println("Consider " + mainVar.dom().ProbRanges[indexmainVar] + ", " + biVar.dom().ProbRanges[indexbiVar]);

	    minProb += mainVar.dom().ProbRanges[indexmainVar].min * biVar.dom().ProbRanges[indexbiVar].min;
	    maxProb += mainVar.dom().ProbRanges[indexmainVar].max * biVar.dom().ProbRanges[indexbiVar].max;
	}
	// System.out.println("3. To subtract "+ minProb + ".." + maxProb);

	double totalMin=0, totalMax=0;
	// System.out.println ("### " + r2l.get(aMap.edge) + " " + r2l.get(aMap.leaf));

	if (first)
	    for (Link r2lMap : r2l.get(aMap.leaf)) {
		if (mainVar.dom().values[i] == r2lMap.leaf) {
		    // System.out.println ("aMap.leaf = "+aMap.leaf+ ", aMap.edge = " + aMap.edge);
		    // System.out.println ("r2lMap.leaf = "+r2lMap.leaf+ ", r2lMap.edge = " + r2lMap.edge);

		    int indexLeaf = Arrays.binarySearch(Srhs.dom().values, r2lMap.leaf);
		    int indexEdge = Arrays.binarySearch(biVar.dom().values, r2lMap.edge);

		    // System.out.println ("min = "+biVar.dom().ProbRanges[indexEdge].min);
		    // System.out.println ("max = "+biVar.dom().ProbRanges[indexEdge].max);

		    totalMin += biVar.dom().ProbRanges[indexEdge].min;
		    totalMax += biVar.dom().ProbRanges[indexEdge].max;
		}
	    }
	else // ! first  
	    for (Link r2lMap : r2l.get(aMap.leaf)) {
		if (mainVar.dom().values[i] == r2lMap.edge) { 
		    // System.out.println ("aMap.leaf = "+aMap.leaf+ ", aMap.edge = " + aMap.edge);
		    // System.out.println ("r2lMap.leaf = "+r2lMap.leaf+ ", r2lMap.edge = " + r2lMap.edge);

		    int indexLeaf = Arrays.binarySearch(Srhs.dom().values, r2lMap.edge);
		    int indexEdge = Arrays.binarySearch(biVar.dom().values, r2lMap.leaf);

		    // System.out.println ("min = "+biVar.dom().ProbRanges[indexEdge].min);
		    // System.out.println ("max = "+biVar.dom().ProbRanges[indexEdge].max);

		    totalMin += biVar.dom().ProbRanges[indexEdge].min;
		    totalMax += biVar.dom().ProbRanges[indexEdge].max;
		}
	    }

	// System.out.println ("totalMin/Max = "+totalMin + ".." + totalMax);

	int indexLeaf = Arrays.binarySearch(Srhs.dom().values, aMap.leaf); // r2l.get(aMap.leaf).get(0).edge);

	double minTmp = (totalMax == 0) ? 0 : (Srhs.dom().ProbRanges[indexLeaf].min - maxProb) / totalMax;
	double maxTmp = (totalMin == 0) ? 1 : (Srhs.dom().ProbRanges[indexLeaf].max - minProb) / totalMin;

	return new ProbabilityRange(minTmp, maxTmp);
    }

    private ArrayList<Link> computeMappingsToSubtract1(ArrayList<Link> links, int value) {

        ArrayList<Link> subLinks = (ArrayList<Link>)links.clone();
        for (Link link : links) {
            if ( link.leaf == value)
                subLinks.remove(link);
        }
        return subLinks;
    }

    private ArrayList<Link> computeMappingsToSubtract2(ArrayList<Link> links, int value) {

        ArrayList<Link> subLinks = (ArrayList<Link>)links.clone();
        for (Link link : links) {
            if ( link.edge == value )
                subLinks.remove(link);
        }
        return subLinks;
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

        Slhs1.putModelConstraint(this, getConsistencyPruningEvent(Slhs1));
        Slhs2.putModelConstraint(this, getConsistencyPruningEvent(Slhs2));
        Srhs.putModelConstraint(this, getConsistencyPruningEvent(Srhs));

        store.addChanged(this);
        store.countConstraint();
    }

    @Override
    public void removeConstraint() {

        Slhs1.removeConstraint(this);
        Slhs2.removeConstraint(this);
        Srhs.removeConstraint(this);
    }

    @Override
    public boolean satisfied() {

        return false;

        // TODO Krzysztof make correct checking.
        // The same comment as for SopCrelS
        // Moreover, currently can divide by 0 :( and return true if not all consistency is finished.

        /*for (int i=0; i < Slhs1.getSize(); i++){

        ArrayList<Link> map = l2r1.get(new Integer(Slhs1.dom().values[i]));
        ProbabilityRange r = new ProbabilityRange(0);

        if (map.size() > 0){

        for (int j=0; j < map.size(); j++) {

        int indexLeaf = Arrays.binarySearch(Srhs.dom().values, map.get(j).leaf);
        int indexEdge = Arrays.binarySearch(Slhs2.dom().values, map.get(j).edge);

        double minTmp = (Srhs.dom().ProbRanges[indexLeaf].min)/(Slhs2.dom().ProbRanges[indexEdge].min);
        double maxTmp = (Srhs.dom().ProbRanges[indexLeaf].max)/(Slhs2.dom().ProbRanges[indexEdge].max);

        r.union(new ProbabilityRange(minTmp, maxTmp));
        }
        }

        if (!Slhs1.dom().ProbRanges[i].eq(r))
        return false;

        }

        for (int i=0; i < Slhs2.getSize(); i++){

        ArrayList<Link> map = l2r2.get(new Integer(Slhs2.dom().values[i]));
        ProbabilityRange r = new ProbabilityRange(0);

        if (map.size() > 0){

        for (int j=0; j < map.size(); j++) {

        int indexLeaf = Arrays.binarySearch(Srhs.dom().values, map.get(j).leaf);
        int indexEdge = Arrays.binarySearch(Slhs1.dom().values, map.get(j).edge);

        double minTmp = (Srhs.dom().ProbRanges[indexLeaf].min)/(Slhs1.dom().ProbRanges[indexEdge].min);
        double maxTmp = (Srhs.dom().ProbRanges[indexLeaf].max)/(Slhs1.dom().ProbRanges[indexEdge].max);

        r.union(new ProbabilityRange(minTmp, maxTmp));
        }
        }

        if (!Slhs2.dom().ProbRanges[i].eq(r))
        return false;
        }

        for (int i=0; i < Srhs.getSize(); i++){

        ArrayList<Link> map = r2l.get(new Integer(Srhs.dom().values[i]));
        ProbabilityRange r = new ProbabilityRange(0);

        if (map.size() > 0) {

        for (int j=0; j < map.size(); j++) {

        int indexLeaf = Arrays.binarySearch(Slhs1.dom().values, map.get(j).leaf);
        int indexEdge = Arrays.binarySearch(Slhs2.dom().values, map.get(j).edge);

        double minTmp = (Slhs1.dom().ProbRanges[indexLeaf].min)*(Slhs2.dom().ProbRanges[indexEdge].min);
        double maxTmp = (Slhs1.dom().ProbRanges[indexLeaf].max)*(Slhs2.dom().ProbRanges[indexEdge].max);

        r.add(new ProbabilityRange(minTmp, maxTmp));
        }
        }

        if (!Srhs.dom().ProbRanges[i].eq(r))
        return false;
        }

        return true;
      */
    }

    @Override
    public String toString() {

        StringBuffer result = new StringBuffer( id() );

        result.append(" : SopSeqS( " + Slhs1 + " " + op.aOp + " " + Slhs2
                + " " + " == " + " " + Srhs + ")");

        return result.toString();
    }

    @Override
    public void increaseWeight() {

        if (increaseWeight) {
            Slhs1.weight++;
            Slhs2.weight++;
            Srhs.weight++;
        }
    }

}
