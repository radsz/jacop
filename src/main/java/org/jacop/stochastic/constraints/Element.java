package org.jacop.stochastic.constraints;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Arrays;

import org.jacop.constraints.Constraint;
import org.jacop.core.*;
import org.jacop.stochastic.core.ProbabilityRange;
import org.jacop.stochastic.core.StochasticDomain;
import org.jacop.stochastic.core.StochasticVar;

public class Element extends Constraint{

	static int IdNumber = 1;
	public IntVar index;
	public StochasticVar[] list;
	public StochasticVar value;
	public int offset;
	private HashMap<Integer, HashMap<Integer, ProbabilityRange>> map;

	public Element (IntVar index, StochasticVar[] list, StochasticVar value, int offset){
		
		this.queueIndex = 1;
		this.numberId = IdNumber++;
		this.numberArgs = (short) (list.length + 1);
		this.index = index;
		this.list = list;	
		this.value = value;		
		this.offset = offset;
		
		computeMappings();
	}

	public Element (IntVar index, StochasticVar[] list, StochasticVar value){
		
		this.queueIndex = 1;
		this.numberId = IdNumber++;
		this.numberArgs = (short) (list.length + 1);
		this.index = index;
		this.list = list;	
		this.value = value;		
		this.offset = 0;
		
		computeMappings();
	}
	
	private void computeMappings() {

		map = new HashMap<Integer, HashMap<Integer, ProbabilityRange>>(value.getSize());
		
		for (int i = 0; i < value.getSize(); i++) {
			
			HashMap<Integer, ProbabilityRange> subMap = new HashMap<Integer, ProbabilityRange>(index.getSize());
			
            for (ValueEnumeration e = index.dom().valueEnumeration(); e.hasMoreElements();) {
                int j = e.nextElement();

                StochasticVar S = list[j - offset];
				ProbabilityRange r = new ProbabilityRange(0, 0);
				
				for (int k = 0; k < S.getSize(); k++)
					if (value.dom().values[i] == S.dom().values[k])
						r = S.dom().ProbRanges[k];

                subMap.put(j - offset, r);

			}
			
			map.put(value.dom().values[i], subMap);
		}
		//System.out.println(map);
	}
	
	@Override
	public ArrayList<Var> arguments() {
		
		ArrayList<Var> variables = new ArrayList<Var>(list.length + 2);
		variables.add(index);
		variables.add(value);
		
		for (int i = 0; i < list.length; i++)
			variables.add(list[i]);
		
		return variables;
	}

	@Override
	public void consistency(Store store) {
		
		do{
			store.propagationHasOccurred = false;
			
            IntervalDomain indexSet = new IntervalDomain();

			for (int i = 0; i < map.size(); i++) {
				
				ProbabilityRange r = new ProbabilityRange(1,0);
				
				HashMap<Integer, ProbabilityRange> subMap = map.get(value.dom().values[i]);
				
				// TODO: RADEK, What about taking into account the actual domain of the index variable?
                for (ValueEnumeration e = index.dom().valueEnumeration(); e.hasMoreElements();) {
                    int j = e.nextElement();
					r.union(subMap.get(j - offset));
                }

                // TO_DO: What if index is fixed then the constraint should enforce SeqS(V, L[i]) functionality.
                // KRZYSZTOF: This is done by setting probabilities to 0 for values not fulfilling relation.

				// TODO: If list does not hold stochastic constants only then the ranges can
				// change and this should be reflected too. 
				
				value.dom().inElement(store.level, value, value.dom().values[i], r);

                // Checking which indexes are possible
                for (Integer key : subMap.keySet())
                    if (index.dom().contains(key + offset) && subMap.get(key).max > 0.0 )
                        indexSet.addDom(new IntervalDomain(key+offset, key+offset));
            }

            //System.out.println(this.id() + "  "+ indexSet);
            index.domain.in(store.level, index, indexSet);

		} while(store.propagationHasOccurred);
		
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
		
		index.putModelConstraint(this, getConsistencyPruningEvent(index));
		value.putModelConstraint(this, getConsistencyPruningEvent(value));

		for (Var V : list)
			V.putModelConstraint(this, getConsistencyPruningEvent(V));

		store.addChanged(this);
		store.countConstraint();
	}

	@Override
	public void removeConstraint() {
		
		index.removeConstraint(this);
		value.removeConstraint(this);
		for (int i = 0; i < list.length; i++) {
			list[i].removeConstraint(this);
		}
	}

	@Override
	public boolean satisfied() {
		
		for (int i = 0; i < map.size(); i++) {
			
			ProbabilityRange r = new ProbabilityRange(1,0);
			
			HashMap<Integer, ProbabilityRange> subMap = map.get(new Integer(value.dom().values[i]));
			
			for (int j = 0; j < index.getSize(); j++)					
				r.union(subMap.get(new Integer(index.dom().getElementAt(j) - offset)));
			
			if (!value.dom().ProbRanges[i].eq(r))
				return false;
		}
		
		return true;
	}

	@Override
	public String toString() {
		
		StringBuffer result = new StringBuffer( id() );
		
		result.append(" : Element( ");
		for (int i = 0; i < list.length; i++) {
			result.append( list[i] );
			if (i < list.length - 1)
				result.append(", "); 
		}
		result.append(")");
		return result.toString();
	}

	@Override
	public void increaseWeight() {
		
		if (increaseWeight) {
			index.weight++;
			value.weight++;
			for (Var v : list) 
				v.weight++;
		}	
	}

}
