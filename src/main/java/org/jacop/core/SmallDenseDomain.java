/**
 *  SmallDenseDomain.java 
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

package org.jacop.core;

import java.util.ArrayList;
import java.util.Random;

import org.jacop.constraints.Constraint;

/**
 * Defines small dense domain based on bits within a long number. 
 * 
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.2
 */

public class SmallDenseDomain extends IntDomain {


	/**
	 * It is an empty domain returned by default when empty domain becomes a result of 
	 * any function.
	 */
	public static final SmallDenseDomain emptyDomain = new SmallDenseDomain(1, 0L);
	
	/**
	 * The minimal value present in this domain encoding. The 
	 * domain can only encode small domains within a range [min .. min + 63].
	 */
	public int min;
	
	/**
	 * It stores information about presence of the elements in the domain. If 
	 * the least significant bit is set then min + 63 is present. The most
	 * significant bit is always set as this domain maintains invariant that
	 * minimum value always belongs to the domain. 
	 */
	public long bits;

	private boolean singleton;
	
	private int size;
	
	private int max;
	
	/**
	 * It specifies the previous domain which was used by this domain. The old
	 * domain is stored here and can be easily restored if necessary.
	 */

	public IntDomain previousDomain;

	
	/**
	 * It creates an empty domain. 
	 */
	public SmallDenseDomain() {
		
		bits = 0;
		size = 0;
		singleton = false;
		min = Integer.MAX_VALUE;
		max = Integer.MIN_VALUE;
				
	}

	/**
	 * It creates a domain of type small dense. 
	 * 
	 * @param min the minimum value present in this domain. 
	 * @param bits the bits representing presence of any value from the range [ min .. min + 63].
	 */
	public SmallDenseDomain(int min, long bits) {
		
		if (bits != 0) {

			this.min = min;
			this.bits = bits;

			assert (bits != 0) : "Empty Domain not yet allowed";

			adaptMin();
			this.size = getSize(bits);

			if (size == 1)
				this.singleton = true;
			else
				this.singleton = false;

			this.max = min + 63;
			this.max = previousValue(this.min + 64);

		}
		else {
			
			bits = 0;
			size = 0;
			singleton = false;
			min = Integer.MAX_VALUE;
			max = Integer.MIN_VALUE;

		}
				
	}

	/**
	 * It creates a domain with values between min and max inclusive.
	 * @param min
	 * @param max
	 */
	public SmallDenseDomain(int min, int max) {
		
		if (min <= max) {

			this.min = min;

			this.bits = -1;
			this.bits = this.bits << (63 - ( max - min ) );
			this.size = getSize(bits);

			if (size == 1)
				this.singleton = true;
			else
				this.singleton = false;

			this.max = max;

		}
		else {
			
			bits = 0;
			size = 0;
			singleton = false;
			min = Integer.MAX_VALUE;
			max = Integer.MIN_VALUE;
			
		}
		
	}

	
	@Override
	public void addDom(IntDomain domain) {
		
		super.addDom(domain);

	}

	@Override
	public IntDomain complement() {

		IntDomain intervalBasedRepresentation = this.toIntervalDomain();
		
		return intervalBasedRepresentation.complement();

		/*
		 
		// it should not assume that complement is restricted to the range given by small dense domain. 
	
		long result = -1;
		
		result = result ^ bits;
		
		if (result == 0)
			return emptyIntDomain;
		else
			return new SmallDenseDomain(min, result);
		*/
		
	}

    public IntDomain previousDomain() {
        return previousDomain;
    }

	@Override
	public boolean contains(IntDomain domain) {

		if (domain.isEmpty())
			return true;
		
		if (isEmpty())
			return false;
		
		if (domain.min() < this.min || domain.max() > this.max)
			return false;
				
		if (domain.domainID() == IntDomain.SmallDenseDomainID) {
			
			SmallDenseDomain input = (SmallDenseDomain) domain;

			// no problem with shift modulo 64 as it is always lower than 64.
			long bitsResult = this.bits | ( input.bits >>> (input.min - this.min) );

			if (bitsResult != this.bits)
				return false;
			else
				return true;
			
		}
		
		if (size < domain.getSize())
			return false;
		
		
		/* TODO implement special code, 
		if (domain.domainID() == IntDomain.IntervalDomainID) {

			IntervalDomain input = (IntervalDomain) domain;

			assert false;
			
		}
		*/

		boolean result = super.contains(domain);
		
		assert ( result == this.toIntervalDomain().contains(domain)) : "Improper implementation of function contains " + this + "d" + domain;

		return result;
		
	}

	@Override
	public boolean contains(int value) {
		
		// TODO, CHECK.
		if ( value >= min && value <= min + 63 && ( bits & TWO_N_ARRAY[63 - ( value - min )] ) != 0)
			return true;
		else
			return false;
		
	}

	@Override
	public boolean eq(IntDomain domain) {
		
		if (this.isEmpty()) {
			if (domain.isEmpty())
				return true;
			else
				return false;
		}
		else if (domain.isEmpty())
			return false;
		
		if (domain.domainID() == IntDomain.SmallDenseDomainID) {

			SmallDenseDomain input = (SmallDenseDomain) domain;
			
			if (input.min == this.min && input.bits == this.bits)
				return true;
			else
				return false;
			
		}

		if (domain.domainID() == IntDomain.IntervalDomainID) {

			IntervalDomain input = (IntervalDomain) domain;

			if (input.min() != this.min || input.max() != this.max || input.getSize() != this.size ) {
				assert super.eq(domain) == false;
				return false;
			}
			
			for (int i = input.size - 1; i > 0; i--)
				if (isIntersecting(input.intervals[i-1].max + 1, input.intervals[i].min - 1)) {
					assert super.eq(domain) == false;
					return false;
				}
			
			assert ( super.eq(domain) ) : "Incorrect implementation for IntervalDomain and SmallDenseDomain.";
			
			return true;
				
		}
		
		assert checkInvariants() == null : checkInvariants() ;

		// TODO, implement special code, check the super implementation. 
		return super.eq(domain);

	}

	@Override
	public int getElementAt(int index) {

		assert checkInvariants() == null : checkInvariants() ;

		if (index >= getSize())
			throw new IllegalArgumentException("The domain has less elements then index.");
		
		long result = bits;
		int value = min;
		
		while (index > 0) {
			if (result < 0) {
				index--;
			}
			result = result << 1;
			value++;
		}

		while (result > 0) {
			result = result << 1;
			value++;
		}
		
		return value;
		
	}

	@Override
	public Interval getInterval(int position) {
		
		int no = 0;
		int shift = 0;
		long result = bits;
		boolean inInterval = false;
		int begin = Integer.MIN_VALUE;
		
		while (result != 0) {
			if (!inInterval && result < 0) {
				inInterval = true;
				if (no == position)
					begin = min + shift;
				no++;
				result = result << 1;
				shift++;
			}
			if (!inInterval && result > 0) {
				result = result << 1;
				shift++;
			}
			if (inInterval && result < 0) {
				result = result << 1;
				shift++;
			}
			if (inInterval && result >= 0) {
				if (no - 1 == position) {
					return new Interval(begin, min + shift - 1);
				}
				inInterval = false;
				result = result << 1;
				shift++;
			}
		}

		assert false : "Interval with a given number does not exist.";
		return null;

	}

	@Override
	public int getSize() {

		assert (size == getSize(bits)) : "size cache was not updated before correctly";
		
		return size;
		
	}


	/**
	 * It computes the number of 1's in the binary representation of the number given in the field input. 
	 * 
	 * @param input the 64bits for which calculation of number of 1's takes place.
	 * 
	 * @return the number of 1's.
	 * 
	 */
	public int getSize(long input) {

		long xDown = input & 0xffffffffL;
		xDown = xDown - ((xDown >>> 1) & 0x55555555);
		xDown = (xDown & 0x33333333) + ((xDown >>> 2) & 0x33333333);
		xDown = (xDown + (xDown >>> 4)) & 0x0f0f0f0f;
		xDown = xDown + (xDown >>> 8);
		xDown = xDown + (xDown >>> 16);
		
		long xUp = input >>> 32;
		xUp = xUp - ((xUp >>> 1) & 0x55555555);
		xUp = (xUp & 0x33333333) + ((xUp >>> 2) & 0x33333333);
		xUp = (xUp + (xUp >>> 4)) & 0x0f0f0f0f;
		xUp = xUp + (xUp >>> 8);
		xUp = xUp + (xUp >>> 16);
		
		return ((int) xDown & 0x0000003f) + ((int) xUp & 0x0000003f);

	}
	
	/**
	 * It updates the domain to have values only within the interval min..max.
	 * The type of update is decided by the value of stamp. It informs the
	 * variable of a change if it occurred.
	 */
	@Override
	public void in(int storeLevel, Var var, int min, int max) {

		assert checkInvariants() == null : checkInvariants() ;
		
		assert (min <= max) : "Min value greater than max value " + min + " > " + max;

		if (max < this.min)
			throw failException;

		if (min > this.max)
			throw failException;

		if (min <= this.min && max >= this.max)
			return;

        if (singleton)
            return;

		long bitsResult = bits;
		
//		System.out.println( "Starting with " + new SmallDenseDomain(min, bitsResult));
		if (this.max - max > 0) {

			int thisMax = this.min + 63;

			bitsResult = bitsResult >>> (thisMax - max);
//			System.out.println( new SmallDenseDomain(min, bitsResult));
			
			if (min - this.min > 0) {
				bitsResult = bitsResult << ( min - this.min + thisMax - max );
//				System.out.println( new SmallDenseDomain(min, bitsResult));

				bitsResult = bitsResult >>> ( min - this.min );
//				System.out.println( new SmallDenseDomain(min, bitsResult));			
			}
			else {
				bitsResult = bitsResult << ( thisMax - max );
//				System.out.println( new SmallDenseDomain(min, bitsResult));
			}
			

		}
		else {

			if (min - this.min > 0) {
				bitsResult = bitsResult << ( min - this.min );
//				System.out.println( new SmallDenseDomain(min, bitsResult));

				bitsResult = bitsResult >>> ( min - this.min );
//				System.out.println( new SmallDenseDomain(min, bitsResult));			
			}
			else {
				// nothing to prune, it should not be here as this condition is discovered earlier.
				return;
			}
			
		}
		
		int newSize = getSize( bitsResult );

		if (newSize == 0)
			throw failException;
			
//		assert (newSize <= size) : "Incorrect in operation";
		
//		if (newSize == size)
//			return;

		assert (newSize < size) : "Incorrect in operation";
		
		// Pruning has occurred. 
		
		if (stamp == storeLevel) {

			bits = bitsResult;
			size = newSize;
			if (newSize == 1)
				singleton = true;

			int previousMin = min;
			int previousMax = max;
			
			// 1. Find new min.
			if (this.min < min) {
				bits = bits << ( min - this.min );
				this.min = min;
				adaptMin();
			}

			// 2. Find new max. 
			if (this.max > max) {
				this.max = previousValue(max + 1);
			}

			assert (max <= previousMax) : "Domain update incorrect.";
			assert (min >= previousMin) : "Domain update incorrect.";
			
			assert checkInvariants() == null : checkInvariants() ;
			
			if (singleton) {
				var.domainHasChanged(IntDomain.GROUND);
				return;
			} else {
				var.domainHasChanged(IntDomain.BOUND);
				return;
			}


		} else {

			assert stamp < storeLevel;

			SmallDenseDomain result;

			// 1. Find new min.
			if (this.min < min) {
				bitsResult = bitsResult << ( min - this.min );
				result = new SmallDenseDomain(min, bitsResult);
				result.adaptMin();
			}
			else
				result = new SmallDenseDomain(this.min, bitsResult);

			if (newSize == 1)
				result.singleton = true;

			// 2. Find new max. 
			if (this.max > max) {
				result.max = result.previousValue(max + 1);
			}

			assert (result.max <= max) : "Domain update incorrect.";
			assert (result.min >= min) : "Domain update incorrect.";

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = storeLevel;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			((IntVar)var).domain = result;

			assert checkInvariants() == null : checkInvariants() ;
			assert result.checkInvariants() == null : result.checkInvariants() ;

			if (result.singleton()) {
				var.domainHasChanged(IntDomain.GROUND);
				return;
			} else {
				var.domainHasChanged(IntDomain.BOUND);
				return;
			}

		}	
		
	}
	

	private void adaptMin() {
		
		assert (bits != 0) : "Empty domain, min can not be adapted.";

		while ( (bits & first8) == 0 ) {
			min += 8;
			bits = bits << 8;
		}

		while ( (bits & TWO_N_ARRAY[63]) == 0 ) {
			min++;
			bits = bits << 1;
		}
		
	}

	public void in(int storeLevel, Var var, long domain) {
				
		assert checkInvariants() == null : checkInvariants() ;
		
		long bitsResult = bits & domain;
		
		if (bitsResult == bits)
			return;
		
		int newSize = getSize( bitsResult );

		if (newSize == 0)
			throw failException;
			
		// Pruning has occurred. 

		int previousMin = min;
		int previousMax = max;
		
		if (stamp == storeLevel) {

			bits = bitsResult;
			size = newSize;
			if (newSize == 1)
				singleton = true;

			adaptMin();
			max = previousValue(max + 1);

			assert (max <= previousMax) : "Domain update incorrect.";
			assert (min >= previousMin) : "Domain update incorrect.";
			
			assert checkInvariants() == null : checkInvariants() ;
			
			if (singleton) {
				var.domainHasChanged(IntDomain.GROUND);
				return;
			} else {
				
				if (previousMin != min || previousMax != max) {
					var.domainHasChanged(IntDomain.BOUND);
					return;
				}
				else {
					var.domainHasChanged(IntDomain.ANY);
					return;					
				}
			}


		} else {

			assert stamp < storeLevel;

			SmallDenseDomain result = new SmallDenseDomain(min, bitsResult);

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = storeLevel;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			((IntVar)var).domain = result;

			assert (result.max <= previousMax) : "Domain update incorrect.";
			assert (result.min >= previousMin) : "Domain update incorrect.";

			assert checkInvariants() == null : checkInvariants() ;
			assert result.checkInvariants() == null : result.checkInvariants() ;

			if (result.singleton()) {
				var.domainHasChanged(IntDomain.GROUND);
				return;
			} else {
				
				if (previousMin != result.min || previousMax != result.max) {
					var.domainHasChanged(IntDomain.BOUND);
					return;
				}
				else {
					var.domainHasChanged(IntDomain.ANY);
					return;					
				}

			}

		}	

	}

	
	@Override
	public void in(int storeLevel, Var var, IntDomain domain) {
		
		if (domain.singleton()) {
			in(storeLevel, var, domain.value(), domain.value());
			return;
		}
		
		if (domain.domainID() == IntDomain.SmallDenseDomainID) {
			
			SmallDenseDomain input = (SmallDenseDomain) domain;
			
			long inBits;
			
			if (min <= input.min) {
				int shift = input.min - min;
				if (shift < 64)
					inBits = input.bits >>> ( input.min - min );
				else
					inBits = 0;
			}
			else {
				int shift = min - input.min;
				if (shift < 64)
					inBits = input.bits << ( min - input.min );
				else
					inBits = 0;
			}

			in(storeLevel, var, inBits);
			return;
		}

		if (domain.domainID() == IntDomain.IntervalDomainID) {
			
			IntervalDomain input = (IntervalDomain) domain;
				
			int i = 0;
			
			for (; i < input.size; i++) {
				if (input.intervals[i].max < this.min)
					continue;
				else 
					break;
			}

			if ( i == input.size )
				throw Store.failException;
			
			Interval first = input.intervals[i];
			int length = Math.min(first.max, this.max) - Math.max(this.min, first.min);

			if (length == this.max - this.min)
				return;

			if (length < 0)
				throw Store.failException;
			
			long inBits = SEQ_ARRAY[length];			
			
			i++;

			Interval next = null;
			for (; i < input.size; i++) {
				next = input.intervals[i];
				if (next.max > this.max)
					break;
				inBits = inBits << (next.max - input.intervals[i-1].max);
				inBits = inBits | SEQ_ARRAY[next.max - next.min];
				
			}

			inBits = inBits << Math.max(this.max - ( input.intervals[i-1].max ), 0);
			//SmallDenseDomain temp = new SmallDenseDomain(this.min, inBits);

			if (i < input.size && next.min <= this.max) {

				inBits = inBits | SEQ_ARRAY[this.max - ( next.min ) ];
				
			}

			inBits = inBits << ( this.min + 63 - this.max );
			
			//if (inBits == 0)
			//	System.out.println(this + "domain " + domain + " shift " + shift);
			
			//temp = new SmallDenseDomain(this.min, inBits);
			//inBits = inBits << (this.min + 63 - this.max - Math.max(first.min + shift - this.min, 0));
			//System.out.println(this + "domain " + domain + " shift " + shift + " transformed " + temp);

			in(storeLevel, var, inBits);
						
			assert (domain.complement().isIntersecting((IntDomain)var.dom()) == false) : "Error either in in or isIntersecting.";
			
			return;
			
		}

		assert ( domain.max() - domain.min() + 1 == domain.getSize() ) : "Loosing propagation" + domain;

		// TODO, improve, it does not take yet holes in the domain. 
		in(storeLevel, var, domain.min(), domain.max());
	
	}

	@Override
	public void inComplement(int storeLevel, Var var, int complement) {

		assert checkInvariants() == null : checkInvariants() ;

		if (complement < min)
			return;
		if (complement > min + 63)
			return;

		long bitsResult = bits & ~TWO_N_ARRAY[63 - ( complement - min)];

		if (bitsResult == bits)
		    return;  // no change in the domain; ADDED BY KKU

		int newSize = getSize( bitsResult );

		if (newSize == 0)
			throw failException;
			
		assert (newSize <= size) : "Incorrect in operation";
		
		if (newSize == size)
			return;

		// Pruning has occurred. 
		
		if (stamp == storeLevel) {

			boolean boundEvent = false;
			bits = bitsResult;
			size = newSize;
			if (newSize == 1)
				singleton = true;
			
			// TODO, remove asserts which require a local variable to speedup non asserts execution.
			int previousMin = min;
			int previousMax = max;
			
			if (this.min == complement) {
				boundEvent = true;
				adaptMin();
			}
			// 2. Find new max. 
			if (this.max == complement) {
				this.max = previousValue( complement );
				boundEvent = true;
			}

			assert (max <= previousMax) : "Domain update incorrect.";
			assert (min >= previousMin) : "Domain update incorrect.";

			assert checkInvariants() == null : checkInvariants() ;
			
			if (singleton) {
				var.domainHasChanged(IntDomain.GROUND);
				return;
			} else {
				if (boundEvent)
					var.domainHasChanged(IntDomain.BOUND);
				else
					var.domainHasChanged(IntDomain.ANY);
				return;
			}


		} else {

			assert stamp < storeLevel;

			SmallDenseDomain result;

			boolean boundEvent = false;

			result = new SmallDenseDomain(min, bitsResult);

			// 1. Find new min.
			if (this.min == complement) {
				result.adaptMin();
				boundEvent = true;
			}

			if (this.max == complement) {
				boundEvent = true;
				result.max = result.previousValue(max);
				boundEvent = true;
			}

			if (newSize == 1)
				result.singleton = true;

			assert (result.max <= max) : "Domain update incorrect.";
			assert (result.min >= min) : "Domain update incorrect.";

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = storeLevel;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			((IntVar)var).domain = result;

			assert checkInvariants() == null : checkInvariants() ;
			assert result.checkInvariants() == null : result.checkInvariants() ;

			if (result.singleton()) {
				var.domainHasChanged(IntDomain.GROUND);
				return;
			} else {
				if (boundEvent)
					var.domainHasChanged(IntDomain.BOUND);
				else 
					var.domainHasChanged(IntDomain.ANY);

				return;
			}

		}			
		
	}

	@Override
	public void inComplement(int storeLevel, Var var, int minComplement, int maxComplement) {

		assert checkInvariants() == null : checkInvariants() ;

		if (maxComplement < min)
			return;
		
		if (minComplement > max)
			return;
		
		if (minComplement < min)
			minComplement = min;
		
		if (maxComplement > max)
			maxComplement = max;
		
		long bitsResult = bits & ~( SEQ_ARRAY[maxComplement - minComplement] << ( min + 63 - maxComplement ) );

        if (bitsResult == bits)
            return;

        int newSize = getSize( bitsResult );

		if (newSize == 0)
			throw failException;
			
		assert (newSize <= size) : "Incorrect in operation";
		
		if (newSize == size)
			return;

		// Pruning has occurred. 
		
		if (stamp == storeLevel) {

			boolean boundEvent = false;
			bits = bitsResult;
			size = newSize;
			if (newSize == 1)
				singleton = true;
			
			// TODO, remove asserts which require a local variable to speedup non asserts execution.
			int previousMin = min;
			int previousMax = max;
			
			if (this.min == minComplement) {
				boundEvent = true;
				adaptMin();
			}
			// 2. Find new max. 
			if (this.max == maxComplement) {
				this.max = previousValue( maxComplement );
				boundEvent = true;
			}

			assert (max <= previousMax) : "Domain update incorrect.";
			assert (min >= previousMin) : "Domain update incorrect.";

			assert checkInvariants() == null : checkInvariants() ;
			
			if (singleton) {
				var.domainHasChanged(IntDomain.GROUND);
				return;
			} else {
				if (boundEvent)
					var.domainHasChanged(IntDomain.BOUND);
				else
					var.domainHasChanged(IntDomain.ANY);
				return;
			}


		} else {

			assert stamp < storeLevel;

			SmallDenseDomain result;

			boolean boundEvent = false;

			result = new SmallDenseDomain(min, bitsResult);

			// 1. Find new min.
			if (this.min == minComplement) {
				result.adaptMin();
				boundEvent = true;
			}

			if (this.max == maxComplement) {
				boundEvent = true;
				result.max = result.previousValue(max);
				boundEvent = true;
			}

			if (newSize == 1)
				result.singleton = true;

			assert (result.max <= max) : "Domain update incorrect.";
			assert (result.min >= min) : "Domain update incorrect.";

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = storeLevel;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			((IntVar)var).domain = result;

			assert checkInvariants() == null : checkInvariants() ;
			assert result.checkInvariants() == null : result.checkInvariants() ;

			if (result.singleton()) {
				var.domainHasChanged(IntDomain.GROUND);
				return;
			} else {
				if (boundEvent)
					var.domainHasChanged(IntDomain.BOUND);
				else 
					var.domainHasChanged(IntDomain.ANY);

				return;
			}

		}			

	}

	@Override
	public void inMax(int storeLevel, Var var, int max) {

		if (max < min)
			throw Store.failException;

		// TODO, improve.
		in(storeLevel, var, min, max);

	}

	@Override
	public void inMin(int storeLevel, Var var, int min) {

		if (max < min)
			throw Store.failException;

		// TODO, improve.
		in(storeLevel, var, min, max);

	}

	@Override
	public void inShift(int storeLevel, Var var, IntDomain domain, int shift) {
				
		if (domain.domainID() == IntDomain.SmallDenseDomainID) {
			
			SmallDenseDomain input = (SmallDenseDomain) domain;
			
			long inBits;
			
			if (min <= input.min + shift) {
				int internalShift = input.min + shift - min;
				if (internalShift < 64)
					inBits = input.bits >>> internalShift;
				else
					inBits = 0;
			}
			else {
				int internalShift = min - input.min - shift;
				if (internalShift < 64)
					inBits = input.bits << internalShift;
				else
					inBits = 0;
			}

			in(storeLevel, var, inBits);
			return;
		}

		// TODO, create proper assert check for this case.

		if (domain.domainID() == IntDomain.IntervalDomainID) {
			
			IntervalDomain input = (IntervalDomain) domain;
				
			long inBits = 0;
			
			int i = 0;
			
			for (; i < input.size; i++) {
				if (input.intervals[i].max + shift < this.min)
					continue;
				else 
					break;
			}

			if ( i == input.size )
				throw Store.failException;
			
			Interval first = input.intervals[i];
			int length = Math.min(first.max + shift, this.max) - Math.max(this.min, first.min + shift);

			if (length == this.max - this.min)
				return;

			if (length < 0)
				throw Store.failException;
			
			inBits = inBits | SEQ_ARRAY[length];			
			
			i++;

			Interval next = null;
			for (; i < input.size; i++) {
				next = input.intervals[i];
				if (next.max + shift > this.max)
					break;
				inBits = inBits << (next.max - input.intervals[i-1].max);
				inBits = inBits | SEQ_ARRAY[next.max - next.min];
				
			}

			inBits = inBits << Math.max(this.max - ( input.intervals[i-1].max + shift ), 0);
			//SmallDenseDomain temp = new SmallDenseDomain(this.min, inBits);

			if (i < input.size && next.min + shift <= this.max) {

				inBits = inBits | SEQ_ARRAY[this.max - ( next.min + shift ) ];
				
			}

			inBits = inBits << ( this.min + 63 - this.max );
			
			//if (inBits == 0)
			//	System.out.println(this + "domain " + domain + " shift " + shift);
			
			//temp = new SmallDenseDomain(this.min, inBits);
			//inBits = inBits << (this.min + 63 - this.max - Math.max(first.min + shift - this.min, 0));
			//System.out.println(this + "domain " + domain + " shift " + shift + " transformed " + temp);

			in(storeLevel, var, inBits);
			return;
			
		}
		
		
		assert ( domain.max() - domain.min() + 1 == domain.getSize() ) : "Loosing propagation" + domain;

		// TODO, improve, it does not take yet holes in the domain. 
		in(storeLevel, var, domain.min() + shift, domain.max() + shift);

	}

	public SmallDenseDomain intersect(IntervalDomain input, int shift) {
				
		// System.out.println("Domain " + this + " intersecting with " + input);
		
		// TODO, check all return empty domains to make sure that they are not being used 
		// as normal domains (constraints).
		if (isEmpty())
			return SmallDenseDomain.emptyDomain;
		
		long inBits = 0;
		
		int i = 0;
		
		for (; i < input.size; i++) {
			if (input.intervals[i].max + shift < this.min)
				continue;
			else 
				break;
		}

		if ( i == input.size )
			return SmallDenseDomain.emptyDomain;
		
		Interval first = input.intervals[i];
		int length = Math.min(first.max + shift, this.max) - Math.max(this.min, first.min + shift);

		if (length == this.max - this.min)
			return this.cloneLight();

		if (length < 0)
			return SmallDenseDomain.emptyDomain;
		
		inBits = inBits | SEQ_ARRAY[length];			
		
		i++;

		Interval next = null;
		for (; i < input.size; i++) {
			next = input.intervals[i];
			if (next.max + shift > this.max)
				break;
			inBits = inBits << (next.max - input.intervals[i-1].max);
			inBits = inBits | SEQ_ARRAY[next.max - next.min];
			
		}

		inBits = inBits << Math.max(this.max - ( input.intervals[i-1].max + shift ), 0);
		//SmallDenseDomain temp = new SmallDenseDomain(this.min, inBits);

		if (i < input.size && next.min + shift <= this.max) {

			inBits = inBits | SEQ_ARRAY[this.max - ( next.min + shift ) ];
			
		}

		inBits = inBits << ( this.min + 63 - this.max );
		
		inBits = inBits & bits;
		//if (inBits == 0)
		//	System.out.println(this + "domain " + domain + " shift " + shift);
		
		//temp = new SmallDenseDomain(this.min, inBits);
		//inBits = inBits << (this.min + 63 - this.max - Math.max(first.min + shift - this.min, 0));
		//System.out.println(this + "domain " + domain + " shift " + shift + " transformed " + temp);

		return new SmallDenseDomain(this.min, inBits);
		
	}
	
	@Override
	public IntDomain intersect(IntDomain domain) {

		if (domain.domainID() == IntDomain.SmallDenseDomainID) {
			
			SmallDenseDomain input = (SmallDenseDomain) domain;

			if (input.bits == 0)
				return IntDomain.emptyIntDomain;
			
			long inBits;
			
			if (min <= input.min) {
				int shift = input.min - min;
				if (shift < 64)
					inBits = input.bits >>> shift;
				else
					inBits = 0;
			}
			else {
				int shift = min - input.min;
				if (shift < 64)
					inBits = input.bits << shift;
				else
					inBits = 0;
			}

			SmallDenseDomain result = new SmallDenseDomain(min, inBits & bits);

			assert result.checkInvariants() == null : result.checkInvariants() ;
			
			return result;

		}

		if (domain.domainID() == IntDomain.IntervalDomainID) {
			
			IntervalDomain input = (IntervalDomain) domain;
			
			SmallDenseDomain result = intersect(input, 0);
			
			assert result.checkInvariants() == null : result.checkInvariants() ;

			return result;
			
		}

		if (domain.domainID() == IntDomain.BoundDomainID) {
			
		    IntervalDomain input = new IntervalDomain( domain.min(), domain.max());
			
			SmallDenseDomain result = intersect(input, 0);
			
			assert result.checkInvariants() == null : result.checkInvariants() ;

			return result;
			
		}
		
		assert false : "Not implemented for class " + domain.getClass();

		return null;
	}

	@Override
	public IntDomain intersect(int min, int max) {
		
		IntDomain result = this.cloneLight();
		
		result.intersectAdapt(min, max);

		return result;
	}

	@Override
	public int intersectAdapt(IntDomain domain) {
		
		// TODO, do a bit more testing, although code has been derived from in function.
		
	//	System.out.println("i>" + this  + "(" + domain + ")");
		
		if (domain.domainID() == IntDomain.SmallDenseDomainID) {
			
			SmallDenseDomain input = (SmallDenseDomain) domain;

			long inBits;

			if (min <= input.min) {
				int shift = input.min - min;
				if (shift < 64)
					inBits = input.bits >>> shift;
				else
					inBits = 0;
			}
			else {
				int shift = min - input.min;
				if (shift < 64)
					inBits = input.bits << shift;
				else
					inBits = 0;
			}

			assert checkInvariants() == null : checkInvariants() ;

			long bitsResult = bits & inBits;

			if (bitsResult == bits)
				return IntDomain.NONE;

			int newSize = getSize( bitsResult );

			if (newSize == 0) {
				clear();
				return IntDomain.GROUND;
			}

			// Pruning has occurred. 

			int previousMin = min;
			int previousMax = max;

			bits = bitsResult;
			size = newSize;
			if (newSize == 1)
				singleton = true;

			adaptMin();
			max = previousValue(max + 1);

			assert (max <= previousMax) : "Domain update incorrect.";
			assert (min >= previousMin) : "Domain update incorrect.";

			assert checkInvariants() == null : checkInvariants() ;

		//	System.out.println("i<" + this );
			
			if (singleton) {
				return IntDomain.GROUND;
			} else {

				if (previousMin != min || previousMax != max) {
					return IntDomain.BOUND;
				}
				else {
					return IntDomain.ANY;					
				}
			}

		}

		if (domain.domainID() == IntDomain.IntervalDomainID) {
			
			IntervalDomain input = (IntervalDomain) domain;
			
			SmallDenseDomain result = this.intersect(input, 0);

			assert ( result.eq( this.toIntervalDomain().intersect(input) )) : "Intersection not properly computed." + this + "i" + input + "r" + result;

			assert result.checkInvariants() == null : result.checkInvariants() ;

			int previousMin = min;
			int previousMax = max;

			setDomain(result);
			
			if (isEmpty())
				return IntDomain.GROUND;

			if (singleton) {
				return IntDomain.GROUND;
			} else {

				if (previousMin != min || previousMax != max) {
					return IntDomain.BOUND;
				}
				else {
					return IntDomain.ANY;					
				}
			}
			
		}

		if (domain.domainID() == IntDomain.BoundDomainID) {

			// TODO, test this special case.
			BoundDomain input = (BoundDomain) domain;

			int previousMin = min;
			int previousMax = max;

			intersectAdapt(input.min(), input.max());

			if (isEmpty())
				return IntDomain.GROUND;

			if (singleton) {
				return IntDomain.GROUND;
			} else {

				if (previousMin != min || previousMax != max) {
					return IntDomain.BOUND;
				}
				else {
					return IntDomain.ANY;					
				}
			}

		}

		// TODO, used by in functions of BoundSetDomain.
		assert false : "Not implemented for class " + domain.getClass();
		return -1;
		
	}

	@Override
	public int intersectAdapt(int min, int max) {

		// TODO, test, recent code.
		
		if (isEmpty())
			return IntDomain.NONE;

		if (min <= this.min && max >= this.max)
			return IntDomain.NONE;
		
		if (this.max < min || this.min > max) {
			clear();
			return IntDomain.GROUND;
		}
			
		assert checkInvariants() == null : checkInvariants() ;

		min = Math.max(min, this.min);
		max = Math.min(max, this.max);
		
		long result = SEQ_ARRAY[max - min] << ( 63 - ( max - min) );

		bits = ( bits << min - this.min) & result;
		
		this.min = min;
		this.max = max;
		this.size = getSize(bits);
		if (this.size == 1)
			this.singleton = true;
		else
			this.singleton = false;
		
		assert checkInvariants() == null : checkInvariants() ;

		if (!singleton)
			return IntDomain.BOUND;
		else
			return IntDomain.GROUND;
		
	}

	@Override
	public IntervalEnumeration intervalEnumeration() {
		
		return new SmallDenseDomainIntervalEnumeration(this);

	}

	@Override
	public boolean isIntersecting(IntDomain domain) {

		if (domain.isEmpty() || isEmpty())
			return false;
		
		if (domain.domainID() == IntDomain.SmallDenseDomainID) {
			
			SmallDenseDomain input = (SmallDenseDomain) domain;
			
			long inBits;
			
			if (min <= input.min) {
				int shift = input.min - min;
				if (shift < 64)
					inBits = input.bits >>> shift;
				else
					inBits = 0;
			}
			else {
				int shift = min - input.min;
				if (shift < 64)
					inBits = input.bits << shift;
				else
					inBits = 0;
			}

			inBits = inBits & bits;
			
			if (inBits != 0) {
				assert (super.isIntersecting(domain)) : "isIntersecting not properly implemented";
				return true;
			}
			else {
				assert (!super.isIntersecting(domain)) : "isIntersecting not properly implemented";
				return false;
			}
		}

		boolean result = super.isIntersecting(domain);
						
		assert (result == this.toIntervalDomain().isIntersecting(domain)) : "isIntersecting not properly implemented." + this + "d" + domain + "result " + result;

		return result;
		
	}

	@Override
	public boolean isIntersecting(int min, int max) {

		assert (min <= max) : "Illegal arguments min is greater than max";
		
		// TODO, test.
		
		if (this.max < min || this.min > max)
			return false;
		
		long result = bits;
		
		int shiftLeft = min - this.min;
		
		if (shiftLeft > 0)
			result = result << shiftLeft;
		
		if (result < 0)
			return true;
		
		if (shiftLeft > 0) {
			result = result >>>  shiftLeft;
		    result = result >>> Math.max(0, 63 + this.min - max);
		}
		else 
			result = result >>> Math.max(0, 63 + this.min - max);
					
		if ( result != 0 )
			return true;
		else
			return false;
		
		// Used in AbsXeqY, Regular.
	}

	@Override
	public int leftElement(int intervalNo) {
		
		return super.leftElement(intervalNo);

	}

	@Override
	public int max() {
		
		assert ( bits != 0 ) : "max function called for an empty domain";
		
		return max;
		
	}

	@Override
	public int min() {
		
		assert ( (bits & TWO_N_ARRAY[63]) != 0) : "Inconsistent field min when compared to bits." + this;
		
		return min;
		
	}

	long first8 = 255L << 56;
	
	@Override
	public int nextValue(int value) {

		assert ( checkInvariants() == null ) : checkInvariants();

		long temp = bits;
		
		if (value < min)
			return min;
		
		int shift = value - this.min + 1;
		
		if (shift < 64)
			temp = temp << shift;
		else 
			temp = 0;

		if (temp == 0)
			return value;

		while (true) {
			
			long sequence8 = temp & first8;

			if (sequence8 == 0) {
				temp = temp << 8;
				shift += 8;
				continue;
			}
			else {
				for (int i = 7; i >= 0; i--) {
					if ( temp < 0 )
						return min + shift;
					else {
						temp = temp << 1;
						shift++;
					}
				}
				
				assert false : "It should not be here.";
					
			}
		}

	}

	@Override
	public int noIntervals() {
		
		int no = 0;
		long result = bits;
		boolean inInterval = false;
		
		while (result != 0) {
			if (!inInterval && result < 0) {
				inInterval = true;
				no++;
				result = result << 1;
			}
			if (inInterval && result > 0) {
				inInterval = false;
				result = result << 1;
			}
			if (inInterval && result < 0) {
				result = result << 1;
			}
			if (!inInterval && result > 0) {
				result = result << 1;
			}
				
		}

		return no;
	}

	@Override
	public int previousValue(int value) {
		
		assert ( checkInvariants() == null ) : checkInvariants();
		
		long temp = bits;
		int shift = this.min + 63 - Math.min( max, value - 1);
		
		if ( shift < 64 )
			temp = temp >>> shift;
		else
			temp = 0;

		if (temp == 0)
			return value;

		while (true) {
			
			long sequence8 = temp & 255;

			if (sequence8 == 0) {
				temp = temp >>> 8;
				shift += 8;
				continue;
			}
			else {
				for (int i = 7; i >= 0; i--) {
					if ( (temp & 0x1) != 0)
						return min + 63 - shift;
					else {
						temp = temp >>> 1;
						shift++;
					}
				}
				
				assert false : "It should not be here.";
					
			}
		}

		
	}

	@Override
	public IntDomain recentDomainPruning(int storeLevel) {
		
		// TODO, CHECK.
		
		if (previousDomain == null)
			return IntervalDomain.emptyDomain;

		if (stamp < storeLevel)
			return IntervalDomain.emptyDomain;

		IntDomain previous = this.previousDomain;
		while (previous.stamp > storeLevel) {
			if (previous.domainID() == SmallDenseDomainID)
				previous = ((SmallDenseDomain)previous).previousDomain;
			else 
				if (previous.domainID() == IntervalDomainID)
					previous = ((IntervalDomain)previous).previousDomain;
		}

		if (previous.domainID() == SmallDenseDomainID) {

			SmallDenseDomain _previous = (SmallDenseDomain)previous;
			long result = _previous.bits;
			long current = this.bits >>> (this.min - _previous.min);

			return new SmallDenseDomain(_previous.min, result ^ current);
			
		}

		return previous.subtract(this);
					
	}

	@Override
	public int rightElement(int intervalNo) {

		return super.rightElement(intervalNo);
		
	}

	@Override
	public void setDomain(IntDomain domain) {

		// TODO, test it a bit more. SETADD.

		if (domain.isEmpty()) {
			clear();
			return;
		}
			
		if (domain.max() - domain.min() > 63)
			throw new IllegalArgumentException("The resulting domain can not be handled properly by " + this.getClass());			
			
		assert checkInvariants() == null : checkInvariants() ;
		
		if (domain.domainID() == SmallDenseDomainID) {

			SmallDenseDomain smallDomain = (SmallDenseDomain) domain;

			this.bits = smallDomain.bits;
			this.min = smallDomain.min;
			this.max = smallDomain.max;
			this.size = smallDomain.size;
			this.singleton = smallDomain.singleton;
			
			return;
		}
		
		if (domain.isSparseRepresentation()) {	
			
			this.clear();
			
			ValueEnumeration enumer = domain.valueEnumeration();
			
			while (enumer.hasMoreElements()) {
				
				int next = enumer.nextElement();
				
				if (this.contains(next))
					this.unionAdapt(next, next);
			}			
		
			return;
			
		}
		else {

			this.clear();
			
			IntervalEnumeration enumer = domain.intervalEnumeration();
			
			while (enumer.hasMoreElements())				
				this.unionAdapt(enumer.nextElement());
			
			return;
		}

	}

	@Override
	public void setDomain(int min, int max) {

		// TODO, test recent change.
		this.min = min;

		this.bits = -1;
		this.bits = this.bits << (63 - ( max - min ) );
		this.size = getSize(bits);
		if (size == 1)
			this.singleton = true;
		else
			this.singleton = false;

		this.max = max;

	}

	@Override
	public boolean singleton(int c) {

		// TODO, check asserts.
		// It is used by Lex in set package.
		
		assert checkInvariants() == null : checkInvariants() ;

		return size == 1 && c == min;
		
	}

	@Override
	public int sizeOfIntersection(IntDomain domain) {
		
		return super.sizeOfIntersection(domain);

	}

	@Override
	public IntDomain subtract(int value) {
		
		assert checkInvariants() == null : checkInvariants() ;

		// Used in set package, BoundSetDomain.
		IntDomain result = subtract(value, value);
		
		assert result.checkInvariants() == null : result.checkInvariants() ;

		return result;
		
	}

	@Override
	public IntDomain subtract(IntDomain domain) {
		
		if (domain.domainID() == IntDomain.SmallDenseDomainID) {
			
			SmallDenseDomain input = (SmallDenseDomain) domain;
			
			long negBits;
			
			if (input.min >= this.min) {
				int shift = input.min - this.min;
				if (shift < 64)
					negBits = input.bits >>> shift;
				else
					negBits = 0;
			}
			else {	
				int shift = this.min - input.min;
				if (shift < 64)
					negBits = input.bits << shift;
				else
					negBits = 0;
			}
			
			long result = this.bits & ( ~negBits );
			
			if (result != 0)
				return new SmallDenseDomain(this.min, result);
			else
				return SmallDenseDomain.emptyIntDomain;
			
		}
			
		// assert false;
		
		// TODO CRUCIAL implement special function for IntervalDomain. 
		
		IntDomain result = super.subtract(domain);
		
		assert ( result.eq( this.toIntervalDomain().subtract(domain))) : "Subtraction not properly implemented " + this + "d " + domain + "res" + result;

		assert result.checkInvariants() == null : result.checkInvariants() ;
		
		return result;

	}

	@Override
	public void subtractAdapt(int min, int max) {
		
	//	System.out.println("s>" + this  + "(" + min + ", " + max + ")");
		
		assert checkInvariants() == null : checkInvariants() ;

		if (min > this.max || max < this.min)
			return;
		
		min = Math.max(min, this.min);
		max = Math.min(max, this.max);
		
		// TODO, Test properly.	SETADD
		
		bits = bits & ~( SEQ_ARRAY[max - min] << ( 63 - ( max - min ) - (min - this.min) ) );

		if (bits == 0) {
			// it became empty. 
			size = 0;
			singleton = false;
			min = Integer.MAX_VALUE;
			max = Integer.MIN_VALUE;
			return;
		}

		this.size = getSize(bits);
		if (this.size == 1)
			this.singleton = true;
		else
			this.singleton = false;

		if (min <= this.min) {

			if (max < this.max) {

				// min <= this.min
				// max < this.max
				adaptMin();
				
			}
			
		}
		else {
			// min > this.min
			
			if (max >= this.max) {
			
				this.max = previousValue(min);
				
			}
			else {
				// min > this.min
				// max < this.max
				// no changes to min and max
			}			
		}

		
	}

	
	
	@Override
	public IntDomain subtract(int min, int max) {
		
	//	System.out.println("s>" + this  + "(" + min + ", " + max + ")");
		
		assert checkInvariants() == null : checkInvariants() ;

		if (min > this.max || max < this.min)
			return this.cloneLight();
		
		min = Math.max(min, this.min);
		max = Math.min(max, this.max);
		
		// TODO, Test properly.	SETADD
		
		long result = this.bits & ~( SEQ_ARRAY[max - min] << ( 63 - ( max - min ) - (min - this.min) ) );

		if (result == 0)
			return SmallDenseDomain.emptyIntDomain;
		else {
			SmallDenseDomain returnObj = new SmallDenseDomain(this.min, result);
			assert returnObj.checkInvariants() == null : returnObj.checkInvariants() ;
			
	//		System.out.println("s<" + returnObj  );
			return returnObj;
		}
		
	}

	@Override
	public void subtractAdapt(int value) {

		assert checkInvariants() == null : checkInvariants() ;

		// TODO test, SETADD.
		
		if ( !contains(value) )
			return;
		
	//	System.out.println("s>" + this  + "(" + value + ")");
		
		if (singleton) {
			clear();
			return;
		}
		
		bits = bits & ~TWO_N_ARRAY[ min - value + 63 ];

		size--;
		
		if (size == 1)
			singleton = true;

		if (value == min)
			adaptMin();
		
		if (value == max)
			max = previousValue(value);		

	//	System.out.println("s<" + this);
		
		assert checkInvariants() == null : checkInvariants() ;
		
		

	}

	@Override
	public IntDomain union(IntDomain domain) {

		// TODO, test it.
		
		if (domain.domainID() == IntDomain.SmallDenseDomainID) {
			
			SmallDenseDomain input = (SmallDenseDomain) domain;

			int newMax = Math.max(this.max, input.max);

			if (this.min <= input.min) {

				assert (this.min + 63 >= newMax) : "Union of two SmallDenseDomain does not fit in SmallDenseDomain";
				
				long bitsResult = this.bits | ( input.bits >>> (input.min - this.min) );

				return new SmallDenseDomain(this.min, bitsResult);
				
			}
			else {

				assert (input.min + 63 >= newMax) : "Union of two SmallDenseDomain does not fit in SmallDenseDomain";
				
				long bitsResult = input.bits | ( this.bits >>> (this.min - input.min) );

				return new SmallDenseDomain(input.min, bitsResult);

			}
			
		}

		// assert false;
		
		// TODO, take care in a nice fashion (no exception) if smalldensedomain can not handle the result of union.
		IntDomain result = super.union(domain);
		
		assert (result.eq( this.toIntervalDomain().union(domain))) : "Union not properly implemented " + this + "d" + domain + "res" + result;
		
		assert result.checkInvariants() == null : result.checkInvariants() ;

		return result;
		
	}

	@Override
	public IntDomain union(int min, int max) {
		
		IntDomain result = this.cloneLight();

		result.unionAdapt(min, max);
		
		return result;
		
	}

	@Override
	public IntDomain union(int value) {

		IntDomain result = union(value, value);

		assert result.checkInvariants() == null : result.checkInvariants() ;

		return result;
		
	}

	@Override
	public void unionAdapt(Interval i) {
		
		unionAdapt(i.min, i.max);

	}

	@Override
	public void unionAdapt(int min, int max) {

	//	System.out.println("u>" + this  + "(" + min + ", " + max + ")");
		
		assert checkInvariants() == null : checkInvariants() ;

		// TODO, Test properly. SETADD.
		
		long result = SEQ_ARRAY[max - min] << ( 63 - ( max - min) );

		if (isEmpty()) {
			
			this.bits = result;
			this.min = min;
			this.max = max;
			this.size = max - min + 1;
			if (this.size == 1)
				this.singleton = true;
			else
				this.singleton = false;
			
			assert checkInvariants() == null : checkInvariants() ;

			return;
			
		}

		int newMax = Math.max(this.max, max);
		int newMin = Math.min(this.min, min);
		
		if (newMax - newMin > 63)
			throw new IllegalArgumentException("The resulting domain can not be handled properly by " + this.getClass());
		
		result = result >>> Math.max( min - newMin, 0) | ( bits >>> Math.max( this.min - newMin, 0) );
		
		this.bits = result;
		this.min = newMin;
		this.max = newMax;
		this.size = getSize(result);
		if (this.size == 1)
			this.singleton = true;
		else
			this.singleton = false;
		
		assert checkInvariants() == null : checkInvariants() ;

	//	System.out.println("u<" + this);

	}

	@Override
	public void unionAdapt(int value) {

		unionAdapt(value, value);
		
	}

	@Override
	public ValueEnumeration valueEnumeration() {
		
		// TODO, CHECK.
		return new SmallDenseDomainValueEnumeration(this);

	}

	@Override
	public String checkInvariants() {
		
		assert (singleton || getSize(bits) != 1) : "Singleton value was not recognized";

		if (bits != 0) 
			min();
		
		return null;

	}

	@Override
	public void clear() {
		
		bits = 0;
		size = 0;
		singleton = false;
		min = Integer.MAX_VALUE;
		max = Integer.MIN_VALUE;
		
	}

	@Override
	public Domain clone() {
		
		assert checkInvariants() == null : checkInvariants() ;
		
		SmallDenseDomain cloned = new SmallDenseDomain(min, bits);

		cloned.stamp = stamp;
		cloned.previousDomain = previousDomain;

		cloned.searchConstraints = searchConstraints;
		cloned.searchConstraintsToEvaluate = searchConstraintsToEvaluate;

		cloned.modelConstraints = modelConstraints;
		cloned.modelConstraintsToEvaluate = modelConstraintsToEvaluate;

		cloned.searchConstraintsCloned = searchConstraintsCloned;

		return cloned;

	}

	@Override
	public int domainID() {
		
		return SmallDenseDomainID;

	}

	@Override
	public boolean isEmpty() {
		
		// TODO, CHECK.
		if (bits == 0)
			return true;
		else
			return false;
		
	}

	@Override
	public boolean isNumeric() {

		return true;
		
	}

	@Override
	public boolean isSparseRepresentation() {
		
		// TODO, adapt the answer depending on the particular instance 
		// (e.g. it should return false for dense domains).
		return true;
	
	}


	/**
	 * It clones the domain object, only data responsible for encoding domain
	 * values is cloned. All other fields must be set separately.
	 * @return It returns a clone of this domain.
	 */

	public SmallDenseDomain cloneLight() {

		assert checkInvariants() == null : checkInvariants() ;
		
		SmallDenseDomain cloned = new SmallDenseDomain( this.min, this.bits );

		return cloned;
		
	}

	// TODO, put putModelConstraint inside IntDomain to reduce coding.
	
	/**
	 * It adds a constraint to a domain, it should only be called by
	 * putConstraint function of Variable object. putConstraint function from
	 * Variable must make a copy of a vector of constraints if vector was not
	 * cloned.
	 */

	@Override
	public void putModelConstraint(int storeLevel, Var var, Constraint C,
			int pruningEvent) {

		if (stamp < storeLevel) {

			SmallDenseDomain result = this.cloneLight();

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = storeLevel;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			((IntVar)var).domain = result;

			result.putModelConstraint(storeLevel, var, C, pruningEvent);
			return;
		}

		Constraint[] pruningEventConstraints = modelConstraints[pruningEvent];

		if (pruningEventConstraints != null) {

			boolean alreadyImposed = false;

			if (modelConstraintsToEvaluate[pruningEvent] > 0)
				for (int i = pruningEventConstraints.length - 1; i >= 0; i--)
					if (pruningEventConstraints[i] == C)
						alreadyImposed = true;

			int pruningConstraintsToEvaluate = modelConstraintsToEvaluate[pruningEvent];

			if (!alreadyImposed) {
				Constraint[] newPruningEventConstraints = new Constraint[pruningConstraintsToEvaluate + 1];

				System.arraycopy(pruningEventConstraints, 0,
						newPruningEventConstraints, 0,
						pruningConstraintsToEvaluate);
				newPruningEventConstraints[pruningConstraintsToEvaluate] = C;

				Constraint[][] newModelConstraints = new Constraint[3][];

				newModelConstraints[0] = modelConstraints[0];
				newModelConstraints[1] = modelConstraints[1];
				newModelConstraints[2] = modelConstraints[2];

				newModelConstraints[pruningEvent] = newPruningEventConstraints;

				modelConstraints = newModelConstraints;

				int[] newModelConstraintsToEvaluate = new int[3];

				newModelConstraintsToEvaluate[0] = modelConstraintsToEvaluate[0];
				newModelConstraintsToEvaluate[1] = modelConstraintsToEvaluate[1];
				newModelConstraintsToEvaluate[2] = modelConstraintsToEvaluate[2];

				newModelConstraintsToEvaluate[pruningEvent]++;

				modelConstraintsToEvaluate = newModelConstraintsToEvaluate;

			}

		} else {

			Constraint[] newPruningEventConstraints = new Constraint[1];

			newPruningEventConstraints[0] = C;

			Constraint[][] newModelConstraints = new Constraint[3][];

			newModelConstraints[0] = modelConstraints[0];
			newModelConstraints[1] = modelConstraints[1];
			newModelConstraints[2] = modelConstraints[2];

			newModelConstraints[pruningEvent] = newPruningEventConstraints;

			modelConstraints = newModelConstraints;

			int[] newModelConstraintsToEvaluate = new int[3];

			newModelConstraintsToEvaluate[0] = modelConstraintsToEvaluate[0];
			newModelConstraintsToEvaluate[1] = modelConstraintsToEvaluate[1];
			newModelConstraintsToEvaluate[2] = modelConstraintsToEvaluate[2];

			newModelConstraintsToEvaluate[pruningEvent] = 1;

			modelConstraintsToEvaluate = newModelConstraintsToEvaluate;

		}

	}

	@Override
	public void putSearchConstraint(int storeLevel, Var var, Constraint C) {
		
		if (!searchConstraints.contains(C)) {

			if (stamp < storeLevel) {

				SmallDenseDomain result = this.cloneLight();

				result.modelConstraints = modelConstraints;

				result.searchConstraints = new ArrayList<Constraint>(
						searchConstraints.subList(0,
								searchConstraintsToEvaluate));
				result.searchConstraintsCloned = true;
				result.stamp = storeLevel;
				result.previousDomain = this;
				result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
				result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
				((IntVar)var).domain = result;

				result.putSearchConstraint(storeLevel, var, C);
				return;
			}

			if (searchConstraints.size() == searchConstraintsToEvaluate) {
				searchConstraints.add(C);
				searchConstraintsToEvaluate++;
			} else {
				// Exchange the first satisfied constraint with just added
				// constraint
				// Order of satisfied constraints is not preserved

				if (searchConstraintsCloned) {
					Constraint firstSatisfied = searchConstraints
							.get(searchConstraintsToEvaluate);
					searchConstraints.set(searchConstraintsToEvaluate, C);
					searchConstraints.add(firstSatisfied);
					searchConstraintsToEvaluate++;
				} else {
					searchConstraints = new ArrayList<Constraint>(
							searchConstraints.subList(0,
									searchConstraintsToEvaluate));
					searchConstraintsCloned = true;
					searchConstraints.add(C);
					searchConstraintsToEvaluate++;
				}
			}
		}

	}

	@Override
	public void removeLevel(int level, Var var) {
		
		assert (this.stamp <= level);

		if (this.stamp == level) {

			((IntVar)var).domain = this.previousDomain;
		}

		assert (((IntVar)var).domain.stamp < level);

	}

	@Override
	public void removeModelConstraint(int storeLevel, Var var, Constraint c) {
		
		if (stamp < storeLevel) {

			SmallDenseDomain result = this.cloneLight();

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = storeLevel;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			((IntVar)var).domain = result;

			result.removeModelConstraint(storeLevel, var, c);
			return;
		}

		int pruningEvent = IntDomain.GROUND;

		Constraint[] pruningEventConstraints = modelConstraints[pruningEvent];

		if (pruningEventConstraints != null) {

			boolean isImposed = false;

			int i;

			for (i = modelConstraintsToEvaluate[pruningEvent] - 1; i >= 0; i--)
				if (pruningEventConstraints[i] == c) {
					isImposed = true;
					break;
				}

			if (isImposed) {

				if (i != modelConstraintsToEvaluate[pruningEvent] - 1) {

					modelConstraints[pruningEvent][i] = modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1];

					modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1] = c;
				}

				int[] newModelConstraintsToEvaluate = new int[3];

				newModelConstraintsToEvaluate[0] = modelConstraintsToEvaluate[0];
				newModelConstraintsToEvaluate[1] = modelConstraintsToEvaluate[1];
				newModelConstraintsToEvaluate[2] = modelConstraintsToEvaluate[2];

				newModelConstraintsToEvaluate[pruningEvent]--;

				modelConstraintsToEvaluate = newModelConstraintsToEvaluate;

				return;

			}

		}

		pruningEvent = IntDomain.BOUND;

		pruningEventConstraints = modelConstraints[pruningEvent];

		if (pruningEventConstraints != null) {

			boolean isImposed = false;

			int i;

			for (i = modelConstraintsToEvaluate[pruningEvent] - 1; i >= 0; i--)
				if (pruningEventConstraints[i] == c) {
					isImposed = true;
					break;
				}

			if (isImposed) {

				if (i != modelConstraintsToEvaluate[pruningEvent] - 1) {

					modelConstraints[pruningEvent][i] = modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1];

					modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1] = c;
				}

				int[] newModelConstraintsToEvaluate = new int[3];

				newModelConstraintsToEvaluate[0] = modelConstraintsToEvaluate[0];
				newModelConstraintsToEvaluate[1] = modelConstraintsToEvaluate[1];
				newModelConstraintsToEvaluate[2] = modelConstraintsToEvaluate[2];

				newModelConstraintsToEvaluate[pruningEvent]--;

				modelConstraintsToEvaluate = newModelConstraintsToEvaluate;

				return;

			}

		}

		pruningEvent = IntDomain.ANY;

		pruningEventConstraints = modelConstraints[pruningEvent];

		if (pruningEventConstraints != null) {

			boolean isImposed = false;

			int i;

			for (i = modelConstraintsToEvaluate[pruningEvent] - 1; i >= 0; i--)
				if (pruningEventConstraints[i] == c) {
					isImposed = true;
					break;
				}

			// int pruningConstraintsToEvaluate =
			// modelConstraintsToEvaluate[pruningEvent];

			if (isImposed) {

				if (i != modelConstraintsToEvaluate[pruningEvent] - 1) {

					modelConstraints[pruningEvent][i] = modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1];

					modelConstraints[pruningEvent][modelConstraintsToEvaluate[pruningEvent] - 1] = c;
				}

				int[] newModelConstraintsToEvaluate = new int[3];

				newModelConstraintsToEvaluate[0] = modelConstraintsToEvaluate[0];
				newModelConstraintsToEvaluate[1] = modelConstraintsToEvaluate[1];
				newModelConstraintsToEvaluate[2] = modelConstraintsToEvaluate[2];

				newModelConstraintsToEvaluate[pruningEvent]--;

				modelConstraintsToEvaluate = newModelConstraintsToEvaluate;

			}

		}

	}

	@Override
	public void removeSearchConstraint(int storeLevel, Var var, int position,
			Constraint C) {
		
		if (stamp < storeLevel) {

			SmallDenseDomain result = this.cloneLight();

			result.modelConstraints = modelConstraints;
			result.searchConstraints = searchConstraints;
			result.stamp = storeLevel;
			result.previousDomain = this;
			result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
			result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
			((IntVar)var).domain = result;

			result.removeSearchConstraint(storeLevel, var, position, C);
			return;
		}

		assert (stamp == storeLevel);

		assert (searchConstraints.get(position) == C) : "Position of the removed constraint not specified properly";
		
		if (position < searchConstraintsToEvaluate) {

			searchConstraints.set(position, searchConstraints
					.get(searchConstraintsToEvaluate - 1));
			searchConstraints.set(searchConstraintsToEvaluate - 1, C);
			searchConstraintsToEvaluate--;

		}

	}

	@Override
	public boolean singleton() {

		assert checkInvariants() == null : checkInvariants() ;

		return singleton;
	}

	@Override
	public int sizeConstraintsOriginal() {
		
		IntDomain domain = this;

		while (domain.domainID() == SmallDenseDomainID) {

			SmallDenseDomain dom = (SmallDenseDomain) domain;

			if (dom.previousDomain != null)
				domain = dom.previousDomain;
			else
				break;
		}
	
		if (domain.domainID() == SmallDenseDomainID)
			return (domain.modelConstraintsToEvaluate[0]
					+ domain.modelConstraintsToEvaluate[1] + domain.modelConstraintsToEvaluate[2]);
		else
			return domain.sizeConstraintsOriginal();

	}

	
	private static final long[] TWO_N_ARRAY = new long[] { 0x1L, 0x2L, 0x4L,
		                    0x8L, 0x10L, 0x20L, 0x40L, 0x80L, 0x100L, 0x200L, 0x400L, 0x800L,
		                    0x1000L, 0x2000L, 0x4000L, 0x8000L, 0x10000L, 0x20000L, 0x40000L,
		                    0x80000L, 0x100000L, 0x200000L, 0x400000L, 0x800000L, 0x1000000L,
		                    0x2000000L, 0x4000000L, 0x8000000L, 0x10000000L, 0x20000000L,
		                    0x40000000L, 0x80000000L, 0x100000000L, 0x200000000L, 0x400000000L,
		                    0x800000000L, 0x1000000000L, 0x2000000000L, 0x4000000000L,
		                    0x8000000000L, 0x10000000000L, 0x20000000000L, 0x40000000000L,
		                    0x80000000000L, 0x100000000000L, 0x200000000000L, 0x400000000000L,
		                    0x800000000000L, 0x1000000000000L, 0x2000000000000L,
		                    0x4000000000000L, 0x8000000000000L, 0x10000000000000L,
		                    0x20000000000000L, 0x40000000000000L, 0x80000000000000L,
		                    0x100000000000000L, 0x200000000000000L, 0x400000000000000L,
		                    0x800000000000000L, 0x1000000000000000L, 0x2000000000000000L,
		                    0x4000000000000000L, 0x8000000000000000L };

	private static final long[] SEQ_ARRAY = new long[64];

	static {
	
		SEQ_ARRAY[0] = 1L;
		
		for (int i = 1; i < 64; i++)
			SEQ_ARRAY[i] = ( SEQ_ARRAY[i-1] << 1 ) + 1;
		
	}
	
	
	
	@Override
	public String toString() {

		/*
		StringBuilder sb = new StringBuilder(66);
		
		sb.append('{').append(min).append(", ");

		for (int j = 63; j >= 0; j--)
			if (((bits & (TWO_N_ARRAY[j])) != 0))
				sb.append("1");
			else
				sb.append("0");
		
		sb.append(", ").append(max).append('}');
		
		return sb.toString();
		*/
		
		/*
		StringBuilder sb = new StringBuilder(66);
		
		sb.append("{ ");
		
		for (int j = 63; j >= 0; j--)
			if (((bits & (TWO_N_ARRAY[j])) != 0))
				sb.append(String.valueOf( min + 63 - j)).append(" ");
		
		sb.append('}');
		
		return sb.toString();
		*/
		
		return this.toIntervalDomain().toString();
		
	}


	@Override
	public String toStringConstraints() {
		
		// TODO, implement properly. 
		return toString();

	}

	@Override
	public String toStringFull() {
		
		// TODO, implement properly.
		return toString();

	}

	private final static Random generator = new Random();

	@Override
	public int getRandomValue() {
		
		int number = generator.nextInt(size);
		int pos = 0;
		long temp = bits;
		while (number >= 0) {
			if (temp < 0 ) {
				if (number == 0)
					return min + pos;
				number--;
				temp = temp << 1;
			}
			else
				temp = temp << 1;
			pos++;
		}

		assert false;
		return min;
	}

	@Override
	public boolean contains(int min, int max) {

		// TODO, test more.
		if (min < this.min)
			return false;
		
		if (max > this.max)
			return false;

		long result = bits;

		result = result << min - this.min;
		result = result >>> (min - this.min );
		result = result >>> ( this.min + 63 - max );
		
		// SmallDenseDomain temp = new SmallDenseDomain(this.min, result);
		
		if (max - min + 1 != this.getSize(result))
			return false;

	//	System.out.println( this + " contains " + " min " + min + " max " + max );

		return true;
	}
	
	/**
	 * It shifts the domain. 
	 * 
	 * @param shift how much should the domain be shifted.
	 */
	public void shift(int shift) {
		
		min += shift;
		max += shift;
				
	}

	public IntervalDomain toIntervalDomain() {
	
		int noIntervals = this.noIntervals();
		IntervalDomain result = new IntervalDomain(noIntervals);
		
		for (int i = 0; i < noIntervals; i++)
			result.intervals[i] = this.getInterval(i);
		
		result.size = noIntervals;
		
		return result;
	}
	
	
}
