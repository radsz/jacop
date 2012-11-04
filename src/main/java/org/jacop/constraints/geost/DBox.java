/**
 *  DBox.java 
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

package org.jacop.constraints.geost;

import java.util.Arrays;
import java.util.Collection;

import org.jacop.util.SimpleArrayList;


/**
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 *
 */

public class DBox {
	
	// TODO what is the difference between transientInstances and freeBoxes?
	
	/**
	 * TODO, finish the comment.
	 * 
	 * static instance that can be used to avoid allocating
	 * new resources each time a DBox needs to be returned;
	 * modify the static instance using getAllocatedInstance(dim)
	 * instead
	 */
	public static final SimpleArrayList<DBox> transientInstances = new SimpleArrayList<DBox>();
	
	/**
	 * static store of available boxes, accessible by dimension. This makes it possible to
	 * reuse previously used boxes that are not used anymore. The user should use dispatchBox()
	 * to get rid of a box that is not needed anymore, and newBox(dimension) to get a new one.
	 */
	public final static SimpleArrayList<SimpleArrayList<DBox>> freeBoxes = new SimpleArrayList<SimpleArrayList<DBox>>();
	
	/**
	 * It specifies point in n-dimensional space where the dbox originates from.
	 */
	public final int[] origin;
	
	/**
	 * It specifies for each dimension the length of dbox in that dimension. 
	 */
	public final int[] length;
	
	/**
	 * a static collection to use for some operations. Use it instead of creating a new list when
	 * only a temporary list is needed.
	 */
	private static final SimpleArrayList<DBox> workingList = new SimpleArrayList<DBox>();

	/**
	 * It makes sure that there is a slot of the given dimension in the slot.
	 * 
	 * It has to be called at least once before using newBox() and dispatchBox().
	 * 
	 * @param dimension 
	 */
	public static final void supportDimension(int dimension) {
		
		int size = freeBoxes.size();
		
		if(size <= dimension)
			for(int i = size; i <= dimension; i++) {
				freeBoxes.add(new SimpleArrayList<DBox>());
				transientInstances.add(new DBox(new int[i], new int[i]));
			}
		
	}
	
	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"origin", "length"};

	/**
	 * constructs a new Box. The parameter arrays are not copied.
	 * 
	 * @param origin it specifies the origin of the DBox in the n-dimensional space.
	 * @param length it specifies the length of the Dbox in the n-dimensional space.
	 */
	public DBox(int[] origin, int[] length) {

		// TODO what for super()?
		super();
		
		this.origin = origin;
		this.length = length;
		
		assert (checkInvariants() == null) : checkInvariants();
		
	}

	/**
	 * It checks whether the DBox is consistent.
	 * 
	 * @return It returns the string description of the problem, or null if no problem 
	 * with data structure consistency encountered. 
	 */
	public String checkInvariants() {
		
		if(this.origin.length != this.length.length)
			return "The dimension mismatch between origin and length arrays";
		
		for(int i = 0; i < length.length; i++)
			if(length[i] < 0) 
				return "negative length on dimension " + i + "encounterred.";
		
		return null;
	}
	
	/**
	 * It allows the system to reuse the given box by placing it into the pool of
	 * allocated boxes. After calling this function, the caller must not keep any reference
	 * to the box, as the box may be arbitrary changed by any future owner. 
	 * 
	 * @param unusedBox the not used DBox which is being recycled.
	 */
	public static final void dispatchBox(DBox unusedBox) {
		
		// TODO, Can it be only one transient instance at given index?
		// This assert looks suspicous.
		
		assert unusedBox != transientInstances.get(unusedBox.origin.length) 
			: "placing the static instance inside the pool";
		
		freeBoxes.get( unusedBox.origin.length ).push( unusedBox );
		
	}
	

	/**
	 * It returns an usable box, reusing a box from the pool if possible.
	 * A DBox that is not used anymore should be put back into the pool using
	 * dispatchBox.
	 * 
	 * @param dimension it specifies number of dimensions of a requested box  
	 * @return It returns DBox with the specified dimension. Later on, when 
	 * box is no longer needed it should be dispatched back. 
	 */
	public static final DBox newBox(int dimension) {
		
		SimpleArrayList<DBox> boxes = freeBoxes.get(dimension);
		
		if( ! boxes.isEmpty() )
			return boxes.pop();
		else 
			return new DBox( new int[dimension], new int[dimension] );

	}
	
	/**
	 * It returns an instance of DBox of the corresponding dimension,
	 * using a previously allocated one if possible
	 * @param dimension
	 * 
	 * @return it returns a preallocated DBox of a given dimensions.
	 */
	public static final DBox getAllocatedInstance(int dimension) {
		return transientInstances.get(dimension);
	}
	
	/**
	 * It provides a string representation of the DBoxes which are present
	 * in the DBox pool.
	 * 
	 * @return string representation of the pool of DBoxes.
	 */
	public static String poolStatus() {
		
		StringBuilder builder = new StringBuilder();
		
		for(int i = 0; i < freeBoxes.size(); i++) 
			builder.append( freeBoxes.get(i) ).append( "\n" );
		
		return builder.toString();
	
	}

	/**
	 * 
	 * It checks if this DBox contains the point as specified by an array of coordinates. 
	 * @param pointCoordinates it specifies the point coordinates.
	 * 
	 * @return true if the point is inside DBox.
	 */
	public boolean containsPoint(int[] pointCoordinates) {
		
		assert (pointCoordinates.length <= origin.length) : "dimension mismatch";
		
		int pointDim = pointCoordinates.length;
		
		// unrolling for 2 dimensions
		if(pointDim == 2) {
			// TODO, BUG? describe why >= is used and not >, what are the assumptions?
			return !(pointCoordinates[0] < origin[0] || pointCoordinates[0] >= origin[0]+length[0] ||
					 pointCoordinates[1] < origin[1] || pointCoordinates[1] >= origin[1]+length[1] );
		} else {
			
			int limit = Math.min(origin.length, pointDim);
			
			for(int i = limit - 1; i >= 0; i--) 
				// looping backwards (comparison with 0 may be faster)
				if( pointCoordinates[i] < origin[i] 
				    || pointCoordinates[i] >= origin[i] + length[i] )
					return false;
			
			return true;
		}
		
	}
	
	/**
	 * It intersects this DBox with the given DBox. 
	 * 
	 * For efficiency reasons, the DBox returned is the static instance;
	 * if it needs to be stored, a copy has to be made using clone().
	 * 
	 * @param other the DBox to intersect this one with
	 * 
	 * @return null if the intersection is empty, or a reference to a static DBox corresponding 
	 * to the intersection. The result must be cloned if its scope is not local.
	 */
	public DBox intersectWith(DBox other){
		
		DBox intersection = DBox.getAllocatedInstance(origin.length);
		
		//the origin of the intersection
		int[] intersectionOrigin = intersection.origin;
		//the length of the intersection
		int[] intersectionLength = intersection.length;
		
		for(int i = origin.length - 1; i >= 0; i-- ) { //loop backwards
			intersectionOrigin[i] = Math.max(origin[i], other.origin[i]);
			intersectionLength[i] = Math.min( origin[i] + length[i], other.origin[i] + other.length[i] )
										- intersectionOrigin[i];
			// return empty intersection if the size is negative
			if( intersectionLength[i] <= 0 ) 
				return null;
		
		}
		
		return intersection;
	}
	
	

	/**
	 * It intersects this DBox with the given DBox, but the other DBox is
	 * shifted by the specified offset. 
	 * 
	 * For efficiency reasons, the DBox returned is the static instance;
	 * if it needs to be stored, a copy has to be made using clone().	 
	 * 
	 * @param other DBox with which the intersection is computed.
	 * @param otherOffset the offset 
	 * 
	 * @return null if the intersection is empty, or a reference to a static DBox corresponding 
	 * to the intersection. The result must be cloned if its scope is not local.
	 */
	public DBox intersectWith(DBox other, int[] otherOffset) {
		
		DBox intersection = DBox.getAllocatedInstance(origin.length);
		
		//the origin of the intersection
		int[] intersectionOrigin = intersection.origin;
		//the length of the intersection
		int[] intersectionLength = intersection.length;
		
		for(int i = origin.length - 1; i >= 0; i--) {
			
			intersectionOrigin[i] = Math.max( origin[i], other.origin[i] + otherOffset[i] );
			
			intersectionLength[i] = Math.min( origin[i] + length[i], other.origin[i] + other.length[i] + otherOffset[i] )
										- intersectionOrigin[i];
			
			//empty intersection if the size is negative
			if(intersectionLength[i] <= 0) return null;
			
		}
		
		return intersection;
	}
	
	/**
	 * It intersects this DBox with a view of the given DBox that was
	 * shifted according to the given offset. If the intersection is empty,
	 * returns null.
	 * 
	 * For efficiency reasons, the DBox returned is the static instance;
	 * if it needs to be stored, a copy has to be made using clone().
	 * @param offset the offset to apply to this box before intersecting
	 * @param other the DBox to intersect this one with
	 * @param otherOffset the offset to apply to the other DBox before intersecting
	 * @return null if the intersection is empty, or a reference to a static DBox corresponding 
	 * to the intersection. Clone if its scope is not local.
	 */
	public DBox intersectWith(int[] offset, 
							  DBox other, 
							  int[] otherOffset){
		
		DBox intersection = DBox.getAllocatedInstance(origin.length);
		
		//minimal value of the intersection
		int[] intersectionOrigin = intersection.origin;
		//maximal value of the intersection
		int[] intersectionLength = intersection.length;
		
		for(int i = origin.length - 1; i >= 0; i--){
			intersectionOrigin[i] = Math.max(origin[i] + offset[i], other.origin[i] + otherOffset[i]);
			intersectionLength[i] = Math.min(origin[i] + length[i] + offset[i], other.origin[i] + other.length[i] + otherOffset[i])
										- intersectionOrigin[i];
			//empty intersection if the size is negative
			if(intersectionLength[i]<= 0) return null;
			
		}
		
		return intersection;
	}
	
	/**
	 * computes the difference between this box and the given box. The difference
	 * is returned under the form of a collection of boxes.
	 * 
	 * NOTE: the collection of DBoxes returned is not minimal (in some cases,
	 * some boxes can be merged)
	 * 
	 * if needed, implement a version that can take a lexical order as argument,
	 * to allow brute force search or learning of the best decomposition
	 * 
	 * @param hole the box to subtract this box with
	 * @param difference the collection of boxes corresponding to the remaining area
	 * @return the computed difference, which is the difference paramter after the call
	 *         (this is for ease of use only)
	 */
	public Collection<DBox> subtract(DBox hole, Collection<DBox> difference){
		/*
		 * the cutting algorithm works in the following way:
		 * for each dimension, it maintains an upper and lower bound,
		 * which are the bounds of the remaining area to cut. Initially,
		 * they are the bounds of this box.
		 * Then it considers each dimension one after the other,
		 * and if the hole is between the bounds wrt the current dimension,
		 * it creates (at most) 2 boxes, one on each side of the hole, and
		 * updates the bounds in the current dimension to be the bounds of the hole.
		 * 
		 * This way, at most 2*dimension boxes will be created, and they will not
		 * overlap.
		 */

		assert difference != null : "accumulator must be initialized";

		final int dimension = origin.length;
		
		//first, make sure that the intersection is not empty (else the difference is this box)
		if(this.intersectWith(hole) == null){
			DBox diff = newBox(dimension);
			this.copyInto(diff);
			difference.add(diff);
		} else {

			//if there is an intersection, we need to subtract the space

			//initialize bounds
			DBox dummyBox = newBox(dimension);
			int[] lowerbound = dummyBox.length;
			int[] upperbound = dummyBox.origin;

			System.arraycopy(origin, 0, lowerbound, 0, dimension);
			
			for(int i = dimension - 1; i >= 0; i--)
				upperbound[i] = origin[i] + length[i];

			/*
			 * for each dimension, create at most 2 outboxes,
			 * one on each side, and update the bounds
			 * 
			 * Remark: we already know that the intersection is not empty,
			 * so we do not consider the cases where the hole origin is after the box end,
			 * or where the hole end is before the origin
			 */
			for(int i = dimension - 1; i >= 0; i--){

				//slice before hole
				if(hole.origin[i] > lowerbound[i]){
					//else, we need to add the slice before, and update the lower bound
					DBox newBox = newBox(dimension);
					int[] sliceOrigin = newBox.origin;
					int[] sliceLength = newBox.length;
					//origin is same as lower bound 
					System.arraycopy(lowerbound, 0, sliceOrigin, 0, dimension);
					//slice upper bound is same as upper bound, except in the current dimension
					for(int j = dimension-1; j >= 0; j--) //reverse loop
						sliceLength[j] = upperbound[j]-lowerbound[j];
					
					sliceLength[i] = hole.origin[i] - lowerbound[i];

					assert(newBox.checkInvariants() == null) : newBox.checkInvariants();
					
					//the box is defined, we can add it
					difference.add(newBox);

					//we can now update the bound
					lowerbound[i] = hole.origin[i];
				}

				//slice after hole
				if(hole.origin[i] + hole.length[i] < upperbound[i]){
					//else, we need to add the slice after, and update the upper bound
					DBox newBox = newBox(dimension);
					int[] sliceOrigin = newBox.origin;
					int[] sliceLength = newBox.length;
					//origin is same as lower bound, except in the current dimension
					System.arraycopy(lowerbound, 0, sliceOrigin, 0, dimension);
					sliceOrigin[i] = hole.origin[i] + hole.length[i];
					//slice upper bound is same as upper bound
					for(int j = dimension - 1; j >= 0; j--)//reverse loop
						sliceLength[j] = upperbound[j] - sliceOrigin[j];
					

					assert(newBox.checkInvariants() == null) : newBox.checkInvariants();
					
					//the box is defined, we can add it
					difference.add(newBox);

					//we can now update the upper bound
					upperbound[i] = hole.origin[i] + hole.length[i];
				}


			}
			
			DBox.dispatchBox(dummyBox);
		}
		
		return difference;
	}
	
	/**
	 * computes the bounding box of the given collection of boxes
	 * @param boxes
	 * @return a temporary DBox that represents the bounding box of the given boxes.
	 * 	       clone it if you need to reuse it.
	 */
	public static DBox boundingBox(Collection<DBox> boxes) {
		
		assert !boxes.isEmpty();
		
		DBox boundingBox = null;
		int[] mins = null;
		int[] maxes = null;
		int dim = 0;
		
		for(DBox b : boxes)
			if(mins == null) {
				//initialization of the values
				dim = b.origin.length;
				boundingBox = getAllocatedInstance(dim);
				b.copyInto(boundingBox);
				
				mins = boundingBox.origin;
				maxes = boundingBox.length;
				
				for(int i = dim - 1; i >= 0; i--)
					maxes[i] += mins[i];
				
			} else {
				for(int i = dim - 1; i >= 0; i--) {
					mins[i] = Math.min(mins[i], b.origin[i]);
					maxes[i] = Math.max(maxes[i], b.origin[i] + b.length[i]);
				}
			}
		
		//replace the maxes by the actual sizes
		for(int i = dim - 1; i >= 0; i--)
			maxes[i] = maxes[i] - mins[i];
		
		return boundingBox;
	}
	
	/**
	 * It computes the result of a subtraction from the given collection of boxes of all the boxes given
	 * in the subtracting collection. The collection used to store the result is given to avoid allocating 
	 * a new set of boxes each time the function is called. However, for ease of use, it is also returned 
	 * (after the call, the result argument is equal to the returned value).
	 * 
	 * @param source the collection of boxes to subtract from
	 * @param holes the boxes to subtract from the source boxes
	 * @param result the collection to store the resulting boxes into
	 * @return the result argument, for ease of use
	 */
	public static Collection<DBox> subtractAll(Collection<DBox> source,
											   Collection<DBox> holes,
											   Collection<DBox> result){
		
		
		if(result != source){
			assert result.isEmpty() :  "the collection must be emptied before the call";

			result.addAll(source);
		}
		Collection<DBox> resultWork = result;


		assert workingList.isEmpty() : "working list must be empty";
		
		Collection<DBox> resultStep = workingList;
		
		/*
		 * proceed hole by hole: for each hole, subtract it to each remaining piece.
		 * 
		 * We need two lists, one to store the current pieces not yet subtracted with the 
		 * current hole, and one to store the ones that were subtracted already.
		 */
	
		for(DBox hole : holes){
			
			for(DBox piece : resultWork){
				piece.subtract(hole, resultStep);
			}
			//the DBoxes contained in result can be reused
			for(DBox piece: resultWork){
				dispatchBox(piece);
			}
			if(resultWork == workingList){
				workingList.clearNoGC(); //garbage collection is not done on DBoxes anyway
			} else {
				resultWork.clear();
			}
			//switch lists
			Collection<DBox> resTmp = resultWork;
			resultWork = resultStep;
			resultStep = resTmp;
			
			//if there is nothing left, no need to continue
			if(resultWork.isEmpty()){
				break;
			}
		}

		//now we need to make sure that the correct list contains the boxes
		assert (resultStep.isEmpty() && !resultWork.isEmpty()) || 
			resultStep.isEmpty() && resultWork.isEmpty() : //without this the assertion would fail when subtracting leaves nothing
				"bad cleaning of the lists";
		
		if(result == resultStep){
			// in that case we need to transfer the elements to the right list
			result.addAll(resultWork);
			//and clear the ones in the working list
			resultWork.clear();
		}
		
		assert workingList.isEmpty() : "working list must be empty";
		
		
			
		return result;
	}
	
	/**
	 * It computes the result of a subtraction from this box of all the boxes given. The collection
	 * used to store the result is given to avoid allocating a new set of boxes each time the function is called.
	 * However, for ease of use, it is also returned (after the call, the result argument is equal to the returned value)
	 * 
	 * @param others the boxes to subtract from this box
	 * @param result the collection to store the resulting boxes into
	 * @return the result argument, for ease of use
	 */
	public Collection<DBox> subtractAll(Collection<DBox> others, Collection<DBox> result){
		
		/*
		 * begin with this as temporary result, then subtract each box
		 * to the temporary result.
		 */	

		assert result.isEmpty() :  "collection must be emptied before call";

		Collection<DBox> resultWork = result;
		resultWork.add( this.copyInto(newBox(origin.length)) );


		assert workingList.isEmpty() : "working list must be empty";
		
		Collection<DBox> resultStep = workingList;
		
		/*
		 * proceed hole by hole: for each hole, subtract it to each remaining piece.
		 * 
		 * We need two lists, one to store the current pieces not yet subtracted with the 
		 * current hole, and one to store the ones that were subtracted already.
		 */
	
		for(DBox hole : others) {
			
			for(DBox piece : resultWork)
				piece.subtract(hole, resultStep);
			
			//the DBoxes contained in result can be reused
			for(DBox piece: resultWork) {
				assert piece != this : "dispatching this";
				dispatchBox(piece);
			}
			
			if(resultWork == workingList)
				workingList.clearNoGC();
			 else 
				resultWork.clear();
			
			//switch lists
			Collection<DBox> forExchange = resultWork;
			resultWork = resultStep;
			resultStep = forExchange;
			
			//if there is nothing left, no need to continue
			if(resultWork.isEmpty())
				break;
			
		}

		//now we need to make sure that the correct list contains the boxes
		assert (resultStep.isEmpty() && !resultWork.isEmpty()) || 
			resultStep.isEmpty() && resultWork.isEmpty() : //without this the assertion would fail when subtracting leaves nothing
				"bad cleaning of the lists";
		
		if(result == resultStep){
			// in that case we need to transfer the elements to the right list
			result.addAll(resultWork);
			//and clear the ones in the working list
			resultWork.clear();
		}
		
		assert workingList.isEmpty() : "working list must be empty";
			
		return result;
		 
	}
	
	/**
	 * It computes the area in 2D case or volume in 3D case. 
	 * 
	 * @return the area/volume of the DBox.
	 * 
	 */
	public int area(){
		
		int area = length[0];
		
		// i is not >= 0 since area initial value is length[0]
		for(int i = origin.length - 1; i > 0 ; i--)
			area *= length[i];
		
		return area;
	}
	
	/**
	 * It copies this DBox into given DBox.
	 * 
	 * @param box the DBox to copy this DBox into
	 * @return for convenience reasons, returns the copied DBox (same as the argument)
	 */
	public final DBox copyInto(DBox box) {
		
		assert box != null : "It is not possible to copy into null box";
		
		final int dimension = origin.length;
		
		System.arraycopy(origin, 0, box.origin, 0, dimension);
		System.arraycopy(length, 0, box.length, 0, dimension);
		
		return box;
		
	}
	
	public String toString(){
		
		StringBuilder result = new StringBuilder();
		result.append("DBox(").append(Arrays.toString(origin)).append(" ; ");
		result.append(Arrays.toString(length)).append(")");
		
		return  result.toString();
		
	}

	@Override
	public int hashCode() {
		//TODO profile and make sure this does not kill efficiency
		final int prime = 31;
		int result = 1;
		result = prime * result + Arrays.hashCode(length);
		result = prime * result + Arrays.hashCode(origin);
		return result;
	}


	public boolean equals(Object obj) {
		
		if (this == obj)
			return true;
		
		if (obj == null)
			return false;
		
		if (getClass() != obj.getClass())
			return false;
		
		DBox other = (DBox) obj;
		
		if (!Arrays.equals(length, other.length))
			return false;
		
		if (!Arrays.equals(origin, other.origin))
			return false;
		
		return true;
	}
	
	
}
