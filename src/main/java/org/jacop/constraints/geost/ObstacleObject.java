/**
 *  ObstacleObject.java 
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

import org.jacop.core.IntDomain;
import org.jacop.util.SimpleArrayList;

/**
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 *
 * This version of the ObstacleObject internal constraint allows the use
 * of multiple d-boxes per shape.
 * 
 * TODO, describe how it works and what is the idea behind this implementation?
 * 
 */

public class ObstacleObject extends ObstacleObjectFrame {

	/**
	 * It shifts boxes of the given shape as required by the frame. It recomputed 
	 * always when frame is updated. It allows for faster execution in between frame updates.
	 */
	final SimpleArrayList<DBox> preshiftedElems;

	final int[] lowerAbsInsfeasible;
	final int[] upperAbsInsfeasible;

	/**
	 * It is a boolean switch which steers this constraint behavior. 
	 * It is set to true as soon as frame is not empty. 
	 */
	boolean frameExists;

	/**
	 * It stores the information about the shape, so it does not always have to look for its value inside 
	 * the domain of shape variable.
	 */
	int shapeId;

	/**
	 * It constructs an internal constraint to constraint the objects not to overlap with this 
	 * obstacle object. 
	 * 
	 * @param geost the constraint for which this internal constraint has been created. 
	 * @param obstacle the obstacle object which is responsible for this constraint.
	 * @param selectedDimensions the dimensions on which the constraint is applicable.
	 */
	public ObstacleObject(Geost geost, GeostObject obstacle, int[] selectedDimensions) {

		super(geost, obstacle, selectedDimensions);

		preshiftedElems = new SimpleArrayList<DBox>();

		assert obstacle.shapeID.singleton() : "Polymorphism not supperted by this simple internal constraint. Use ObstacleObjectFrame instead.";

		shapeId = obstacle.shapeID.value();

		for(DBox elem : geost.getShape(shapeId).boxes)
			preshiftedElems.add(elem.copyInto(DBox.newBox(obstacle.dimension)));

		upperAbsInsfeasible = new int[obstacle.dimension+1];
		lowerAbsInsfeasible = new int[obstacle.dimension+1];

	}

	@Override
	public String checkInvariants() {

		if(super.checkInvariants() != null) return super.checkInvariants();

		if(obstacle == null) return "obstacle field is null";

		//make sure the selected dimensions are sorted and have correct values
		int previous = 0;
		for(int i = 0; i < selectedDimensions.length; i++) {
			if(i != 0)
				if(selectedDimensions[i] <= previous) 
					return "selected dimensions " + Arrays.toString(selectedDimensions) + " are not sorted or not unique";

			previous = selectedDimensions[i];

			if(!( selectedDimensions[i] >= 0 && selectedDimensions[i] <= obstacle.dimension) ) 
				return "incorrect dimension: " + selectedDimensions[i];
		}

		return null;
	}

	@Override
	public int[] AbsInfeasible(Geost.SweepDirection minlex) {

		//TODO implement, 

		if(frameExists)
			return super.AbsInfeasible(minlex);
		else {

			if(minlex == Geost.SweepDirection.PRUNEMAX)
				return upperAbsInsfeasible;
			else 
				return lowerAbsInsfeasible;

		}

	}


	@Override
	public int cardInfeasible() {

		if(frameExists){
			return super.cardInfeasible();
		} else {
			//rough approximation, but consistent among ObstacleObject constraint
			return 1; //TODO correct
		}
	}


	@Override
	public DBox isFeasible(Geost.SweepDirection min, 
						   LexicographicalOrder order,
						   GeostObject o, 
						   int currentShape, 
						   int[] c) {


		// TODO, Does it make sense from efficiency point of view to work on polymorphism?
		assert obstacle.shapeID.singleton() : "no support for polymorphism. Use ObstacleObjectFrame instead.";

		if(frameExists)
			return super.isFeasible(min, order, o, currentShape, c);

		//an object can overlap with itself
		if(o == obstacle) return null;

		if(!timeOnlyCheck(min, order, o, currentShape, c)) 
			return null;

		//intermediate check: use bounding boxes to skip test quickly
		DBox obstacleBB = geost.getShape(shapeId).boundingBox;
		DBox otherBB = geost.getShape(currentShape).boundingBox;
		int outDimOrigin = 0;
		int outDimLength = 0;
		int selectedDimIndex = 0;
		for(int i = 0;  i < obstacle.dimension; i++) {
			if(selectedDimIndex < selectedDimensions.length && selectedDimensions[selectedDimIndex] == i) {

				//the dimension is relevant
				selectedDimIndex++;

				//shift origin
				outDimOrigin = obstacleBB.origin[i] + obstacle.coords[i].max() - otherBB.origin[i] - otherBB.length[i] + 1;

				final int max = obstacleBB.origin[i] + obstacleBB.length[i] 
				                + obstacle.coords[i].min() - otherBB.origin[i];

				outDimLength = max - outDimOrigin;

				if(outDimLength <=0 )
					return null;

			} else {
				//the dimension is not relevant, outbox covers the whole space
				outDimOrigin = IntDomain.MinInt;
				outDimLength = IntDomain.MaxInt-IntDomain.MinInt;
			}
			
			if(c[i] < outDimOrigin || c[i] >= outDimOrigin+outDimLength)
				return null;
			
		}


		/*
		 * for now, simply check against each component of the frame one after the other
		 * TODO improve this: get the actual maximal forbidden domain (hard), or sort the frame boxes
		 */

		//avoid allocating new object if possible
		DBox outBox = DBox.getAllocatedInstance(obstacle.dimension+1);
		int[] outOrigin = outBox.origin;
		int[] outLength = outBox.length;

		//we already know the size in the time dimension
		outOrigin[obstacle.dimension] = timeSizeOrigin;
		outLength[obstacle.dimension] = timeSizeMax - timeSizeOrigin;

		for(DBox constrainedPiece : geost.getShape(currentShape).boxes)
			for(DBox preshift : preshiftedElems) {

				boolean useless = false;

				selectedDimIndex = 0;

				//TODO precompute elem.origin[i] + obstacle.coords[i].max() and elem.origin[i] + elem.length[i] + obstacle.coords[i].min()
				//and update whenever the object gets updated

				for(int i = 0;  i< obstacle.dimension; i++)
					if(selectedDimIndex < selectedDimensions.length 
					   && selectedDimensions[selectedDimIndex] == i) {

						//the dimension is relevant
						selectedDimIndex++;
						outOrigin[i] = preshift.origin[i] - constrainedPiece.origin[i] - constrainedPiece.length[i] + 1;

						final int max = preshift.length[i] - constrainedPiece.origin[i];
						outLength[i] = max - outOrigin[i];

						if(outLength[i] <= 0 )
							useless = true;

					} else {
						//the dimension is not relevant, outbox covers the whole space
						outOrigin[i] = IntDomain.MinInt;
						outLength[i] = IntDomain.MaxInt - IntDomain.MinInt;
					}

				assert(useless || outBox.checkInvariants() == null) : outBox.checkInvariants();

				if(!useless && outBox.containsPoint(c))
					return outBox;

			}

		return null;
	}


	@Override
	public String toString() {

		StringBuilder result = new StringBuilder();

		result.append("ObstacleObject(o").append(obstacle.no).append(", ");
		result.append(Arrays.toString(selectedDimensions)).append(")");

		return result.toString();

	}

	@Override
	public boolean isStatic() {
		//if obstacle object is grounded, frame will not change anymore
		return obstacle.isGrounded();
	}

	@Override
	public boolean isSingleUse() {
		return false;
	}

	@Override
	public void updateFrame(){

		//note: frameIsUsed is undefined until the first call to this function (done at initialization)

		super.updateFrame();

		if(frame.isEmpty()){

			frameExists = false;
			int currentIndex = 0;

			for(DBox elem : geost.getShape(shapeId).boxes) {

				DBox preshift = preshiftedElems.get(currentIndex);

				for(int i = 0; i < obstacle.dimension; i++) {
					preshift.origin[i] = elem.origin[i] + obstacle.coords[i].max();
					preshift.length[i] = elem.origin[i] + elem.length[i] + obstacle.coords[i].min();
				}

				currentIndex++;
			}

			//update absolute infeasible points
			DBox bb = geost.getShape(shapeId).boundingBox;

			for(int i = 0; i < obstacle.dimension;i++) {
				// TODO, Are the max and min functions here, put correctly?
				upperAbsInsfeasible[i] = obstacle.coords[i].min() + bb.origin[i] + bb.length[i];
				lowerAbsInsfeasible[i] = obstacle.coords[i].max() + bb.origin[i];
			}

			upperAbsInsfeasible[obstacle.dimension]= IntDomain.MaxInt;
			lowerAbsInsfeasible[obstacle.dimension] = IntDomain.MinInt;

		} else
			frameExists = true;

		assert checkInvariants() == null : checkInvariants();
	}

}
