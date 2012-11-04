/**
 *  ObstacleObjectFrame.java 
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

import java.awt.Color;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.LinkedList;
import java.util.ListIterator;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;
import org.jacop.util.SimpleArrayList;

/**
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 *
 * This version of the ObstacleObject internal constraint allows the use
 * of multiple d-boxes per shape.
 * 
 * TODO, description explaining how it works, what is it good for, etc...
 * 
 */

public class ObstacleObjectFrame extends InternalConstraint {

	//TODO, introduce boolean switch computeArea(Precisely) which if is set to false will not compute the area at all or precisely.
	// Possibly, useful to set to 1 if greater than 1 and to 0 if empty.
	
	//TODO, use << 2, instead of *4. Explain precisely why this scalling was needed in the first place.
	
	final static boolean DISPLAY_FRAME = false;
	
	static BoxDisplay display = null; //TODO remove if not needed anymore, or better separate from other code by putting it inside functions.

	/**
	 * It specifies the geost constraint to which this internal constraint belongs to.
	 */
	final Geost geost;

	/**
	 * It specifies the geost objection which is the foundation of this obstacle constraint.
	 */
	final GeostObject obstacle;
	
	/**
	 * the frame is the area that is ensured to be covered by the obstacle,
	 * given the domain of its origin variables
	 */
	public LinkedList<DBox> frame;
	
	/**
	 * It specifies the bounding box of the frame.
	 */
	private DBox frameBoundingBox;

	/**
	 * it computes the area/volume of the frame.
	 */
	private int frameArea;
	

	/**
	 * the collection of holes that are included in all possible shapes, 
	 * enlarged to include the whole domain that can be covered for any
	 * feasible choice of the origin
	 */
	private SimpleArrayList<DBox> extendedHoles;
	
	
	/**
	 * The selected dimensions are sorted, they were sorted by NonOverlapping external constraint.
	 */
	final int[] selectedDimensions;
	
	/** 
	 * It specifies if the time dimension is used within computation. 
	 */
	final boolean useTime;
	
	int timeSizeOrigin = 0;
	int timeSizeMax = 0;
	
	
	/**
	 * It creates an internal constraint to enforce non-overlapping relation with this
	 * obstacle object. 
	 * 
	 * @param geost the geost constraint which this constraint is part of.
	 * @param obstacle the obstacle object responsible for this internal constraint. 
	 * 
	 * @param selectedDimensions the dimensions on which the constraint is applied
	 */
	public ObstacleObjectFrame(Geost geost, GeostObject obstacle, int[] selectedDimensions) {
	
		this.obstacle = obstacle;

		this.geost = geost;
		
		this.selectedDimensions = selectedDimensions;
		
		//check whether time should be used or not
		useTime = selectedDimensions[selectedDimensions.length-1] == obstacle.dimension;
		
		extendedHoles = new SimpleArrayList<DBox>();
		
	}
	
	
	/**
	 * It checks that this constraint has consistent data structures.
	 * 
	 * @return a string describing the consistency problem with data structures, null if no problem encountered.
	 */
	public String checkInvariants(){
		
		if(obstacle == null)
			return "obstacle field is null";
		
		if(frame == null)
			return "frame is null";

		if(extendedHoles == null)
			return "frame is null";
		
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
	
	/**
	 * It creates the frame if it does not exist, and clears it if it does.
	 */
	private void clearFrame() {
		
		if(frame != null) {
			
			for(DBox b : frame)
				DBox.dispatchBox(b);
			frame.clear();
			
		} else {
			frame = new LinkedList<DBox>();
			frameBoundingBox = DBox.newBox(obstacle.dimension);
		}

		frameArea = 0;
	}
	
	/**
	 * updates the frame given the current values of the object coordinate variables. This method
	 * should be called whenever some of the coordinate variables of the associated object change.
	 */
	public void updateFrame(){
		
		//TODO optimize the frame computation given the set of dimensions used
		
		if(geost.backtracking && obstacle.isGrounded()) {	
			return;
		}
		
		/*
		 * to find the frame, we subtract from the domain always covered by the bounding box the area that can be
		 * covered by some hole
		 */
		if(DISPLAY_FRAME) {
			if(display == null)
				display = new BoxDisplay(5, obstacle.toString());
			else {
				display.eraseAll();
				display.setTitle(obstacle.toString());
				display.drawGrid(Color.lightGray);
			}
		}
		
		//remember whether one of the shapes has holes
		boolean holesExist = false;
		
		//define coverable domain
		DBox domain = DBox.newBox(obstacle.dimension);
		int[] domOrigin = domain.origin;
		int[] domSize = domain.length;
		/*
		 * in the polymorphic case, the domain that is covered in any case is the intersection
		 * of the bounding boxes of each shape
		 */
		DBox boundingBox = null;
		ValueEnumeration vals = obstacle.shapeID.domain.valueEnumeration();
		boolean firstIter = true;
		while (vals.hasMoreElements()){
			int sid = vals.nextElement();
			
			Shape shape = geost.getShape(sid);
			//if we don't know that there are holes yet, check
			if(!holesExist && !shape.holes().isEmpty())
				holesExist = true;
			
			DBox shapeBoundingBox = shape.boundingBox();
			if(firstIter) {
				boundingBox = shapeBoundingBox.copyInto(DBox.newBox(obstacle.dimension));
				firstIter = false;
			} else {
				DBox inter = boundingBox.intersectWith(shapeBoundingBox);
				if(inter != null)
					inter.copyInto(boundingBox);
				else {
					//there is no box common to all bounding boxes, the frame is empty
					clearFrame();
					//release unused boxes
					DBox.dispatchBox(domain);
					DBox.dispatchBox(boundingBox);	
					return;
				}
			}
			
		}
		
		assert boundingBox != null;
		
		for(int i = 0; i < obstacle.dimension; i++) {
			
			IntVar coordVar = obstacle.coords[i];
			domOrigin[i] = coordVar.max() + boundingBox.origin[i];
			domSize[i] = coordVar.min() + boundingBox.length[i] - coordVar.max();
			
			if(domSize[i] < 0) {
				//means that the bounding box itself does not have any space always covered
				clearFrame();
				//release the domain box
				DBox.dispatchBox(domain);
				DBox.dispatchBox(boundingBox);
				return;
			}
		}
		
		//we will not need this one anymore
		DBox.dispatchBox(boundingBox);
		
		//if there are no holes, the frame is simply the domain that can be covered by the bounding box
		if(!holesExist) {
			
			clearFrame();		
			frame.add(domain);
			frameArea = domain.area();
			
		} else {
		
			clearFrame();
			updateExtendedHoles();
			
			//scale the domain by a factor 4, so that it has the same scale as the holes
			for(int i = 0; i < obstacle.dimension; i++){
				//add extra quarter unit so that a flat frame piece right next to the border is detected
				domain.origin[i] = domain.origin[i]*4 - 1;
				domain.length[i] = domain.length[i]*4 + 2;
			}
			
			if(DISPLAY_FRAME) {

				ValueEnumeration vals2 = obstacle.shapeID.domain.valueEnumeration();
				while (vals2.hasMoreElements()){
					int sid = vals.nextElement();

					Shape shape = geost.getShape(sid);

					for(DBox sp : shape.holes()){
						display.display2DBox(sp, Color.orange);
					}
					for(DBox b : shape.boxes){
						display.display2DBox(b, Color.black);
					}
					Collection<DBox> rescaledBoxes = new ArrayList<DBox>(shape.boxes.size());

					for(DBox b : shape.boxes){
						int dim = b.origin.length;
						DBox scaled = DBox.newBox(dim);
						for(int i = 0; i < dim; i++) {
							scaled.origin[i] = b.origin[i]*4;
							scaled.length[i] = b.length[i]*4;
						}
						rescaledBoxes.add(scaled);
					}

					for(DBox sb : rescaledBoxes){
						display.display2DBox(sb, Color.magenta);
					}
					
				}
				
				for(DBox sp : extendedHoles){
					display.display2DBox(sp, Color.blue);
				}
				display.display2DBox(domain, Color.green);

			}
				
			domain.subtractAll(extendedHoles, frame);
				
			ListIterator<DBox> iterator = frame.listIterator();
		
			/* now sweep through the obtained frame, and rescale the pieces. 
			 * A piece that has length 1 in some dimension must be discarded, because it was obtained
			 * using an artificial hole boundary and a shape hole boundary
			 * A piece that has length 2 must be kept, it results of a limit case: the two holes
			 * that created it are on the sides of some shape component.
			 */
			int dim = obstacle.dimension;
			while (iterator.hasNext()){
				DBox piece = iterator.next();
				if(DISPLAY_FRAME){
					display.display2DBox(piece, Color.gray);
				}
				boolean valid = true;
				for(int i = 0; valid && i < dim; i++){
					if(piece.length[i] == 1){
						//ignore this piece, and remove it from the frame
						valid = false; 
						DBox.dispatchBox(piece);
						iterator.remove();
					} else {
						//we need to retrieve the correct boundaries, given that the holes have one missing quarter unit
						int originMod = piece.origin[i]%4;
						int end = piece.origin[i] + piece.length[i];
						int endMod = end%4;

						if(originMod >= 3){
							piece.origin[i] = (int) Math.ceil(piece.origin[i]/4.0);
						} else {
							piece.origin[i] = (int) Math.floor(piece.origin[i]/4.0);	
						}
						
						if(endMod <= 1){
							//shift boundary to the left
							end = (int) Math.floor(end/4.0);
						} else {
							//shift boundary to the right
							end = (int) Math.ceil(end/4.0);
						}
						piece.length[i] = end - piece.origin[i];
						
					}
				}
			}
			
			
		
			//no need of the extended holes anymore, we can reuse the boxes
			for(DBox b : extendedHoles){
				DBox.dispatchBox(b);
			}
			
			//release the domain box
			DBox.dispatchBox(domain);

			
		}
		

		if(DISPLAY_FRAME){

			for(DBox framePiece : frame){
				display.display2DBox(framePiece, Color.red);
			}
		}

		//update frame bounding box
		if(!frame.isEmpty())
			DBox.boundingBox(frame).copyInto(frameBoundingBox);
		
		//update the frame area
		frameArea = 0;
		for(DBox frameComponent : frame)
			frameArea += frameComponent.area();
		
		
		if(!frame.isEmpty()){
			frameArea++; //just to make sure that area made of thin parts are not discarded
		}
		
		assert checkInvariants() == null : checkInvariants();
	}
	
	private void updateExtendedHoles(){
		
		/*
		 * This can be further improved by updating the extended the holes in the only
		 * dimension that changed.
		 */
		extendedHoles.clearNoGC(); //DBoxes are not collected anyway

		final ValueEnumeration vals = obstacle.shapeID.domain.valueEnumeration();
		while(vals.hasMoreElements()){
			int sid = vals.nextElement();

			Shape shape = geost.getShape(sid);

			for(DBox hole : shape.holes()){
				//define coverable domain
				DBox extendedHole = DBox.newBox(obstacle.dimension);
				int[] holeDomOrigin = extendedHole.origin;
				int[] holeDomSize = extendedHole.length;

				//preserve scaling by 4
				for(int i = 0; i<obstacle.dimension; i++){
					IntVar coordVar = obstacle.coords[i];
					holeDomOrigin[i] = 4*coordVar.min() + hole.origin[i];
					holeDomSize[i] = 4*coordVar.max() + hole.length[i] - 4*coordVar.min();
				}

				extendedHoles.add(extendedHole);
			}
		}
	}


	@Override
	public int[] AbsInfeasible(Geost.SweepDirection minlex) {
		//reuse previously allocated array
		int[] outPoint = DBox.getAllocatedInstance(obstacle.dimension+1).origin;
	
		final boolean consider_all = false;
		if(consider_all){
			switch (minlex) {
			case PRUNEMAX:
				Arrays.fill(outPoint, Integer.MAX_VALUE);
				break;
			case PRUNEMIN:
				Arrays.fill(outPoint, Integer.MIN_VALUE);
				break;
			default:
				assert false : "unhandled case";

			}
			return outPoint;
		}

		if(frame.isEmpty())
			return null;
		else {
			//look for the upper or lower bound of the frame
				
			switch (minlex) {
			case PRUNEMAX:
				Arrays.fill(outPoint, Integer.MIN_VALUE);
				break;
			case PRUNEMIN:
				Arrays.fill(outPoint, Integer.MAX_VALUE);
				break;
			default:
				assert false : "unhandled case";
			}

			int selectedDimIndex = 0;
			
			for(int i = 0;  i< obstacle.dimension; i++){
				
				if(selectedDimIndex < selectedDimensions.length && selectedDimensions[selectedDimIndex] == i){
					//the dimension is relevant
					selectedDimIndex++;

					switch (minlex) {
					
					case PRUNEMAX:
						outPoint[i] = frameBoundingBox.origin[i] + frameBoundingBox.length[i];
						break;
						
					case PRUNEMIN:
						outPoint[i] = frameBoundingBox.origin[i];
						break;
						
					default:
						assert false : "unhandled case";

					}


				} else { //cover the whole space
	
					if(minlex == Geost.SweepDirection.PRUNEMAX)
						outPoint[i] = Integer.MAX_VALUE;
					else
						outPoint[i] = Integer.MIN_VALUE;
					
				}
			}
			
			
			if(useTime) {
				/**
				 * for the time dimension, we need the bounds of the frame in the time 
				 * dimension, which are the extrema of the area in time that is for certain
				 * used by this object
				 */
				int up = obstacle.end.max();
				int low = obstacle.start.min();
				if(up - low < 0)
					outPoint[obstacle.dimension] = 0;
				else {
					
					if(minlex == Geost.SweepDirection.PRUNEMAX && up==low)
						//same case as above, we need to include the constraint in the series
						up = low + 1;

					outPoint[obstacle.dimension] = minlex == Geost.SweepDirection.PRUNEMIN ? low : up;
				}
			} else {
				
				if(minlex == Geost.SweepDirection.PRUNEMAX)
					outPoint[obstacle.dimension] = Integer.MAX_VALUE;
				else
					outPoint[obstacle.dimension] = Integer.MIN_VALUE;
				
			}

			return outPoint;
		}

	}


	@Override
	public int cardInfeasible() {
		return frameArea;
	}

	@Override
	public Collection<Var> definingVariables() {
		
		Collection<Var> variables = new ArrayList<Var>(obstacle.dimension);
		
		for(int i = 0; i<obstacle.dimension; i++)
			variables.add(obstacle.coords[i]);
		
		variables.add(obstacle.shapeID);
		variables.add(obstacle.start);
		variables.add(obstacle.duration);
		variables.add(obstacle.end);
		
		return variables;
	}

	
	protected boolean timeOnlyCheck(Geost.SweepDirection min, 
									LexicographicalOrder order,
									GeostObject o, 
									int currentShape, 
									int[] c){
		
		if(useTime){
			//if there is no overlap in time, no need to continue
			if(min == Geost.SweepDirection.PRUNEMIN) {
				//largest possible origin when objects begin to overlap (infeasible)
				timeSizeOrigin =  obstacle.start.max() - o.duration.min() + 1;
				//smallest possible end is when placed after the obstacle (feasible)
				assert obstacle.start.min() + obstacle.duration.min() <= obstacle.end.min() : "time constraint not valid: " + obstacle.start+" + " +obstacle.duration + " <= " + obstacle.end;
				timeSizeMax = obstacle.end.min(); 
			} else {
				//PRUNEMAX: the outbox has to mark the upper limit of the possible domain (end variable)

				/* in the usual case (not time), we can simply prune the upper bound of the origin domain.
				 * However, in this case, since the "length" changes, we really have to consider the maximal
				 * ending time.
				 */

				timeSizeOrigin =  obstacle.start.max() + 1;
				assert obstacle.start.min()+obstacle.duration.min() <= obstacle.end.min();
				timeSizeMax = obstacle.end.min() + o.duration.min(); 
			}
			
			if(timeSizeMax - timeSizeOrigin <= 0) 
				return false;

			//check if point is between bounds, if not return null
			if(c[obstacle.dimension] < timeSizeOrigin || c[obstacle.dimension] > timeSizeMax)
				//point cannot be contained in outbox, no need to continue
				return false;
			else
				return true;
			
		} else {
			//time is not included in the dimensions, thus the outbox covers the whole space 
			timeSizeOrigin = IntDomain.MinInt;
			timeSizeMax = IntDomain.MaxInt;
			return true;
		}
	}
	
	@Override
	public DBox isFeasible(Geost.SweepDirection min, 
						   LexicographicalOrder order,
						   GeostObject o, 
						   int currentShape, 
						   int[] c) {
		
		
		//an object can overlap with itself
		if(o == obstacle) 
			return null;
		
		//if the frame is empty, then any point is feasible
		if(frame.isEmpty()) 
			return null;
		
		if(!timeOnlyCheck(min, order, o, currentShape, c)) 
			return null;
		

		//intermediate check: use bounding boxes to skip test quickly
		DBox otherBB = geost.getShape(currentShape).boundingBox;
		
		int outDimOrigin = 0;
		int outDimLength = 0;
		int selectedDimIndex = 0;
		
		for(int i = 0;  i < obstacle.dimension; i++) {
			
			if(selectedDimIndex < selectedDimensions.length && selectedDimensions[selectedDimIndex] == i) {
				//the dimension is relevant
				selectedDimIndex++;
				//shift origin
				outDimLength = frameBoundingBox.length[i] + otherBB.length[i]-1;
				//adjust size
				outDimOrigin = frameBoundingBox.origin[i]-(otherBB.length[i]-1) - otherBB.origin[i];
			} else {
				//the dimension is not relevant, outbox covers the whole space
				outDimOrigin = IntDomain.MinInt;
				outDimLength = IntDomain.MaxInt-IntDomain.MinInt;
			}
			
			if(c[i] < outDimOrigin || c[i] >= outDimOrigin + outDimLength)
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
			for(DBox framePiece : frame) {
				selectedDimIndex = 0;
				for(int i = 0;  i < obstacle.dimension; i++) {
					if(selectedDimIndex < selectedDimensions.length 
					   && selectedDimensions[selectedDimIndex] == i) {
						
						//the dimension is relevant
						selectedDimIndex++;
						//shift origin
						outLength[i] = framePiece.length[i] + constrainedPiece.length[i] - 1;
						//adjust size
						outOrigin[i] = framePiece.origin[i]- ( constrainedPiece.length[i] - 1 ) 
									   - constrainedPiece.origin[i];
						
					} else {
						//the dimension is not relevant, outbox covers the whole space
						outOrigin[i] = IntDomain.MinInt;
						outLength[i] = IntDomain.MaxInt-IntDomain.MinInt;
					}
				}

				assert(outBox.checkInvariants() == null) : outBox.checkInvariants();

				if(outBox.containsPoint(c))
					return outBox;
				 
			}
		
		
		return null;
	}


	@Override
	public String toString() {

		StringBuilder result = new StringBuilder();

		result.append("ObstacleObject(o").append(obstacle.no).append(", ");
		result.append(Arrays.toString(selectedDimensions)).append(", ");
		result.append(frame.toString());
		
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
	
}
