/**
 *  Shape.java 
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedList;

import org.jacop.util.SimpleArrayList;

/**
 * 
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 * 
 * A shape is composed of a set of shifted boxes.
 * 
 */
public class Shape {
	
	/**
	 * The collection of DBoxes that constitute the shape.
	 */
	public Collection<DBox> boxes;

	/**
	 * It specifies the smallest bounding box which encapsulates all boxes constituting the shape. 
	 */
	public final DBox boundingBox;
	
	/**
	 * It defines unique shape id which is used by geost objects to define their shapes.
	 */
	public int no;
	
	/**
	 * It defines the area (2D) or volume (3D) of the shape. 
	 */
	private int area;
	
	private SimpleArrayList<DBox> holes = null;
	
	/**
	 * It specifies the arguments required to be saved by an XML format as well as 
	 * the constructor being called to recreate an object from an XML format.
	 */
	public static String[] xmlAttributes = {"no", "boxes"};

	/**
	 * It constructs a shape with a given id based on a specified collection of Dboxes.
	 *  
	 * @param no the unique identifier of the created shape.
	 * @param boxes the collection of boxes constituting the shape.
	 */
	public Shape(int no, Collection<DBox> boxes) {
		
		this.no = no;
		this.boxes = boxes;
		area = -1; // lazily initialized
		
		// TODO is it really lazily initialized?
		//the bounding box is lazily initialized
		boundingBox = computeBoundingBox();
		
		assert (checkInvariants() == null) : checkInvariants();
	}
	
	/**
	 * It constructs a shape from only one DBox. 
	 * 
	 * @param id shape unique identifier.
	 * @param box the single dbox specifying the shape.
	 */
	public Shape(int id, DBox box){
		this.no = id;
		
		
		this.boxes = new ArrayList<DBox>(1);
		boxes.add(box);
		
		this.boundingBox = box;
		
		assert (checkInvariants() == null) : checkInvariants();
	}
	
	/**
	 * It constructs a shape with a given id based on a single dbox
	 * specified by the origin and length arrays.
	 * 
	 * @param id the unique identifier of the constructed shape.
	 * @param origin it specifies the origin of the dbox specifying the shape.
	 * @param length it specifies the length of the dbox specifying the shape.
	 */
	public Shape(int id, int[] origin, int[] length) {
		
		this.no = id;
		
		boundingBox = new DBox(origin, length);
		boxes = new ArrayList<DBox>(1);
		boxes.add(boundingBox);
		
		assert checkInvariants() == null : checkInvariants();
	}

	/**
	 * It checks whether the shape object is consistent.
	 * 
	 * @return It returns the string description of the problem, or null if no problem 
	 * with data structure consistency encountered. 
	 */
	public String checkInvariants(){
		
		if(boxes == null)
			return "uninitialized shifted box set";
		
		for(DBox b : boxes)
			if ( b == null )
				return "shape contains a null box";
		
		return null;
	}

	/**
	 * It returns the dboxes defining the shape.
	 * 
	 * @return the collection of dboxes defining the shape.
	 */
	public Collection<DBox> components() {
		return boxes;
	}
	
	/**
	 * It computes the bounding box of the given shape. 
	 * 
	 * @return the bounding box covering all boxes constituting the shape.
	 */
	private DBox computeBoundingBox() {
		
		int[] mins = null;
		int[] maxes = null;
		int dim = 0;
		
		for(DBox b : boxes) {
			
			if(mins == null) {
				dim = b.origin.length;
				mins = new int[dim];
				maxes = new int[dim];
				Arrays.fill(mins, Integer.MAX_VALUE);
				Arrays.fill(maxes, Integer.MIN_VALUE);
			}
			
			for(int i = 0; i < dim; i++){
				mins[i] = Math.min(mins[i], b.origin[i]);
				maxes[i] = Math.max(maxes[i], b.origin[i] + b.length[i]);
			}
			
		}
		
		//replace the maxes by the actual sizes
		for(int i = 0; i<dim; i++){
			maxes[i] = maxes[i]-mins[i];
		}
		
		return new DBox(mins, maxes);
	}

	/**
	 * It returns previously computed bounding box of the shape.
	 * 
	 * @return the bounding box of the shape.
	 */
	public final DBox boundingBox() {
		return boundingBox;
	}

	/**
	 * It checks whether a given point lies within any of the shapes boxes.
	 * 
	 * @param point the point which containment within a shape is being checked.
	 * 
	 * @return true if the point lies within a shape, false otherwise.
	 */
	public boolean containsPoint(int[] point) {
		
		Iterator<DBox> i = boxes.iterator();
		
		boolean inside = false;
		
		while(!inside && i.hasNext())
			inside = i.next().containsPoint(point);
		
		return inside;
		
	}
	
	/**
	 * It (re)initializes the holes
	 */
	private void initHoles(){
		/*
		 * the holes are the result of the subtraction to the bounding
		 * box of all components
		 */
		if(holes == null){
			holes = new SimpleArrayList<DBox>();
		} else {
			if (!holes.isEmpty()){
				for(DBox hole : holes){
					DBox.dispatchBox(hole);
				}
				holes.clearNoGC();//DBoxes will not be garbage anyway
			}
		}
		
		/*in order to be able to get a correct frame in the limit cases,
		 * where the portion of the frame is flat, we need quarter units.
		 * A simple way to get them is to change the scale to four times the original size,
		 * and add an extra unit to the boxes, which thus corresponds to a quarter unit
		 */
		final int dimension = boundingBox.origin.length;
		Collection<DBox> rescaledBoxes = new ArrayList<DBox>(boxes.size());
		for(DBox b : boxes){
			DBox scaled = DBox.newBox(dimension);
			for(int i = 0; i < dimension; i++) {
				scaled.origin[i] = b.origin[i]*4 - 1; //1 extra quarter unit
				scaled.length[i] = b.length[i]*4 + 2; //1 extra quarter unit, + the one removed from the origin
			}
			rescaledBoxes.add(scaled);
		}
		
		
		
		DBox scaledBoundingBox = DBox.newBox(dimension);
		
		for(int i = 0; i < dimension; i++) {
			scaledBoundingBox.origin[i] = boundingBox.origin[i]*4;
			scaledBoundingBox.length[i] = boundingBox.length[i]*4;
		}
		
		scaledBoundingBox.subtractAll(rescaledBoxes, holes);
		
		//release boxes
		for(DBox b : rescaledBoxes){
			DBox.dispatchBox(b);
		}
		DBox.dispatchBox(scaledBoundingBox);
	}
	
	/**
	 * It returns the set of holes of this shape. The set of holes is
	 * a set of boxes with the following properties, once scaled by a factor 1/4:
	 *   - none of its components overlaps with the shape's components
	 *   - its union with the set of components covers the bounding box of the shape, except for
	 *     an empty area at the component boundary that has size 1/4
	 *     
	 * @return the set of holes of this shape.
	 */
	public Collection<DBox> holes(){
		if(holes == null){
			initHoles();
		}
		return holes;
	}
	
	@Override
	public String toString(){
		StringBuilder builder = new StringBuilder();
		builder.append("Shape(");
		for(DBox b : boxes)
			builder.append(b).append(", ");
		builder.deleteCharAt(builder.length()-1);
		builder.deleteCharAt(builder.length()-1);
		
		builder.append(")");
		return builder.toString();
	}
	

	/**
	 * It computes the area (2D), volumen (3D) of the shape.
	 *  
	 * @return the area/volume of the shape.
	 */
	public int area(){
		
		if(area < 0){
			int holeArea = 0;
			Collection<DBox> actualHoles = new LinkedList<DBox>();
			actualHoles = boundingBox.subtractAll(boxes, actualHoles);
			for(DBox hole : actualHoles){
				holeArea += (hole.area());
				DBox.dispatchBox(hole);
			}

			assert boundingBox.area() - holeArea > 0 : "negative area";

			area =  boundingBox.area() - holeArea;
		}
		return area;
	}
	
	/**
	 * It computes a collection of DBoxes that form the same shape, but that are certain
	 * to not overlap
	 * 
	 * This implementation is probably not the most efficient possible representation.
	 * 
	 * @return non overlapping representation of the shape.
	 */
	public Collection<DBox> noOverlapRepresentation(){
		Collection<DBox> actualHoles = new ArrayList<DBox>();
		actualHoles = boundingBox.subtractAll(boxes, actualHoles);
		return boundingBox.subtractAll(actualHoles, new ArrayList<DBox>());
	}
	
}
