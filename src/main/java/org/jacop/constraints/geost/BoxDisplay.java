/**
 *  BoxDisplay.java
 *   
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
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Image;

import javax.swing.JFrame;

import org.jacop.core.IntVar;

/**
 * @author Marc-Olivier Fleury and Radoslaw Szymanek
 * 
 * It specifies  a simple functionality to graphically represent 2D geost. It was 
 * mostly used during development phase but it may be still useful if user is interested
 * in visualizing Geost constraint. 
 * 
 */
public class BoxDisplay extends JFrame {

	/**
	 * It specifies the serial UID. 
	 */
	private static final long serialVersionUID = -1620053778620352318L;

	/**
	 * It specifies the number of pixels per unit of length.
	 */
	public int pixelsPerUnit = 5;
	
	/**
	 * It defines the shift in x dimension for drawing.
	 */
	public int xCellsShift = 0;
	
	/**
	 * It defines the shift in x dimension for drawing.
	 */
	public int yCellsShift = 0;

	private Image bufferImage = null;
	private Image displayImgae = null; // page flipping
	
	/**
	 * It constructs a display to visualize Geost objects/constraint.
	 * 
	 * @param pixelsPerUnit number of pixels on our first mission.
	 */
	public BoxDisplay(int pixelsPerUnit) {
		
		super();
		
		this.pixelsPerUnit = pixelsPerUnit;
		this.setSize(new Dimension(800,600));

		this.setResizable(false);
		setVisible(true);
		int width = getWidth();
		int height = getHeight();
		bufferImage = createImage(width, height);
		displayImgae = createImage(width, height);
		
	}
	
	
	/**
	 * It creates a display to visualize 2D geost constraint. 
	 *  
	 * @param pixelsPerUnit number of pixels per unit of object length. 
	 * @param title 
	 * @param geost geost constraint to visualize
	 */
	public void displayState(int pixelsPerUnit, String title, Geost geost){
		
		BoxDisplay display = new BoxDisplay(pixelsPerUnit, title);
		Color color = Color.black;
		
		for(GeostObject o : geost.objects) {
			display2DGeostObject(geost, o, color);
			color = color.brighter();
		}
		
		display.flip();
	
	}
	
	/**
	 * It displays the state of the geost constraint. 
	 * 
	 * @param domainWidth
	 * @param groundedOnly only grounded objects should be displayed.
	 * @param withFrames should frames describing non-overlapping constraint be displayed too?
	 * @param geost geost constraint being displayed.
	 */
	public void displayState(int domainWidth, boolean groundedOnly, boolean withFrames, Geost geost){
		
		Color color = Color.black;
	
		if(withFrames){
			for(InternalConstraint c : geost.internalConstraints){
				if(c instanceof ObstacleObjectFrame){
					Color frameColor = Color.GRAY;//new Color(c.hashCode());
					for(DBox fp : ((ObstacleObjectFrame) c).frame){
						display2DBox(fp, frameColor, true);
					}
				}
			}
		}
		
		for(GeostObject o : geost.objects){
			if(!groundedOnly || o.isGrounded()){
				color = new Color(o.hashCode());
				int heightMin = 0;
				int heightMax = 0;
				if(o.coords.length > 2){
					DBox bb = geost.shapeRegister[o.shapeID.min()].boundingBox;
					heightMin = o.coords[2].min() + bb.origin[2];
					heightMax = o.coords[2].max() + bb.length[2] + bb.origin[2]-1;
				}
				for(int height = heightMin; height <= heightMax; height++){
					for(int timeVal = o.start.min(), timeMax = o.end.min(); timeVal < timeMax; timeVal++){
						xCellsShift = timeVal*(domainWidth+1);
						yCellsShift = height*(domainWidth+1);

						display3DGeostObjectSlice(geost, o, color, height);
					}
				}
			}
		}
	}

	/*
	public static final void displayPool(BoxDisplay display, Color color){
		
		for(int i = 0; i<DBox.freeBoxes.size(); i++){
			SimpleArrayList<DBox> boxes = DBox.freeBoxes.get(i);
			for(int j = 0; j<boxes.size(); j++){
				display.display2DBox(boxes.get(j), color);
			}
		}
		
	}
	*/
	
	/**
	 * It constructs a window given the parameters like pixels per unit shape, 
	 * and name of the window.
	 * @param pixelsPerUnit number of pixels per unit length.
	 * @param name window name.
	 */
	public BoxDisplay(int pixelsPerUnit, String name){
		super(name);
		this.pixelsPerUnit = pixelsPerUnit;
		this.setSize(new Dimension(800,600));

		this.setResizable(false);
		setVisible(true);
		int width = getWidth();
		int height = getHeight();
		bufferImage = createImage(width, height);
		displayImgae = createImage(width, height);
		
		setDefaultCloseOperation(EXIT_ON_CLOSE);
	}
	
	
	/**
	 * It displays a given dbox in a black color.
	 *  
	 * @param b dbox to be displayed.
	 */
	public void display2DBox(DBox b){
		display2DBox(b, Color.BLACK);
	}
	
	/**
	 * It displays a given dbox using a given color. 
	 * @param b dbox to be displayed.
	 * @param color color to be used to draw dbox.
	 */
	public void display2DBox(DBox b, Color color){
		display2DBox(b, color, false);
	}
	
	
	/**
	 * It draws dboxes given color. If n-dimensional box supplied
	 * then its 2D projection will be drawn only if it cuts the plane. 
	 * 
	 * @param b dbox to be displayed.
	 * @param color color to be used. 
	 * @param fill should the object be filled. 
	 */
	public void display2DBox(DBox b, Color color, boolean fill){
		//a box that has dimension more than 2 should only be drawn if it cuts the plane
		boolean shouldDraw = true;
		if(b.origin.length > 2){
			for(int i = 2; shouldDraw && i < b.origin.length; i++){
				if(b.origin[i] > 0 || b.origin[i]+b.length[i] < 0){
					shouldDraw = false;
				}
			}
		}
		if(shouldDraw){
			Graphics g = bufferImage.getGraphics();
			int height = this.getContentPane().getHeight() -10;
			g.setColor(color);
			if(fill){
				g.fillRect(10+(xCellsShift + b.origin[0])*pixelsPerUnit, height-(yCellsShift + b.origin[1]+b.length[1])*pixelsPerUnit, 
						(b.length[0] > 0) ? b.length[0]*pixelsPerUnit-1 : 1,
								(b.length[1] > 0) ? b.length[1]*pixelsPerUnit-1 : 1);
			} else {
				g.drawRect(10+(xCellsShift + b.origin[0])*pixelsPerUnit, height-(yCellsShift + b.origin[1]+b.length[1])*pixelsPerUnit, 
						(b.length[0] > 0) ? b.length[0]*pixelsPerUnit-1 : 1,
								(b.length[1] > 0) ? b.length[1]*pixelsPerUnit-1 : 1);
			}

			repaint();
		}
	}
	
	
	
	/**
	 * It draws the grid. 
	 * 
	 * @param color the color in which the grid should be drawn.
	 */
	public void drawGrid(Color color){
		
		Graphics g = bufferImage.getGraphics();
		g.setColor(color);
		int height = this.getContentPane().getHeight() -10;
		int width = this.getContentPane().getWidth();
		int i = 10;
		int j = 0;
		while(i < width){
			g.drawLine(i, 0, i, height);
			i+=pixelsPerUnit;
		}
		while (j< height){
			g.drawLine(0, j, width, j);
			j+= pixelsPerUnit;
		}
	}
	
	/**
	 * It displays a 2D geost object. 
	 * 
	 * @param geost Geost constraint containting information about object shapes. 
	 * @param o geost object to be drawn. 
	 * @param c color in which the remaining units should be painted with.
	 */
	public void display2DGeostObject(Geost geost, GeostObject o, Color c){
		Shape shape = geost.getShape(o.shapeID.min());
		DBox area = DBox.newBox(o.dimension);
		
		for(DBox piece : shape.boxes){
			for(int i = 0; i<o.dimension; i++){
				IntVar coordVar = o.coords[i];
				area.origin[i] = coordVar.min() + piece.origin[i];
				area.length[i] = coordVar.max() /*+ hole.origin[i]*/ + piece.length[i]
				                  - coordVar.min()/*-hole.origin[i]*/;
			}
			display2DBox(area, c, true);
		}
		
		//draw bounding box
		final boolean draw_bounding_box = false;
		if(draw_bounding_box){
		Color outColor = c.brighter();
		for(int i = 0; i<o.dimension; i++){
			IntVar coordVar = o.coords[i];
			area.origin[i] = coordVar.min() + shape.boundingBox.origin[i];
			area.length[i] = coordVar.max() /*+ hole.origin[i]*/ + shape.boundingBox.length[i]
			                  - coordVar.min()/*-hole.origin[i]*/;
		}
		display2DBox(area, outColor, false);
		}
	}
	
	/**
	 * It displays 3D geost by slicing 3rd dimension at given point and displaying the resulting slice. 
	 * 
	 * @param geost Geost constraint containing information about shapes.
	 * @param o object to be displayed.
	 * @param c color the object should be painted with. 
	 * @param sliceHeight the slice position in the third dimension.
	 */
	public void display3DGeostObjectSlice(Geost geost, GeostObject o, Color c, int sliceHeight){
		Shape shape = geost.getShape(o.shapeID.min());
		DBox area = DBox.newBox(2);
		
		for(DBox piece : shape.boxes){
			if(piece.length.length < 3 || piece.origin[2] <= sliceHeight && piece.origin[2]+piece.length[2] > sliceHeight){
			for(int i = 0; i<2; i++){
				IntVar coordVar = o.coords[i];
				area.origin[i] = coordVar.min() + piece.origin[i];
				area.length[i] = coordVar.max() /*+ hole.origin[i]*/ + piece.length[i]
				                  - coordVar.min()/*-hole.origin[i]*/;
			}
			display2DBox(area, c, true);
			}
		}
		//draw bounding box
		final boolean draw_bounding_box = false;
		if(draw_bounding_box){
		Color outColor = c.brighter();
		for(int i = 0; i<o.dimension; i++){
			IntVar coordVar = o.coords[i];
			area.origin[i] = coordVar.min() + shape.boundingBox.origin[i];
			area.length[i] = coordVar.max() /*+ hole.origin[i]*/ + shape.boundingBox.length[i]
			                  - coordVar.min()/*-hole.origin[i]*/;
		}
		display2DBox(area, outColor, false);
		}
	}
	
	/**
	 * It displays a 2D point given its coordinates and color. 
	 * 
	 * @param point point coordinates.
	 * @param color color the point should be painted with.
	 */
	public void display2DPoint(int[] point, Color color){
		Graphics g = bufferImage.getGraphics();
		int height = this.getContentPane().getHeight() -10;
		g.setColor(color);
		g.fillOval(10+point[0]*pixelsPerUnit, height-(point[1]+1)*pixelsPerUnit, pixelsPerUnit/2,pixelsPerUnit/2);

		repaint();
	}
	
	/**
	 * It displays 2D Geost object given its shape.
	 * 
	 * @param o geost object to be displayed.
	 * @param s the shape of the object to be displayed.
	 */
	public void display2DObject(GeostObject o, Shape s){
		Graphics g = bufferImage.getGraphics();
		int height = this.getContentPane().getHeight() -10;
		DBox bb = s.boundingBox();
		int ox = o.coords[0].min()*pixelsPerUnit;
		int oy = o.coords[1].min()*pixelsPerUnit;
		g.setColor(Color.BLUE);
		g.drawRect(10+ox+bb.origin[0]*pixelsPerUnit, height-oy-(bb.origin[1]+bb.length[1])*pixelsPerUnit, bb.length[0]*pixelsPerUnit, bb.length[1]*pixelsPerUnit);
		
		//draw domain
		g.setColor(Color.GREEN);
		int dw =  (o.coords[0].max()-o.coords[0].min())*pixelsPerUnit;
		int dh = (o.coords[1].max()-o.coords[1].min())*pixelsPerUnit;
		g.drawRect(10+ox, height-dh-oy,dw, dh);
		g.fillRect(10+ox, height-oy-pixelsPerUnit/2, pixelsPerUnit/2, pixelsPerUnit/2);
		
		for(DBox b: s.components()){
			display2DBox(b, Color.black);
		}
		
		repaint();
	}
	
	/**
	 * Clear the paint area so drawing can start on fresh canvas. 
	 */
	public void eraseAll(){

		Graphics g = bufferImage.getGraphics();
		g.clearRect(0, 0, getWidth(), getHeight());
	}
	
	/**paints all objects, repaint only if requested to*/
	public void paint(Graphics g) {
		super.paint(g);
		g.drawImage(displayImgae, 0, 0, null);
	}

	/**same as paint*/
	public void update(Graphics g) {
		super.update(g);
		g.drawImage(displayImgae, 0, 0, null);
	}
	
	/**
	 * flips images, making previous operations visible
	 */
	public void flip(){
		Image i = displayImgae;
		displayImgae = bufferImage;
		bufferImage = i;
	}
}
