/**
 *  TraceGenerator.java 
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

package org.jacop.search;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Stack;

import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.sax.SAXTransformerFactory;
import javax.xml.transform.sax.TransformerHandler;
import javax.xml.transform.stream.StreamResult;

import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalEnumeration;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.AttributesImpl;


/**
 * It is a wrapper over Select methods that makes it possible to trace search and 
 * variables' changes.
 * 
 * It generates xml format accepted by CPViz tool developed by Helmut Simonis.
 * 
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 3.1
 */

/**
 * TODO
 * TraceGenerator should accept as input to constructor a Search object. It should 
 * get all the previous listeners and establish itself as the parent of those listeners
 * and substitute them for itself in the search provided. It should ask them to get the 
 * proper return value for listener functions which are returning a code. 
 * 
 * It should later act as suggested by those listeners. This way there may be no need
 * for checking/informing trace if we search for all solutions or just one. 
 * 
 * However, on safety side before TraceGenerator object is created and search object passed
 * to it maybe search object should be already properly set.
 * 
 * Can we wrap one TraceGenerator within another TraceGenerator? It should be possible.
 * 
 * getChoiceVariable in TraceGenerator assumes that the internal 
 * select choice point does not return choice point as primitive 
 * constraint. It incorrectly assumes that if no variable is given
 * by getChoiceVariable then the search is finished. We need all
 * check that getChoiceConstraint returns false. 
 * 
 * Can CPviz handle search for Set variables handle correctly 100%? 
 * If not maybe we should just make TraceGenerator<T extends IntVar>?
 * 
 * 
 * FilterDom should not use string representation of the domain just
 * use Enumeration to get values within domain and create required 
 * String. It should be more or less the same what toString() of domain
 * is doing.
 * 
 */

public class TraceGenerator<T extends Var> 
	implements SelectChoicePoint<T>, 
			   ConsistencyListener, 
			   ExitChildListener<T>, 
			   ExitListener {

	
	ConsistencyListener[] consistencyListeners;

	ExitChildListener<T>[] exitChildListeners;

	ExitListener[] exitListeners;

	/**
	 * It stores the original select choice point method that is used by this trace 
	 * wrapper.
	 */
	SelectChoicePoint<T> select;

	/** 
	 * It stores information about var being selected by internal select choice point. 
	 */
	T selectedVar;
	
	/**
	 * It specifies information about value being selected by internal select choice point. 
	 */
	int selectedValue;
	
	/**
	 * The file containing information about tree for CPviz format. 
	 */
	public final String treeFilename;
	
	/**
	 * The file containing visualisation information. 
	 */
	public final String visFilename;

	/**
	 * An xml handler for tree file. 
	 */
	TransformerHandler hdTree;
	
	/**
	 * An xml handler for visualization file.
	 */
	TransformerHandler hdVis;

	Stack<SearchNode> searchStack = new Stack<SearchNode>();
	SearchNode currentSearchNode;
	int searchNodeId = 1;
	int visualisationNodeId = 1;

	/**
	 * It specifies the list of variables that are being traced.
	 */
	public ArrayList<Var> tracedVar = new ArrayList<Var>();


	public HashMap<Var, Integer> varIndex = new HashMap<Var, Integer>();

	/**
	 * It creates a CPviz trace generator around proper select choice point object.
	 * 
     * @param search it specifies search method used for depth-first-search.
	 * @param select it specifies how the select choice points are being generated.
	 */
	public TraceGenerator(Search<T> search, SelectChoicePoint<T> select) {
		
		this(search, select, new Var[0], "tree.xml", "vis.xml");
				
	}

	/**
	 * It creates a CPviz trace generator around proper select choice point object.
	 * 
     * @param search it specifies search method used for depth-first-search.
	 * @param select it specifies how the select choice points are being generated.
     * @param treeFilename it specifies the file name for search tree trace (default tree.xml).
     * @param visFilename it specifies the file name for variable trace (default vis.xml).
	 */
	public TraceGenerator(Search<T> search, SelectChoicePoint<T> select, String treeFilename, String visFilename) {
		
		this(search, select, new Var[0], treeFilename, visFilename);
		
	}

	
	/**
	 * 
	 * It creates a CPviz trace generator around proper select choice point object.
	 * 
     * @param search it specifies search method used for depth-first-search.
	 * @param select it specifies how the select choice points are being generated.
	 * @param vars it specifies variables which are being traced.
	 */
	public TraceGenerator(Search<T> search, SelectChoicePoint<T> select, Var[] vars) {
		
		this(search, select, vars, "tree.xml", "vis.xml");

	}

	
	/**
	 * 
	 * It creates a CPviz trace generator around proper select choice point object.
	 * 
	 * @param select it specifies how the select choice points are being generated.
	 * @param vars it specifies variables which are being traced.
     * @param treeFilename it specifies the file name for search tree trace (default tree.xml).
     * @param visFilename it specifies the file name for variable trace (default vis.xml).
	 */
	private TraceGenerator(SelectChoicePoint<T> select, Var[] vars, String treeFilename, String visFilename) {
		
		this.select = select;
		this.treeFilename = treeFilename;
		this.visFilename = visFilename;
		
		SearchNode rootNode = new SearchNode();
		rootNode.id = 0;
		searchStack.push(rootNode);

// 		for (Var v : vars) {
		for (int i=0; i<vars.length; i++) {
		    tracedVar.add(vars[i]);
		    varIndex.put(vars[i], i);
		}

		prepareTreeHeader();
		prepareVizHeader();

	}

	/**
	 * 
	 * It creates a CPviz trace generator around proper select choice point object.
	 * 
     * @param search it specifies search method used for depth-first-search.
	 * @param select it specifies how the select choice points are being generated.
	 * @param vars it specifies variables which are being traced.
     * @param treeFilename it specifies the file name for search tree trace (default tree.xml).
     * @param visFilename it specifies the file name for variable trace (default vis.xml).
	 */
	public TraceGenerator(Search<T> search, SelectChoicePoint<T> select, Var[] vars, String treeFilename, String visFilename) {

		this(select, vars, treeFilename, visFilename);
		
		if (search.getConsistencyListener() == null) {
			search.setConsistencyListener(this);
		}
		else {
			ConsistencyListener current = search.getConsistencyListener();
			search.setConsistencyListener(this);
			setChildrenListeners(current);
		}

		if (search.getExitChildListener() == null) {
			search.setExitChildListener(this);
		}
		else {
			ExitChildListener<T> current = search.getExitChildListener();
			search.setExitChildListener(this);
			setChildrenListeners(current);
		}

		if (search.getExitListener() == null) {
			search.setExitListener(this);
		}
		else {
			ExitListener current = search.getExitListener();
			search.setExitListener(this);
			setChildrenListeners(current);
		}

		
	}

	
	public T getChoiceVariable(int index) {

		selectedVar = select.getChoiceVariable(index);

		if (selectedVar != null) {
			
			currentSearchNode = new SearchNode();
			currentSearchNode.v = selectedVar;
			currentSearchNode.dom = selectedVar.dom().cloneLight();
		
		}

		return selectedVar;
	
	}

	public int getChoiceValue() {
		
		selectedValue = select.getChoiceValue();
		currentSearchNode.val = selectedValue;
		currentSearchNode.id = searchNodeId++;
		currentSearchNode.previous = searchStack.peek().id;

		searchStack.push(currentSearchNode);

		return selectedValue;
	}

	public PrimitiveConstraint getChoiceConstraint(int index) {

		PrimitiveConstraint c = select.getChoiceConstraint(index);

		if (c == null) {
		    if (currentSearchNode == null)
			currentSearchNode = new SearchNode();

		    generateSuccessNode(currentSearchNode.id);
		    generateVisualizationNode(currentSearchNode.id, true);

		} else {

		    currentSearchNode = new SearchNode();
		    currentSearchNode.c = c;
		    currentSearchNode.id = searchNodeId++;
		    currentSearchNode.previous = searchStack.peek().id;

		    searchStack.push(currentSearchNode);

		}
		
		return c;
	}

	public IdentityHashMap<T, Integer> getVariablesMapping() {
		return select.getVariablesMapping();
	}

	public int getIndex() {
		return select.getIndex();
	}

	public String toString() {
		return "";
	}


	// =================================================================
	// Metods for tracing using ConsistencyListener

    public void setChildrenListeners(ConsistencyListener[] children) {
		consistencyListeners = children;
	}


	public void setChildrenListeners(ConsistencyListener child) {
		consistencyListeners = new ConsistencyListener[1];
		consistencyListeners[0] = child;
	}

	public boolean executeAfterConsistency(boolean consistent) {

		if (consistencyListeners != null) {
			boolean code = false;
			for (int i = 0; i < consistencyListeners.length; i++)
				code |= consistencyListeners[i].executeAfterConsistency(consistent);
			consistent = code;
		}
		
		if (!consistent) {
			SearchNode sn =  searchStack.peek();
			if (sn.id != 0) { // not root node 
				if (sn.c == null) {
					if (sn.equal) {  // fail x == val
						generateFailNode(sn.id, sn.previous, sn.v.id(), 
								sn.v.dom().getSize(), sn.val);
					}
					else {  // fail x != val
						generateFailcNode(sn.id, sn.previous, sn.v.id(), 
								sn.dom.getSize(), sn.dom);
					}
				} else
					if (sn.equal) {  // fail x == val
						generateFailcNode(sn.id, sn.previous, sn.c);
					}
					else {  // fail x != val
						generateFailcNode(sn.id, sn.previous, new Not(sn.c));
					}
				generateVisualizationNode(currentSearchNode.id, false);					
			}
		}
		else {
			SearchNode sn =  searchStack.peek();
			if (sn.id != 0) { // not root node
				if (sn.c == null) {
					if (sn.equal) {  // try x == val
						generateTryNode(sn.id, sn.previous, sn.v.id(), 
								sn.v.dom().getSize(), sn.val);
					}
					else {  // try x != val
						generateTrycNode(sn.id, sn.previous, sn.v.id(), 
								sn.dom.getSize(), sn.dom);
					}
				}
				else {

					if (sn.equal) {  // try x == val
						generateTrycNode(sn.id, sn.previous, sn.c);
					}
					else {  // try x != val
						generateTrycNode(sn.id, sn.previous, new Not(sn.c));
					}

				}
				generateVisualizationNode(currentSearchNode.id, true);				
			}
		}

		return consistent;
	}

	

	// =================================================================
	// Metods for tracing using ExitChildListener

	public void setChildrenListeners(ExitChildListener<T>[] children) {

		exitChildListeners = children;
	}

	public void setChildrenListeners(ExitListener[] children) {
		exitListeners = children;
	}

	public boolean leftChild(T var, int value, boolean status) {

		boolean returnCode = true;
		
		if (exitChildListeners != null) {
			boolean code = false;
			for (int i = 0; i < exitChildListeners.length; i++)
				code |= exitChildListeners[i].leftChild(var, value, status);
			returnCode = code;
		}

		currentSearchNode = searchStack.pop();
		SearchNode previousSearchNode = currentSearchNode; 

		if (!status && returnCode) {

			currentSearchNode = new SearchNode();
			currentSearchNode.v = var;

			if (previousSearchNode.dom instanceof org.jacop.core.IntDomain)
				currentSearchNode.dom = ((IntDomain)previousSearchNode.dom).subtract( value );
			else if (previousSearchNode.dom instanceof org.jacop.set.core.SetDomain)
				currentSearchNode.dom = ((SetDomain)previousSearchNode.dom).subtract( value, value );

			currentSearchNode.val = value;
			currentSearchNode.id = searchNodeId++;
			currentSearchNode.equal = false;
			currentSearchNode.previous = searchStack.peek().id;

			searchStack.push(currentSearchNode);

		}

		return returnCode;
	
	}

	public boolean leftChild(PrimitiveConstraint choice, boolean status) {
	
		boolean returnCode = true;
		
		if (exitChildListeners != null) {
			boolean code = false;
			for (int i = 0; i < exitChildListeners.length; i++)
				code |= exitChildListeners[i].leftChild(choice, status);
			returnCode = code;
		}

		currentSearchNode = searchStack.pop();
//		SearchNode previousSearchNode = currentSearchNode; 

		if (!status && returnCode) {

			currentSearchNode = new SearchNode();
			// currentSearchNode.v = var;

//			if (previousSearchNode.dom instanceof JaCoP.core.IntDomain)
//				currentSearchNode.dom = ((IntDomain)previousSearchNode.dom).subtract( value );
//			else if (previousSearchNode.dom instanceof JaCoP.set.core.SetDomain)
//				currentSearchNode.dom = ((SetDomain)previousSearchNode.dom).subtract( value, value );

			// currentSearchNode.val = value;
			currentSearchNode.id = searchNodeId++;
			currentSearchNode.equal = false;
			currentSearchNode.c = choice;
			currentSearchNode.previous = searchStack.peek().id;

			searchStack.push(currentSearchNode);

		}

		return returnCode;
		
	}

	public void rightChild(T var, int value, boolean status) {

		currentSearchNode = searchStack.pop();
		
	}

	public void rightChild(PrimitiveConstraint choice, boolean status) {

		currentSearchNode = searchStack.pop();
	
	}

	// =================================================================
	// Metods for tracing using ExitListener

	public void setChildrenListeners(ExitChildListener<T> child) {
		exitChildListeners = new ExitChildListener[1];
		exitChildListeners[0] = child;
	}

	public void setChildrenListeners(ExitListener child) {
		exitListeners = new ExitListener[1];
		exitListeners[0] = child;
	}
	
	public void executedAtExit(Store store, int solutionsNo) {

		try {
			
			hdTree.endElement("", "", "tree");
			hdTree.endDocument();

			hdVis.endElement("", "", "visualization");
			hdVis.endDocument();

		} catch (SAXException e) {
			e.printStackTrace();
		}
		
	}

	
	// Methods to prepare xml files used by visualization tools.

	void prepareTreeHeader() {
		
		PrintWriter printWriter;

		try {
			printWriter = new PrintWriter(new FileOutputStream(treeFilename));
		} catch (FileNotFoundException e) {
			e.printStackTrace();
			printWriter = new PrintWriter( new StringWriter() );
		}

		StreamResult streamResult = new StreamResult(printWriter);
		SAXTransformerFactory tf = (SAXTransformerFactory) SAXTransformerFactory.newInstance();

		try {

			hdTree = tf.newTransformerHandler();

			Transformer serializer = hdTree.getTransformer();
			serializer.setOutputProperty(OutputKeys.ENCODING, "UTF-8"); // "ISO-8859-1");
			serializer.setOutputProperty(OutputKeys.INDENT, "yes");
			serializer.setOutputProperty(OutputKeys.STANDALONE, "yes");
			serializer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "4");

			hdTree.setResult(streamResult);

			hdTree.startDocument();

			AttributesImpl atts = new AttributesImpl();
			atts.addAttribute("", "", "version", "CDATA", "1.0");
			atts.addAttribute("", "", "xmln:xsi", "CDATA", "http://www.w3.org/2001/XMLSchema-instance");
			atts.addAttribute("", "", "xsi:noNamespaceSchemaLocation", "CDATA", "tree.xsd");

			String ourText = " Generated by JaCoP solver; " + getDateTime() + " ";
			char[] comm = ourText.toCharArray();
			hdTree.comment(comm, 0, comm.length);

			hdTree.startElement("", "", "tree", atts);

			atts = new AttributesImpl();
			atts.addAttribute("", "", "id", "CDATA", "0");
			hdTree.startElement("", "", "root", atts);
			hdTree.endElement("", "", "root");

		} catch (TransformerConfigurationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (SAXException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}


	void prepareVizHeader() {
		
		PrintWriter printWriter;

		try {
			printWriter = new PrintWriter(new FileOutputStream(visFilename));
		} catch (FileNotFoundException e) {
			e.printStackTrace();
			printWriter = new PrintWriter( new StringWriter() );
		}

		StreamResult streamResult = new StreamResult(printWriter);
		SAXTransformerFactory tf = (SAXTransformerFactory) SAXTransformerFactory.newInstance();

		try {

			hdVis = tf.newTransformerHandler();

			Transformer serializer = hdVis.getTransformer();
			serializer.setOutputProperty(OutputKeys.ENCODING, "UTF-8"); // "ISO-8859-1");
			serializer.setOutputProperty(OutputKeys.INDENT, "yes");
			serializer.setOutputProperty(OutputKeys.STANDALONE, "yes");
			serializer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "4");

			hdVis.setResult(streamResult);

			hdVis.startDocument();

			AttributesImpl atts = new AttributesImpl();
			atts.addAttribute("", "", "version", "CDATA", "1.0");
			atts.addAttribute("", "", "xmlns:xsi", "CDATA", "http://www.w3.org/2001/XMLSchema-instance");
			atts.addAttribute("", "", "xsi:noNamespaceSchemaLocation", "CDATA", "visualization.xsd");

			String ourText = " Generated by JaCoP solver; " + getDateTime() + " ";
			char[] comm = ourText.toCharArray();
			hdVis.comment(comm, 0, comm.length);

			hdVis.startElement("", "", "visualization", atts);

			// visualizer
			if (tracedVar.size() != 0) {
				AttributesImpl visAtt = new AttributesImpl();
				visAtt.addAttribute("", "", "id", "CDATA", "1");
				visAtt.addAttribute("", "", "type", "CDATA", "vector");
				visAtt.addAttribute("", "", "display", "CDATA", "expanded");
				visAtt.addAttribute("", "", "group", "CDATA", "default");
				visAtt.addAttribute("", "", "x", "CDATA", "0");
				visAtt.addAttribute("", "", "y", "CDATA", "0");

				int minV = minValue(tracedVar), maxV = maxValue(tracedVar);
				visAtt.addAttribute("", "", "width", "CDATA", ""+tracedVar.size());
				visAtt.addAttribute("", "", "height", "CDATA", ""+(int)(maxV-minV+1));

				visAtt.addAttribute("", "", "min", "CDATA", ""+minV);
				visAtt.addAttribute("", "", "max", "CDATA", ""+maxV);

				hdVis.startElement("", "", "visualizer", visAtt);
				hdVis.endElement("", "", "visualizer");
			}

			generateVisualizationNode(0, true);


		} catch (TransformerConfigurationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (SAXException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public void addTracedVar (Var v) {
		tracedVar.add(v);
	}

	private int minValue(ArrayList<Var> vars) {
		int min = org.jacop.core.IntDomain.MaxInt;
		if (vars.get(0) instanceof org.jacop.core.IntVar)
			for (Var v : vars)
				min = (min < ((IntVar)v).min()) ? min : ((IntVar)v).min();

		return min;
	}

	private int maxValue(ArrayList<Var> vars) {
		int max = org.jacop.core.IntDomain.MinInt;
		if (vars.get(0) instanceof org.jacop.core.IntVar)
			for (Var v : vars)
				max = (max > ((IntVar)v).max()) ? max : ((IntVar)v).max();

		return max;
	}

	private String getDateTime() {
		DateFormat dateFormat = new SimpleDateFormat("yyyy/MM/dd HH:mm:ss");
		Date date = new Date();
		return dateFormat.format(date);
	}

	void generateSuccessNode(int searchNodeId) {
		try {
			AttributesImpl atts = new AttributesImpl();
			atts.addAttribute("", "", "id", "CDATA", ""+searchNodeId);
			hdTree.startElement("", "", "succ", atts);
			hdTree.endElement("", "", "succ");

		} catch (SAXException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	void generateTryNode(int searchNodeId, int parentNode, String name, int size, int value) {
		try {
			AttributesImpl atts = new AttributesImpl();
			atts.addAttribute("", "", "id", "CDATA", ""+searchNodeId);
			atts.addAttribute("", "", "parent", "CDATA", ""+parentNode);
			atts.addAttribute("", "", "name", "CDATA", name);
			atts.addAttribute("", "", "size", "CDATA", ""+size);
			atts.addAttribute("", "", "value", "CDATA", ""+value);
			hdTree.startElement("", "", "try", atts);
			hdTree.endElement("", "", "try");

		} catch (SAXException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	void generateFailNode(int searchNodeId, int parentNode, String name, int size, int value) {
		try {
			AttributesImpl atts = new AttributesImpl();
			atts.addAttribute("", "", "id", "CDATA", ""+searchNodeId);
			atts.addAttribute("", "", "parent", "CDATA", ""+parentNode);
			atts.addAttribute("", "", "name", "CDATA", name);
			atts.addAttribute("", "", "size", "CDATA", ""+size);
			atts.addAttribute("", "", "value", "CDATA", ""+value);
			hdTree.startElement("", "", "fail", atts);
			hdTree.endElement("", "", "fail");

		} catch (SAXException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	void generateTrycNode(int searchNodeId, int parentNode, String name, int size, Domain dom) {
		try {
			AttributesImpl atts = new AttributesImpl();
			atts.addAttribute("", "", "id", "CDATA", ""+searchNodeId);
			atts.addAttribute("", "", "parent", "CDATA", ""+parentNode);
			atts.addAttribute("", "", "name", "CDATA", name);
			atts.addAttribute("", "", "size", "CDATA", ""+size);
			if (dom instanceof IntDomain)
				atts.addAttribute("", "", "choice", "CDATA", ""+ intDomainToString( (IntDomain)dom));
			if (dom instanceof SetDomain) {
				atts.addAttribute("", "", "choice", "CDATA", ""+ setDomainToString( (SetDomain)dom));
			}
			hdTree.startElement("", "", "tryc", atts);
			hdTree.endElement("", "", "tryc");

		} catch (SAXException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	void generateFailcNode(int searchNodeId, int parentNode, String name, int size, Domain dom) {
		
		try {
			AttributesImpl atts = new AttributesImpl();
			atts.addAttribute("", "", "id", "CDATA", ""+searchNodeId);
			atts.addAttribute("", "", "parent", "CDATA", ""+parentNode);
			atts.addAttribute("", "", "name", "CDATA", name);
			atts.addAttribute("", "", "size", "CDATA", ""+size);
			// TODO, BUG? Why in the function above generateTrycNode, originally function filter*(dom) was called and here 
			// our toString() for dom is being called.
			atts.addAttribute("", "", "choice", "CDATA", ""+dom);
			hdTree.startElement("", "", "failc", atts);
			hdTree.endElement("", "", "failc");

		} catch (SAXException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}

	
	void generateTrycNode(int searchNodeId, int parentNode, PrimitiveConstraint c) {
		try {
			AttributesImpl atts = new AttributesImpl();
			atts.addAttribute("", "", "id", "CDATA", ""+searchNodeId);
			atts.addAttribute("", "", "parent", "CDATA", ""+parentNode);
			atts.addAttribute("", "", "choice", "CDATA", c.toString());
			hdTree.startElement("", "", "tryc", atts);
			hdTree.endElement("", "", "tryc");

		} catch (SAXException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	void generateFailcNode(int searchNodeId, int parentNode, PrimitiveConstraint c) {
		
		try {
			AttributesImpl atts = new AttributesImpl();
			atts.addAttribute("", "", "id", "CDATA", ""+searchNodeId);
			atts.addAttribute("", "", "parent", "CDATA", ""+parentNode);
			atts.addAttribute("", "", "choice", "CDATA", c.toString());
			hdTree.startElement("", "", "failc", atts);
			hdTree.endElement("", "", "failc");

		} catch (SAXException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		
	}

	
	void generateVisualizationNode(int searchNodeId, boolean tryNode) {

		int visualizerState = 1;

		try {
			AttributesImpl atts = new AttributesImpl();
			atts.addAttribute("", "", "id", "CDATA", ""+visualisationNodeId);
			atts.addAttribute("", "", "tree_node", "CDATA", ""+searchNodeId);
			hdVis.startElement("", "", "state", atts);

			if (tracedVar.size() != 0) {
				AttributesImpl visAtts = new AttributesImpl();
				visAtts.addAttribute("", "", "id", "CDATA", ""+visualizerState);
				hdVis.startElement("", "", "visualizer_state", visAtts);

				// variable visualization
				for (int i = 0; i < tracedVar.size(); i++) {

					AttributesImpl vAtts = new AttributesImpl();
					vAtts.addAttribute("", "", "index", "CDATA", ""+(int)(i+1));
					if (tracedVar.get(i) instanceof org.jacop.core.IntVar) {
						IntVar v = (IntVar)tracedVar.get(i);
						if ( v.singleton() ) { // IntVar
							vAtts.addAttribute("", "", "value", "CDATA", ""+v.value());
							hdVis.startElement("", "", "integer", vAtts);
							hdVis.endElement("", "", "integer");
						}
						else {
							vAtts.addAttribute("", "", "domain", "CDATA", intDomainToString( (IntDomain)v.dom() ));
							hdVis.startElement("", "", "dvar", vAtts);
							hdVis.endElement("", "", "dvar");
						}
					}
					else { // setVar
						SetVar v = (SetVar)tracedVar.get(i);
						if ( v.singleton() ) { // IntVar
							vAtts.addAttribute("", "", "value", "CDATA", ""+ setDomainToString((SetDomain)v.dom()));
							hdVis.startElement("", "", "sinteger", vAtts);
							hdVis.endElement("", "", "sinteger");
						}
						else {
							// TODO, BUG? Why the same thing is written to low and high attribute?
							vAtts.addAttribute("", "", "low", "CDATA", setDomainToString( (SetDomain)v.dom() ));
							vAtts.addAttribute("", "", "high", "CDATA", setDomainToString( (SetDomain)v.dom() ));
							hdVis.startElement("", "", "svar", vAtts);
							hdVis.endElement("", "", "svar");
						}
					}

					visualizerState++;
				}
				if (varIndex.get(selectedVar) != null) {
				    AttributesImpl vFocus = new AttributesImpl();
				    vFocus.addAttribute("", "", "index", "CDATA", ""+(int)(varIndex.get(selectedVar)+1));
				    vFocus.addAttribute("", "", "group", "CDATA", ""+"default");
				    if (tryNode) {
					vFocus.addAttribute("", "", "type", "CDATA", "");
					hdVis.startElement("", "", "focus", vFocus);
					hdVis.endElement("", "", "focus");
				    }
				    else {  // fail node
					vFocus.addAttribute("", "", "value", "CDATA", ""+selectedValue);
					hdVis.startElement("", "", "failed", vFocus);
					hdVis.endElement("", "", "failed");
				    }				}
				hdVis.endElement("", "", "visualizer_state");
			}

			hdVis.endElement("", "", "state");

			visualisationNodeId++;

		} catch (SAXException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	String intDomainToString(IntDomain domain) {

		StringBuffer result = new StringBuffer();

		for (IntervalEnumeration enumer = domain.intervalEnumeration(); enumer.hasMoreElements();) {
			Interval next = enumer.nextElement();
			if (next.singleton())
				result.append(next.min);
			else 
				if (next.max - next.min >= 2)
					result.append(next.min).append(" .. ").append(next.max);
				else
					// two elements interval represented as two single entries.
					result.append(next.min).append(" ").append(next.max);
			
			if (enumer.hasMoreElements())
				result.append(" ");
		}

		return result.toString();

	}

	// Remove the need for this function by incorporating it and domain type check in the function above. 
	String setDomainToString(SetDomain domain) {

		if (domain.singleton())
			return intDomainToString( domain.lub() );
		
		StringBuffer result = new StringBuffer();

		result.append("( ");
		result.append( intDomainToString(domain.glb()) ).append(" ) .. ( ");
		result.append( intDomainToString(domain.lub()) ).append(" )");

		return result.toString();

	}

	// TODO, what happens if DepthFirstSearch first evaluates x != v branch before evaluating x = v branch? 
	
	class SearchNode {
		
		Var v;
		Domain dom;
		PrimitiveConstraint c;
		int val;
		int id;	
		boolean equal = true;
		int previous;

		public String toString() {
			return "Node(" + id + ") = " + v.id + ", " + dom + ", " + val + ", " + equal;
		}
		
	}
}
