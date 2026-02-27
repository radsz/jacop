/*
 * TraceGenerator.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.search;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.Map;
import java.util.Stack;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.sax.SAXTransformerFactory;
import javax.xml.transform.sax.TransformerHandler;
import javax.xml.transform.stream.StreamResult;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.Not;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.core.Domain;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalEnumeration;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.AttributesImpl;

/**
 * Trace generator for CPviz visualization of search trees.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
@Slf4j
public class TraceGenerator<T extends Var>
    implements SelectChoicePoint<T>, ConsistencyListener, ExitChildListener<T>, ExitListener {

  /** The file containing information about tree for CPviz format. */
  public final String treeFilename;

  /** The file containing visualisation information. */
  public final String visFilename;

  /** It specifies the list of variables that are being traced. */
  public final List<Var> tracedVar = new ArrayList<>();

  public final Map<Var, Integer> varIndex = Var.createEmptyPositioning();

  /** It stores the original select choice point method that is used by this trace wrapper. */
  final SelectChoicePoint<T> select;

  final Stack<SearchNode> searchStack = new Stack<>();
  ConsistencyListener[] consistencyListeners;
  ExitChildListener<T>[] exitChildListeners;
  ExitListener[] exitListeners;

  /** It stores information about var being selected by internal select choice point. */
  T selectedVar;

  /** It specifies information about value being selected by internal select choice point. */
  int selectedValue;

  /** An xml handler for tree file. */
  TransformerHandler hdTree;

  /** An xml handler for visualization file. */
  TransformerHandler hdVis;

  SearchNode currentSearchNode;
  int searchNodeId = 1;
  int visualisationNodeId = 1;

  private static final String SET_DOMAIN_CLASS_NAME = "org.jacop.set.core.SetDomain";
  private static final String ATTR_TYPE_CDATA = "CDATA";
  private static final String ATTR_PARENT = "parent";
  private static final String ATTR_VALUE = "value";
  private static final String ATTR_CHOICE = "choice";
  private static final String ELEMENT_FAILC = "failc";

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
  public TraceGenerator(
      Search<T> search, SelectChoicePoint<T> select, String treeFilename, String visFilename) {

    this(search, select, new Var[0], treeFilename, visFilename);
  }

  /**
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
   * It creates a CPviz trace generator around proper select choice point object.
   *
   * @param select it specifies how the select choice points are being generated.
   * @param vars it specifies variables which are being traced.
   * @param treeFilename it specifies the file name for search tree trace (default tree.xml).
   * @param visFilename it specifies the file name for variable trace (default vis.xml).
   */
  private TraceGenerator(
      SelectChoicePoint<T> select, Var[] vars, String treeFilename, String visFilename) {

    this.select = select;
    this.treeFilename = treeFilename;
    this.visFilename = visFilename;

    SearchNode rootNode = new SearchNode();
    rootNode.id = 0;
    searchStack.push(rootNode);

    for (int i = 0; i < vars.length; i++) {
      tracedVar.add(vars[i]);
      varIndex.put(vars[i], i);
    }

    prepareTreeHeader();
    prepareVizHeader();
  }

  /**
   * It creates a CPviz trace generator around proper select choice point object.
   *
   * @param search it specifies search method used for depth-first-search.
   * @param select it specifies how the select choice points are being generated.
   * @param vars it specifies variables which are being traced.
   * @param treeFilename it specifies the file name for search tree trace (default tree.xml).
   * @param visFilename it specifies the file name for variable trace (default vis.xml).
   */
  public TraceGenerator(
      Search<T> search,
      SelectChoicePoint<T> select,
      Var[] vars,
      String treeFilename,
      String visFilename) {

    this(select, vars, treeFilename, visFilename);

    if (search.getConsistencyListener() == null) {
      search.setConsistencyListener(this);
    } else {
      ConsistencyListener current = search.getConsistencyListener();
      search.setConsistencyListener(this);
      setChildrenListeners(current);
    }

    if (search.getExitChildListener() == null) {
      search.setExitChildListener(this);
    } else {
      ExitChildListener<T> current = search.getExitChildListener();
      search.setExitChildListener(this);
      setChildrenListeners(current);
    }

    if (search.getExitListener() == null) {
      search.setExitListener(this);
    } else {
      ExitListener current = search.getExitListener();
      search.setExitListener(this);
      setChildrenListeners(current);
    }
  }

  /** {@inheritDoc} */
  public T getChoiceVariable(int index) {

    selectedVar = select.getChoiceVariable(index);

    if (selectedVar != null) {

      currentSearchNode = new SearchNode();
      currentSearchNode.v = selectedVar;
      currentSearchNode.dom = selectedVar.dom().cloneLight();
    }

    return selectedVar;
  }

  /** {@inheritDoc} */
  public int getChoiceValue() {

    selectedValue = select.getChoiceValue();
    currentSearchNode.val = selectedValue;
    currentSearchNode.id = searchNodeId++;
    currentSearchNode.previous = searchStack.peek().id;

    searchStack.push(currentSearchNode);

    return selectedValue;
  }

  /** {@inheritDoc} */
  public PrimitiveConstraint getChoiceConstraint(int index) {

    PrimitiveConstraint c = select.getChoiceConstraint(index);

    if (c == null) {
      if (currentSearchNode == null) {
        currentSearchNode = new SearchNode();
      }

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

  public Map<T, Integer> getVariablesMapping() {
    return select.getVariablesMapping();
  }

  public int getIndex() {
    return select.getIndex();
  }

  /** {@inheritDoc} */
  public String toString() {
    return "";
  }

  // =================================================================
  // Metods for tracing using ConsistencyListener

  /**
   * Sets the children consistency listeners.
   *
   * @param children the array of consistency listeners to set as children
   */
  public void setChildrenListeners(ConsistencyListener[] children) {
    consistencyListeners = new ConsistencyListener[children.length];
    System.arraycopy(children, 0, consistencyListeners, 0, children.length);
  }

  /**
   * Sets a single child consistency listener.
   *
   * @param child the consistency listener to set as the sole child
   */
  public void setChildrenListeners(ConsistencyListener child) {
    consistencyListeners = new ConsistencyListener[1];
    consistencyListeners[0] = child;
  }

  /**
   * Sets the children exit child listeners.
   *
   * @param children the array of exit child listeners to set as children
   */
  @SuppressWarnings("unchecked")
  public void setChildrenListeners(ExitChildListener<T>[] children) {
    exitChildListeners = new ExitChildListener[children.length];
    System.arraycopy(children, 0, exitChildListeners, 0, children.length);
  }

  /**
   * Sets the children exit listeners.
   *
   * @param children the array of exit listeners to set as children
   */
  public void setChildrenListeners(ExitListener[] children) {
    exitListeners = new ExitListener[children.length];
    System.arraycopy(children, 0, exitListeners, 0, children.length);
  }

  /**
   * Sets a single child exit child listener.
   *
   * @param child the exit child listener to set as the sole child
   */
  @SuppressWarnings("unchecked")
  public void setChildrenListeners(ExitChildListener<T> child) {
    exitChildListeners = new ExitChildListener[1];
    exitChildListeners[0] = child;
  }

  /**
   * Sets a single child exit listener.
   *
   * @param child the exit listener to set as the sole child
   */
  public void setChildrenListeners(ExitListener child) {
    exitListeners = new ExitListener[1];
    exitListeners[0] = child;
  }

  /** {@inheritDoc} */
  public boolean executeAfterConsistency(boolean consistent) {

    if (consistencyListeners != null) {
      boolean code = false;
      for (ConsistencyListener consistencyListener : consistencyListeners) {
        code |= consistencyListener.executeAfterConsistency(consistent);
      }
      consistent = code;
    }

    SearchNode sn = searchStack.peek();
    if (sn.id != 0) {
      if (!consistent) {
        generateFailTrace(sn);
        generateVisualizationNode(currentSearchNode.id, false);
      } else {
        generateTryTrace(sn);
        generateVisualizationNode(currentSearchNode.id, true);
      }
    }

    return consistent;
  }

  private void generateFailTrace(SearchNode sn) {
    if (sn.c == null) {
      if (sn.equal) {
        generateFailNode(sn.id, sn.previous, sn.v.id(), sn.v.dom().getSize(), sn.val);
      } else {
        generateFailcNode(sn.id, sn.previous, sn.v.id(), sn.dom.getSize(), sn.dom);
      }
    } else if (sn.equal) {
      generateFailcNode(sn.id, sn.previous, sn.c);
    } else {
      generateFailcNode(sn.id, sn.previous, new Not(sn.c));
    }
  }

  private void generateTryTrace(SearchNode sn) {
    if (sn.c == null) {
      if (sn.equal) {
        generateTryNode(sn.id, sn.previous, sn.v.id(), sn.v.dom().getSize(), sn.val);
      } else {
        generateTrycNode(sn.id, sn.previous, sn.v.id(), sn.dom.getSize(), sn.dom);
      }
    } else if (sn.equal) {
      generateTrycNode(sn.id, sn.previous, sn.c);
    } else {
      generateTrycNode(sn.id, sn.previous, new Not(sn.c));
    }
  }

  // =================================================================
  // Metods for tracing using ExitChildListener

  /** {@inheritDoc} */
  public boolean leftChild(T v, int value, boolean status) {

    boolean returnCode = applyExitChildListenersLeftChild(v, value, status);

    currentSearchNode = searchStack.pop();
    SearchNode previousSearchNode = currentSearchNode;

    if (!status && returnCode) {
      pushSearchNodeAfterLeftFail(v, value, previousSearchNode);
    }

    return returnCode;
  }

  private boolean applyExitChildListenersLeftChild(T v, int value, boolean status) {
    if (exitChildListeners == null) {
      return true;
    }
    boolean code = false;
    for (ExitChildListener<T> exitChildListener : exitChildListeners) {
      code |= exitChildListener.leftChild(v, value, status);
    }
    return code;
  }

  private void pushSearchNodeAfterLeftFail(T v, int value, SearchNode previousSearchNode) {
    currentSearchNode = new SearchNode();
    currentSearchNode.v = v;
    currentSearchNode.dom = subtractValueFromDomain(previousSearchNode.dom, value);
    currentSearchNode.val = value;
    currentSearchNode.id = searchNodeId++;
    currentSearchNode.equal = false;
    currentSearchNode.previous = searchStack.peek().id;
    searchStack.push(currentSearchNode);
  }

  private Domain subtractValueFromDomain(Domain dom, int value) {
    if (dom instanceof IntDomain domain) {
      return domain.subtract(value);
    }
    try {
      Class<?> setDomainClass = Class.forName(SET_DOMAIN_CLASS_NAME);
      if (setDomainClass.isInstance(dom)) {
        java.lang.reflect.Method subtractMethod =
            setDomainClass.getMethod("subtract", int.class, int.class);
        return (Domain) subtractMethod.invoke(dom, value, value);
      }
    } catch (Exception _) {
      // SetDomain not available - skip this operation
    }
    return null;
  }

  /** {@inheritDoc} */
  public boolean leftChild(PrimitiveConstraint choice, boolean status) {

    boolean returnCode = true;

    if (exitChildListeners != null) {
      boolean code = false;
      for (ExitChildListener<T> exitChildListener : exitChildListeners) {
        code |= exitChildListener.leftChild(choice, status);
      }
      returnCode = code;
    }

    currentSearchNode = searchStack.pop();

    if (!status && returnCode) {

      currentSearchNode = new SearchNode();

      currentSearchNode.id = searchNodeId++;
      currentSearchNode.equal = false;
      currentSearchNode.c = choice;
      currentSearchNode.previous = searchStack.peek().id;

      searchStack.push(currentSearchNode);
    }

    return returnCode;
  }

  /** {@inheritDoc} */
  public void rightChild(T v, int value, boolean status) {

    currentSearchNode = searchStack.pop();
  }

  /** {@inheritDoc} */
  public void rightChild(PrimitiveConstraint choice, boolean status) {

    currentSearchNode = searchStack.pop();
  }

  // =================================================================
  // Metods for tracing using ExitListener

  /** {@inheritDoc} */
  public void executedAtExit(Store store, int solutionsNo) {

    try {

      hdTree.endElement("", "", "tree");
      hdTree.endDocument();

      hdVis.endElement("", "", "visualization");
      hdVis.endDocument();

    } catch (SAXException e) {
      log.error("Failed to close XML documents", e);
    }
  }

  // Methods to prepare xml files used by visualization tools.

  void prepareTreeHeader() {

    OutputStreamWriter printWriter;

    try {
      printWriter =
          new OutputStreamWriter(
              new FileOutputStream(treeFilename), StandardCharsets.UTF_8.newEncoder());
    } catch (FileNotFoundException e) {
      log.error("Failed to open tree output file {}", treeFilename, e);
      printWriter = new OutputStreamWriter(System.out, StandardCharsets.UTF_8.newEncoder());
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
      atts.addAttribute("", "", "version", ATTR_TYPE_CDATA, "1.0");
      atts.addAttribute(
          "", "", "xmln:xsi", ATTR_TYPE_CDATA, "http://www.w3.org/2001/XMLSchema-instance");
      atts.addAttribute("", "", "xsi:noNamespaceSchemaLocation", ATTR_TYPE_CDATA, "tree.xsd");

      String ourText = " Generated by JaCoP solver; " + getDateTime() + " ";
      char[] comm = ourText.toCharArray();
      hdTree.comment(comm, 0, comm.length);

      hdTree.startElement("", "", "tree", atts);

      atts = new AttributesImpl();
      atts.addAttribute("", "", "id", ATTR_TYPE_CDATA, "0");
      hdTree.startElement("", "", "root", atts);
      hdTree.endElement("", "", "root");

    } catch (TransformerConfigurationException | SAXException e) {
      log.error("Failed to configure XML transformer for tree", e);
    }
  }

  void prepareVizHeader() {

    OutputStreamWriter printWriter;

    try {
      printWriter =
          new OutputStreamWriter(
              new FileOutputStream(visFilename), StandardCharsets.UTF_8.newEncoder());
    } catch (FileNotFoundException e) {
      log.error("Failed to open visualization output file {}", visFilename, e);
      printWriter = new OutputStreamWriter(System.out, StandardCharsets.UTF_8.newEncoder());
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
      atts.addAttribute("", "", "version", ATTR_TYPE_CDATA, "1.0");
      atts.addAttribute(
          "", "", "xmlns:xsi", ATTR_TYPE_CDATA, "http://www.w3.org/2001/XMLSchema-instance");
      atts.addAttribute(
          "", "", "xsi:noNamespaceSchemaLocation", ATTR_TYPE_CDATA, "visualization.xsd");

      String ourText = " Generated by JaCoP solver; " + getDateTime() + " ";
      char[] comm = ourText.toCharArray();
      hdVis.comment(comm, 0, comm.length);

      hdVis.startElement("", "", "visualization", atts);

      // visualizer
      if (!tracedVar.isEmpty()) {
        AttributesImpl visAtt = new AttributesImpl();
        visAtt.addAttribute("", "", "id", ATTR_TYPE_CDATA, "1");
        visAtt.addAttribute("", "", "type", ATTR_TYPE_CDATA, "vector");
        visAtt.addAttribute("", "", "display", ATTR_TYPE_CDATA, "expanded");
        visAtt.addAttribute("", "", "group", ATTR_TYPE_CDATA, "default");
        visAtt.addAttribute("", "", "x", ATTR_TYPE_CDATA, "0");
        visAtt.addAttribute("", "", "y", ATTR_TYPE_CDATA, "0");

        int minV = minValue(tracedVar);
        int maxV = maxValue(tracedVar);
        visAtt.addAttribute("", "", "width", ATTR_TYPE_CDATA, "" + tracedVar.size());
        visAtt.addAttribute("", "", "height", ATTR_TYPE_CDATA, "" + (maxV - minV + 1));

        visAtt.addAttribute("", "", "min", ATTR_TYPE_CDATA, "" + minV);
        visAtt.addAttribute("", "", "max", ATTR_TYPE_CDATA, "" + maxV);

        hdVis.startElement("", "", "visualizer", visAtt);
        hdVis.endElement("", "", "visualizer");
      }

      generateVisualizationNode(0, true);

    } catch (TransformerConfigurationException | SAXException e) {
      log.error("Failed to configure XML transformer for visualization", e);
    }
  }

  /**
   * Adds a variable to the list of traced variables.
   *
   * @param v the variable to add to the trace
   */
  public void addTracedVar(Var v) {
    tracedVar.add(v);
  }

  private int minValue(List<Var> vars) {
    int min = IntDomain.MAX_INT;
    if (vars.getFirst() instanceof IntVar) {
      for (Var v : vars) {
        min = Math.min(min, ((IntVar) v).min());
      }
    }

    return min;
  }

  private int maxValue(List<Var> vars) {
    int max = IntDomain.MIN_INT;
    if (vars.getFirst() instanceof IntVar) {
      for (Var v : vars) {
        max = Math.max(max, ((IntVar) v).max());
      }
    }

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
      atts.addAttribute("", "", "id", ATTR_TYPE_CDATA, "" + searchNodeId);
      hdTree.startElement("", "", "succ", atts);
      hdTree.endElement("", "", "succ");

    } catch (SAXException e) {
      log.error("Failed to generate success XML node", e);
    }
  }

  void generateTryNode(int searchNodeId, int parentNode, String name, int size, int value) {
    try {
      AttributesImpl atts = new AttributesImpl();
      atts.addAttribute("", "", "id", ATTR_TYPE_CDATA, "" + searchNodeId);
      atts.addAttribute("", "", ATTR_PARENT, ATTR_TYPE_CDATA, "" + parentNode);
      atts.addAttribute("", "", "name", ATTR_TYPE_CDATA, name);
      atts.addAttribute("", "", "size", ATTR_TYPE_CDATA, "" + size);
      atts.addAttribute("", "", ATTR_VALUE, ATTR_TYPE_CDATA, "" + value);
      hdTree.startElement("", "", "try", atts);
      hdTree.endElement("", "", "try");

    } catch (SAXException e) {
      log.error("Failed to generate try XML node", e);
    }
  }

  void generateFailNode(int searchNodeId, int parentNode, String name, int size, int value) {
    try {
      AttributesImpl atts = new AttributesImpl();
      atts.addAttribute("", "", "id", ATTR_TYPE_CDATA, "" + searchNodeId);
      atts.addAttribute("", "", ATTR_PARENT, ATTR_TYPE_CDATA, "" + parentNode);
      atts.addAttribute("", "", "name", ATTR_TYPE_CDATA, name);
      atts.addAttribute("", "", "size", ATTR_TYPE_CDATA, "" + size);
      atts.addAttribute("", "", ATTR_VALUE, ATTR_TYPE_CDATA, "" + value);
      hdTree.startElement("", "", "fail", atts);
      hdTree.endElement("", "", "fail");

    } catch (SAXException e) {
      log.error("Failed to generate fail XML node", e);
    }
  }

  void generateTrycNode(int searchNodeId, int parentNode, String name, int size, Domain dom) {
    try {
      AttributesImpl atts = new AttributesImpl();
      atts.addAttribute("", "", "id", ATTR_TYPE_CDATA, "" + searchNodeId);
      atts.addAttribute("", "", ATTR_PARENT, ATTR_TYPE_CDATA, "" + parentNode);
      atts.addAttribute("", "", "name", ATTR_TYPE_CDATA, name);
      atts.addAttribute("", "", "size", ATTR_TYPE_CDATA, "" + size);
      if (dom instanceof IntDomain domain) {
        atts.addAttribute("", "", ATTR_CHOICE, ATTR_TYPE_CDATA, intDomainToString(domain));
      } else {
        // Handle SetDomain using reflection to avoid import
        try {
          Class<?> setDomainClass = Class.forName(SET_DOMAIN_CLASS_NAME);
          if (setDomainClass.isInstance(dom)) {
            String domainStr = setDomainToStringReflective(dom);
            atts.addAttribute("", "", ATTR_CHOICE, ATTR_TYPE_CDATA, domainStr);
          }
        } catch (Exception _) {
          // SetDomain not available - skip this operation
        }
      }
      hdTree.startElement("", "", "tryc", atts);
      hdTree.endElement("", "", "tryc");

    } catch (SAXException e) {
      log.error("Failed to generate tryc XML node", e);
    }
  }

  void generateTrycNode(int searchNodeId, int parentNode, PrimitiveConstraint c) {
    try {
      AttributesImpl atts = new AttributesImpl();
      atts.addAttribute("", "", "id", ATTR_TYPE_CDATA, "" + searchNodeId);
      atts.addAttribute("", "", ATTR_PARENT, ATTR_TYPE_CDATA, "" + parentNode);
      atts.addAttribute("", "", ATTR_CHOICE, ATTR_TYPE_CDATA, c.toString());
      hdTree.startElement("", "", "tryc", atts);
      hdTree.endElement("", "", "tryc");

    } catch (SAXException e) {
      log.error("Failed to generate tryc XML node", e);
    }
  }

  void generateFailcNode(int searchNodeId, int parentNode, String name, int size, Domain dom) {

    try {
      AttributesImpl atts = new AttributesImpl();
      atts.addAttribute("", "", "id", ATTR_TYPE_CDATA, "" + searchNodeId);
      atts.addAttribute("", "", ATTR_PARENT, ATTR_TYPE_CDATA, "" + parentNode);
      atts.addAttribute("", "", "name", ATTR_TYPE_CDATA, name);
      atts.addAttribute("", "", "size", ATTR_TYPE_CDATA, "" + size);
      atts.addAttribute("", "", ATTR_CHOICE, ATTR_TYPE_CDATA, "" + dom);
      hdTree.startElement("", "", ELEMENT_FAILC, atts);
      hdTree.endElement("", "", ELEMENT_FAILC);

    } catch (SAXException e) {
      log.error("Failed to generate failc XML node", e);
    }
  }

  void generateFailcNode(int searchNodeId, int parentNode, PrimitiveConstraint c) {

    try {
      AttributesImpl atts = new AttributesImpl();
      atts.addAttribute("", "", "id", ATTR_TYPE_CDATA, "" + searchNodeId);
      atts.addAttribute("", "", ATTR_PARENT, ATTR_TYPE_CDATA, "" + parentNode);
      atts.addAttribute("", "", ATTR_CHOICE, ATTR_TYPE_CDATA, c.toString());
      hdTree.startElement("", "", ELEMENT_FAILC, atts);
      hdTree.endElement("", "", ELEMENT_FAILC);

    } catch (SAXException e) {
      log.error("Failed to generate failc XML node", e);
    }
  }

  void generateVisualizationNode(int searchNodeId, boolean tryNode) {

    int visualizerState = 1;

    try {
      AttributesImpl atts = new AttributesImpl();
      atts.addAttribute("", "", "id", ATTR_TYPE_CDATA, "" + visualisationNodeId);
      atts.addAttribute("", "", "tree_node", ATTR_TYPE_CDATA, "" + searchNodeId);
      hdVis.startElement("", "", "state", atts);

      if (!tracedVar.isEmpty()) {
        AttributesImpl visAtts = new AttributesImpl();
        visAtts.addAttribute("", "", "id", ATTR_TYPE_CDATA, "" + visualizerState);
        hdVis.startElement("", "", "visualizer_state", visAtts);

        for (int i = 0; i < tracedVar.size(); i++) {
          visualizerState = writeVariableVisualization(visualizerState, i, tracedVar.get(i));
        }
        writeFocusElement(tryNode);
        hdVis.endElement("", "", "visualizer_state");
      }

      hdVis.endElement("", "", "state");
      visualisationNodeId++;

    } catch (SAXException e) {
      log.error("Failed to generate visualization XML node", e);
    }
  }

  private int writeVariableVisualization(int visualizerState, int index, Var var)
      throws SAXException {
    AttributesImpl vAtts = new AttributesImpl();
    vAtts.addAttribute("", "", "index", ATTR_TYPE_CDATA, "" + (index + 1));
    if (var instanceof IntVar v) {
      writeIntVarVisualization(vAtts, v);
    } else {
      writeNonIntVarVisualization(vAtts, var);
    }
    return visualizerState + 1;
  }

  private void writeIntVarVisualization(AttributesImpl vAtts, IntVar v) throws SAXException {
    if (v.singleton()) {
      vAtts.addAttribute("", "", ATTR_VALUE, ATTR_TYPE_CDATA, "" + v.value());
      hdVis.startElement("", "", "integer", vAtts);
      hdVis.endElement("", "", "integer");
    } else {
      vAtts.addAttribute("", "", "domain", ATTR_TYPE_CDATA, intDomainToString(v.dom()));
      hdVis.startElement("", "", "dvar", vAtts);
      hdVis.endElement("", "", "dvar");
    }
  }

  private void writeNonIntVarVisualization(AttributesImpl vAtts, Var v) throws SAXException {
    DomainOperationHandler domainHandler = SearchHandlerRegistry.getInstance().findDomainHandler(v);
    if (domainHandler == null) {
      return;
    }
    String domainStr = domainHandler.getDomainString(v);
    boolean isSingleton = invokeSingletonReflective(v);
    if (isSingleton) {
      vAtts.addAttribute("", "", ATTR_VALUE, ATTR_TYPE_CDATA, domainStr);
      hdVis.startElement("", "", "sinteger", vAtts);
      hdVis.endElement("", "", "sinteger");
    } else {
      vAtts.addAttribute("", "", "low", ATTR_TYPE_CDATA, domainStr);
      vAtts.addAttribute("", "", "high", ATTR_TYPE_CDATA, domainStr);
      hdVis.startElement("", "", "svar", vAtts);
      hdVis.endElement("", "", "svar");
    }
  }

  private boolean invokeSingletonReflective(Var v) {
    try {
      java.lang.reflect.Method singletonMethod = v.getClass().getMethod("singleton");
      return (Boolean) singletonMethod.invoke(v);
    } catch (Exception _) {
      return false;
    }
  }

  private void writeFocusElement(boolean tryNode) throws SAXException {
    if (varIndex.get(selectedVar) == null) {
      return;
    }
    AttributesImpl vFocus = new AttributesImpl();
    vFocus.addAttribute("", "", "index", ATTR_TYPE_CDATA, "" + (varIndex.get(selectedVar) + 1));
    vFocus.addAttribute("", "", "group", ATTR_TYPE_CDATA, "default");
    if (tryNode) {
      vFocus.addAttribute("", "", "type", ATTR_TYPE_CDATA, "");
      hdVis.startElement("", "", "focus", vFocus);
      hdVis.endElement("", "", "focus");
    } else {
      vFocus.addAttribute("", "", ATTR_VALUE, ATTR_TYPE_CDATA, "" + selectedValue);
      hdVis.startElement("", "", "failed", vFocus);
      hdVis.endElement("", "", "failed");
    }
  }

  String intDomainToString(IntDomain domain) {

    StringBuilder result = new StringBuilder();

    for (IntervalEnumeration enumer = domain.intervalEnumeration(); enumer.hasMoreElements(); ) {
      Interval next = enumer.nextElement();
      if (next.singleton()) {
        result.append(next.min());
      } else if (next.max() - next.min() >= 2) {
        result.append(next.min()).append(" .. ").append(next.max());
      } else {
        // two elements interval represented as two single entries.
        result.append(next.min()).append(" ").append(next.max());
      }

      if (enumer.hasMoreElements()) {
        result.append(" ");
      }
    }

    return result.toString();
  }

  // Remove the need for this function by incorporating it and domain type check in the function
  // above.
  // Uses reflection to avoid SetDomain import
  String setDomainToStringReflective(Domain domain) {
    try {
      Class<?> setDomainClass = Class.forName(SET_DOMAIN_CLASS_NAME);
      java.lang.reflect.Method singletonMethod = setDomainClass.getMethod("singleton");
      java.lang.reflect.Method lubMethod = setDomainClass.getMethod("lub");
      java.lang.reflect.Method glbMethod = setDomainClass.getMethod("glb");

      boolean isSingleton = (Boolean) singletonMethod.invoke(domain);
      if (isSingleton) {
        IntDomain lub = (IntDomain) lubMethod.invoke(domain);
        return intDomainToString(lub);
      }

      StringBuilder result = new StringBuilder();
      IntDomain glb = (IntDomain) glbMethod.invoke(domain);
      IntDomain lub = (IntDomain) lubMethod.invoke(domain);
      result.append("( ");
      result.append(intDomainToString(glb)).append(" ) .. ( ");
      result.append(intDomainToString(lub)).append(" )");
      return result.toString();
    } catch (Exception _) {
      // SetDomain not available - return empty string
      return "";
    }
  }

  static class SearchNode {

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
