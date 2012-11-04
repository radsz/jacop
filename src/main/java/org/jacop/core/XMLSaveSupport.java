package org.jacop.core;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.lang.reflect.Array;
import java.lang.reflect.Constructor;
import java.lang.reflect.Field;
import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;

import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.sax.SAXTransformerFactory;
import javax.xml.transform.sax.TransformerHandler;
import javax.xml.transform.stream.StreamResult;

import org.jacop.constraints.Constraint;
import org.jacop.constraints.geost.GeostObject;
import org.jacop.constraints.regular.Regular;
import org.jacop.util.fsm.FSMState;
import org.xml.sax.SAXException;
import org.xml.sax.helpers.AttributesImpl;

/**
 * 
 * @author Radoslaw Szymanek
 * 
 * 1. Make sure all saved attributes are public. 
 * 2. Make sure order between xmlAttributes and one constructor is the same. 
 * 3. Make sure that id, or numberId is set properly after running constructor. 
 * 4. Make sure that all constraints/variables have attribute numberId;
 * 5. Make sure that all objects have attribute id. 
 * 6. Remove old code for getting XML functionality.
 * 7. Make sure that the ids are proper (unique, and do not contain unusual characters like space). 
 * I. More complex objects to XML need to use special functions to save and load XML. 
 * Ia. void toXML(TransformerHandler) to save to XML the object which implements the function.  It compleemnts xmlAttributes.
 * Ib. DefaultHandler getXMLReader(), returns an object capable of returning the proper object from reading XML.  
 * 9. For variables it is checked if Store argument must be added to constructor. Only as the first one.
 * 10. Save constraints, variables, search definition. 
 */

public class XMLSaveSupport {

	private static final String toXMLfunction = "toXML";

	private static final String elementXMLName = "el";

	private static final String arrayXMLName = "array";
	
	public XMLSaveSupport() {
				
		repositorySet.put(FSMState.class, new HashSet<Object>());
		repositorySet.put(GeostObject.class, new HashSet<Object>());
		
		HashSet<Class> regularClear = new HashSet<Class>();
		regularClear.add(FSMState.class);
		repositoryClear.put(Regular.class, regularClear);
	}

	HashMap<String, Var> varMap = new HashMap<String, Var>();

	public static Class classVariable;

	public static HashMap<Class, HashMap<String, ?>> repository = new HashMap<Class, HashMap<String, ?>>();

	public static HashMap<Class, HashSet<Object>> repositorySet = new HashMap<Class, HashSet<Object>>();

	public static HashMap<Class, HashSet<Class>> repositoryClear = new HashMap<Class, HashSet<Class>>();

	private static char[] space = " ".toCharArray();

	public static void save(Store store, String filename) {
		
		PrintWriter printWriter;

		if (filename == null)
			filename = "test.xml";

		try {
			printWriter = new PrintWriter(new FileOutputStream(filename));
		} catch (FileNotFoundException e) {
			e.printStackTrace();
			printWriter = new PrintWriter( new StringWriter() );
		}
		
		StreamResult streamResult = new StreamResult(printWriter);
		SAXTransformerFactory tf = (SAXTransformerFactory) SAXTransformerFactory.newInstance();

		try {

			classVariable = Class.forName("JaCoP.core.Var");

			TransformerHandler hd = tf.newTransformerHandler();
			
			Transformer serializer = hd.getTransformer();
			serializer.setOutputProperty(OutputKeys.ENCODING, "ISO-8859-1");
			serializer.setOutputProperty(OutputKeys.INDENT, "yes");
			serializer.setOutputProperty("{http://xml.apache.org/xslt}indent-amount", "4");
			
			hd.setResult(streamResult);

			hd.startDocument();

			AttributesImpl atts = new AttributesImpl();
			hd.startElement("", "", "instance", atts);

			// TODO, what about boolean variables? 
			HashMap<String, Constraint> constraints = new HashMap<String, Constraint>();

			Object[] sortedNames = store.variablesHashMap.keySet().toArray(); 
			Arrays.sort(sortedNames);
			
			for (Object name : sortedNames) {
				Var var = store.variablesHashMap.get(name);
				if (var != null) {
					save(hd, var, null);
					for (int i = 0; i < var.dom().modelConstraintsToEvaluate.length; i++)
						for (int j = 0; j < var.dom().modelConstraintsToEvaluate[i]; j++) {
							Constraint olderConstraint = constraints.put( var.dom().modelConstraints[i][j].id(), 
											 							  var.dom().modelConstraints[i][j] );
							assert (olderConstraint == null || olderConstraint == var.dom().modelConstraints[i][j]) : 
								"Constraint id(s) are not unique.";
							
						}
				}
			}

			sortedNames = constraints.keySet().toArray();
			Arrays.sort(sortedNames);
			
			for (Object name : sortedNames)
				save(hd, constraints.get(name), null);
			
			hd.endElement("", "", "instance");

			hd.endDocument();

		} catch (TransformerConfigurationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (SAXException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (ClassNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} 

		
	}
	
	// Invariants - assumptions 
	// Only one load xml function. 
	public static void save(TransformerHandler handler, Object a, AttributesImpl nestedAtts) {

		try {

			Class<?> c = a.getClass();
			
			String elementName = elementXMLName;
			
			if (a instanceof Constraint)
				elementName = "constraint";
			
			if (a instanceof Var)
				elementName = "variable";
			
			if (a instanceof IntDomain)
				elementName = "domain";
	
			if (repositoryClear.get(c) != null) {
				for (Class<?> classToClear : repositoryClear.get(c)) {
					repositorySet.get(classToClear).clear();
				}
			}
			
			boolean saveOnlyReference = false;

			if (repositorySet.get(c) != null) {
				if (repositorySet.get(c).contains(a))
					saveOnlyReference = true;
				else {
					repositorySet.get(c).add(a);
				}
			}
			
		//	assert (elementName != null);

			AttributesImpl atts;
			
			if (nestedAtts == null) 
				atts = new AttributesImpl();
			else
				atts = new AttributesImpl( nestedAtts );
			
			// class attribute
			// atts.addAttribute("", "", "class", "CDATA", c.getCanonicalName());
			atts.addAttribute("", "", "class", "CDATA", c.getSimpleName());

			boolean idFound = false;
			// id attribute
			try {
				Object objectId = c.getField("id").get(a);
				if (objectId != null) {
					// Id was explicity specified.
					atts.addAttribute("", "", "id", "CDATA", objectId.toString() );
					idFound = true;
				}
				else {
					// Id is based on number. 
					Integer no = (Integer) c.getField("numberId").get(a);
					atts.addAttribute("", "", "no", "CDATA", no.toString() );
					idFound = true;
				}
			}
			catch(NoSuchFieldException ex) {
				// Saving an element withouth id.
			}			
			
			if (!idFound) {

				// id attribute
				try {
					Object objectId = c.getField("no").get(a);
					if (objectId != null) {
						// Id is based on number. 
						Integer no = (Integer) c.getField("no").get(a);
						atts.addAttribute("", "", "no", "CDATA", no.toString() );
						idFound = true;
					}
				}
				catch(NoSuchFieldException ex) {
					// Saving an element withouth id.
					assert (saveOnlyReference == false) : "Required to save only reference but no unique id provided";
				}			
				
			}
			
			if (saveOnlyReference) {
				handler.startElement("", "", elementName, atts);
				handler.endElement("", "", elementName);
				return;
			}
				
		//	assert (objectId != null) : "Object " + a + " does not have a id.";

			String[] names;
			try {
				names = (String[]) c.getDeclaredField("xmlAttributes").get(null);
			}
			catch(NoSuchFieldException ex) {
				names = new String[0];
			//	assert (false) : "No xmlAttributes defined.";
			}
			catch(NullPointerException ex) {
				names = new String[0];
			//	assert (false) : "No xmlAttributes defined.";				
			}
			
			// for (String xmlAttribute : names)
			//	System.out.println(xmlAttribute);
			
			Class<?>[] types;
			boolean[] handled = new boolean[names.length];
			Constructor constructorForXML = null;

			types = new Class<?>[names.length];
			for (int i = 0; i < names.length; i++) {
				try {
					types[i] = c.getField(names[i]).getType();
				}
				catch(java.lang.NoSuchFieldException ex) {
					types[i] = c.getMethod(names[i], null).getReturnType();
				}
			}
			
			constructorForXML = c.getConstructor(types);
			
			if (constructorForXML != null) {
				Object [] argumentsFromXML = new Object[types.length];

				for (int i = 0; i < types.length; i++) {

					if (names[i].equals("id"))
						continue;
					
					Object ithArgument = null;

					try {
						ithArgument = c.getMethod(names[i], null).invoke(a, null);
					}
					catch(NoSuchMethodException ex) {};

					String functionName = "get" + names[i].substring(0, 1).toUpperCase() + names[i].substring(1);

					if (ithArgument == null) {

						try {
							ithArgument = c.getMethod(functionName, null).invoke(a, null);
						}
						catch(NoSuchMethodException ex) {};

					}

					if (ithArgument == null) {

						try { 
							Field ithField = c.getField(names[i]);
							if (ithField != null)
								ithArgument = ithField.get(a);
						}
						catch(NoSuchFieldException ex) {
							assert (false) : "xmlAttributes mismatch at " + i + "-th element. No attribute " + names[i] 
							                                                                                         + " found. " + " No function " + functionName + "() found." 
							                                                                                         + "No function " + names[i] + "() found.";
						};

					}

					argumentsFromXML[i] = ithArgument;

					// if (! ithArgument.getClass().equals(Store.class))
					//	System.out.println( ithArgument );

				}

				for (int i = 0; i < types.length; i++) {
					
					if (argumentsFromXML[i] == null)
						continue;
					
					// Adding to attributes of the element.
					// if variable 
					if (classVariable.isAssignableFrom(types[i])) {
						
						handled[i] = true;

						String variableId = null;
						try {
							variableId = (String) classVariable.getMethod("id", null).invoke(argumentsFromXML[i], null);
						}
						catch(NoSuchMethodException ex) {};

						if (variableId == null)
							variableId = (String) c.getDeclaredField("id").get(argumentsFromXML[i]);

						atts.addAttribute("", "", names[i], "CDATA", variableId);
					}

					
					if (types[i].isPrimitive() ) {
						
						handled[i] = true;

						Object value = null;

						try {
							value = c.getMethod(names[i], null).invoke(a, null);
						}
						catch(NoSuchMethodException ex) {};

						String functionName = "get" + names[i].substring(0, 1).toUpperCase() + names[i].substring(1);

						if (value == null) {

							try {
								value = c.getMethod(functionName, null).invoke(a, null);
							}
							catch(NoSuchMethodException ex) {};

						}

						if (value == null) {

							try { 
								Field ithField = c.getField(names[i]);
								if (ithField != null)
									value = ithField.get(a);
							}
							catch(NoSuchFieldException ex) {
								assert (false) : "xmlAttributes mismatch at " + i + "-th element. No attribute " + names[i] 
								                                                     + " found. " + " No function " + functionName + "() found." 
								                                                     + "No function " + names[i] + "() found.";
							};

						}

						atts.addAttribute("", "", names[i], "CDATA", value.toString() );
					}					
					
				}

				handler.startElement("", "", elementName, atts);

				for (int i = 0; i < types.length; i++) {

					if (argumentsFromXML[i] == null)
						continue;

					if (Store.class.isAssignableFrom( argumentsFromXML[i].getClass() ) )
						continue;

					if (handled[i])
						continue;
					
					// array of something. 
					// if (types[i].isArray() || types[i].equals(Collection.class)) {
					if (types[i].isArray() || Collection.class.isAssignableFrom(types[i])) {

						AttributesImpl arrayAtts = new AttributesImpl();

						// class attribute
						arrayAtts.addAttribute("", "", "id", "CDATA", names[i]);
						if (types[i].isArray())
							arrayAtts.addAttribute("", "", "size", "CDATA", String.valueOf( Array.getLength( argumentsFromXML[i]) ));
						else 
							arrayAtts.addAttribute("", "", "size", "CDATA", String.valueOf( ((Collection)argumentsFromXML[i]).size() ) );

						handler.startElement("", "", arrayXMLName, arrayAtts);
						saveArray(handler, argumentsFromXML[i]);
						handler.endElement("", "", arrayXMLName);

					} else {

						AttributesImpl internalAtts = new AttributesImpl();

						// class attribute
						internalAtts.addAttribute("", "", "id", "CDATA", names[i]);
						handler.startElement("", "", elementXMLName, internalAtts);
						save(handler, argumentsFromXML[i], null);
						handler.endElement("", "", elementXMLName);
						
					}

					
				}
				
				// Search for toXML(TransformerHandler) if it exists then execute it. 
				
				try {
					c.getMethod(toXMLfunction, TransformerHandler.class).invoke(a, handler);
				}
				catch(NoSuchMethodException ex) {};
				
				handler.endElement("", "", elementName);


			}


		}
		catch (Throwable e) {
			System.err.println(e);
		}
	}

	private static String id(Object object) throws IllegalArgumentException, 
													SecurityException, 
													IllegalAccessException, 
													NoSuchFieldException, 
													InvocationTargetException {

		Class c = object.getClass();
		
		String id = null;
		try {
			id = (String) c.getMethod("id", null).invoke(object, null);
		}
		catch(NoSuchMethodException ex) {};

		if (id == null)
			id = (String) c.getDeclaredField("id").get(object);

		return id;
		
	}

	private static void saveArray(TransformerHandler handler, Object object) throws IllegalArgumentException, SecurityException, IllegalAccessException, NoSuchFieldException, InvocationTargetException, SAXException {
		// TODO Auto-generated method stub

		if ( object.getClass().isArray() ) {
			//	Array array = (Array) object;
			int length = Array.getLength(object);
			Class<?> arrayClass = object.getClass();
			Class<?> componentClass = arrayClass.getComponentType();

			if (classVariable.isAssignableFrom(componentClass)) {
				for (int i = 0; i < length; i++) {
					Object ithObject = Array.get(object, i);

					String id = id(ithObject);
					handler.characters(id.toCharArray(), 0, id.length());
					handler.characters(space, 0, 1);

				}
				return;
			}

			if (componentClass.equals(int.class)) {

				for (int i = 0; i < length; i++) {
					Integer value = Array.getInt(object, i);
					String characters = value.toString();
					handler.characters(characters.toCharArray(), 0, characters.length());
					handler.characters(space, 0, 1);

				}
				return;
			}

			for (int i = 0; i < length; i++) {
				Object ithObject = Array.get(object, i);

				AttributesImpl internalAtts = new AttributesImpl();

				// class attribute
				internalAtts.addAttribute("", "", "i", "CDATA", String.valueOf(i));
				save(handler, ithObject, internalAtts);

			}

		} else {
			// Collection.
			Collection collection = (Collection) object;
			Iterator iterator = collection.iterator();

			for (int i = 0; iterator.hasNext(); i++) {
				Object ithObject = iterator.next();

				AttributesImpl internalAtts = new AttributesImpl();

				// class attribute
				internalAtts.addAttribute("", "", "i", "CDATA", String.valueOf(i));
				save(handler, ithObject, internalAtts);

			}

				
		}
		
	}
	
	
}

