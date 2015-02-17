/**
 *  RunExample.java 
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


package org.jacop.examples;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;

import org.jacop.fz.Fz2jacop;

/**
 * This class executes the provided example. It also allows to specify 
 * the arguments for the executed example.
 * 
 * @author Radoslaw Szymanek
 * @version 4.2
 *
 */

public class RunExample {

	/**
	 * It executes the example as specified by the first argument. The remaining arguments
	 * will be forwarded to the executed example.
	 * 
	 * @param args name of the example and its arguments.
	 */
	public static void main(String[] args) {
		
		if (args.length == 0) {
			
			System.out.println("You can run java JaCoP examples with java command and Scala JaCoP examples with scala command");
			System.out.println("Please specify as the first argument the name of the example");
			System.out.println("All remaining arguments will be passed to the example.");
			System.out.println("The name of the example is either the class name from org.jacop.examples" + 
								" or name of .fzn file.");
		    System.exit(-1);
            
		}
		
		if (args[args.length - 1].endsWith(".fzn")) {

			Fz2jacop.main(args);
			return;
			
		}
		else
        try {
            // load the target class, and get a reference to its main method
            Class<?> [] mainArgs = new Class[1];
            mainArgs[0] = Class.forName("[Ljava.lang.String;");
            Method mainMethod = Class.forName("org.jacop.examples." + args[0]).getMethod("main", mainArgs);

            // verify that the main method is static
            if((mainMethod.getModifiers() & Modifier.STATIC) == 0){
                System.err.println("examplesloader: main method in target class is not static");
                System.exit(-1);
            }
            
            // verify that the main method returns a void
            if(mainMethod.getReturnType() != void.class){
                System.err.println("examplesloader: target class main must return void");
                System.exit(-1);
            }
            
            // we need to make a copy of our args, with the first two (which were
            // intended for the examplesloader) stripped off
            String [] processedArgs = new String[args.length-1];
            System.arraycopy(args, 1, processedArgs, 0, args.length-1);

            // call the target class main method
            Object[] actualArgs = new Object[1];
            actualArgs[0] = (Object)processedArgs;
            mainMethod.invoke(null, actualArgs);
        }
        catch(ClassNotFoundException e){
            System.err.println("exampleloader: can't find class \"" + 
                               e.getMessage() +
                               "\" when loading target class \"" + 
                               args[0]
                               +"\"");
            System.exit(-1);
        }
        catch(NoSuchMethodException e){
            System.err.println("exampleloader: no main(String[]) method found in class " + args[0]);
            //e.printStackTrace();
            System.exit(-1);
        }
        catch(IllegalAccessException e){
            System.err.println("exampleloader: error calling main method in class " + args[0]);
            //e.printStackTrace();
            System.exit(-1);
        }
        catch(InvocationTargetException e){
            System.err.println("exampleloader: error calling main method in class " + args[0]);
            //e.printStackTrace();
            System.exit(-1);
        }
        
	}
        
}
