/**
 *  Fz2jacop.java 
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


package org.jacop.fz;

import org.jacop.core.FailException;

/**
 * 
 * An executable to parse and execute the flatzinc file. 
 * 
 * @author Krzysztof Kuchcinki
 *
 */

public class Fz2jacop {

    /**
     * It parses the provided file and parsing parameters followed by problem solving. 
     * 
     * @param args parameters describing the flatzinc file containing the problem to be solved as well as options for problem solving. 
     * 
     * TODO what are the conditions for different exceptions being thrown? Write little info below.
     * 
     * @throws ParseException
     * @throws TokenMgrError
     */
	
    public static void main(String[] args)  {

	// org.jacop.core.SwitchesPruningLogging.traceVar =  false;
	// org.jacop.core.SwitchesPruningLogging.traceConstraint =  false;
	// org.jacop.core.SwitchesPruningLogging.traceConsistencyCheck =  false;
	// org.jacop.core.SwitchesPruningLogging.traceQueueingConstraint =  false;
	// org.jacop.core.SwitchesPruningLogging.traceAlreadyQueuedConstraint =  false;
	// org.jacop.core.SwitchesPruningLogging.traceConstraintImposition =  false;
	// org.jacop.core.SwitchesPruningLogging.traceFailedConstraint =  false;
	// org.jacop.core.SwitchesPruningLogging.traceLevelRemoval =  false;
	// org.jacop.core.SwitchesPruningLogging.traceConstraintFailure =  false;
	// org.jacop.core.SwitchesPruningLogging.traceStoreRemoveLevel =  false;
	// org.jacop.core.SwitchesPruningLogging.traceVariableCreation =  false;
	// org.jacop.core.SwitchesPruningLogging.traceOperationsOnLevel =  false;
	// org.jacop.core.SwitchesPruningLogging.traceSearchTree =  false;

	Options opt = new Options(args);

	if (opt.getVerbose())
	    System.out.println("%% Flatzinc2JaCoP: compiling and executing " + args[args.length-1]);

	Thread tread = java.lang.Thread.currentThread();
	java.lang.management.ThreadMXBean b = java.lang.management.ManagementFactory.getThreadMXBean();
	long startCPU = b.getThreadCpuTime(tread.getId());

	Parser parser = new Parser(opt.getFile());
	parser.setOptions(opt);

	RunWhenShuttingDown t = new RunWhenShuttingDown(parser);
	if (opt.getStatistics())
	    Runtime.getRuntime().addShutdownHook(t);

	try {	    

	    parser.model();

	} catch (FailException e) {
            System.out.println("=====UNSATISFIABLE====="); // "*** Evaluation of model resulted in fail.");
	} catch (ArithmeticException e) {
	    System.err.println("%% Evaluation of model resulted in an overflow.");
	} catch (ParseException e) {
	    System.out.println("%% Parser exception "+ e);
	} catch (TokenMgrError e) {
	    System.out.println("%% Parser exception "+ e);
 	} catch (ArrayIndexOutOfBoundsException e) {
 	    System.out.println("%% JaCoP internal error. Array out of bound exception "+ e);
	    if (e.getStackTrace().length > 0)
		System.out.println ("%%\t" + e.getStackTrace()[0]);
	} catch (OutOfMemoryError e) {
	    System.out.println("%% Out of memory error; consider option -Xmx... for JVM");
	} catch (StackOverflowError e) {
	    System.out.println("%% Stack overflow exception error; consider option -Xss... for JVM");
	}

	if (opt.getStatistics()) {
	    Runtime.getRuntime().removeShutdownHook(t); 
	
	    System.out.println("\n%% Total CPU time : " + (b.getThreadCpuTime(tread.getId()) - startCPU)/(long)1e+6 + "ms");
	}

    }
}
