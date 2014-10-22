/**
 *  Options.java 
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

import java.io.FileInputStream;
import org.jacop.floats.core.FloatDomain;

/**
 * 
 * It parses the options provided to flatzinc parser/executable. It contains
 * information about all options used for a given flatzinc file. 
 * 
 * @author Krzysztof Kuchcinski
 *
 */
public class Options {

    String[] argument;
	
    FileInputStream file;

    String fileName;
	
    boolean all = false, verbose = false;
	
    boolean statistics = false;
	
    int time_out = 0;
    
    int number_solutions = -1;

    boolean interval = false;

    boolean precisionDefined = false;
    double precision;

    boolean runSearch = true;

	/**
	 * It constructs an Options object and parses all the parameters/options provided 
	 * to flatzinc to jacop parser.
	 * 
	 * @param args arguments to flatzinc to jacop parser.
	 */
	public Options(String[] args) {
		
		argument = args;
		
		if (args.length == 0) {
			System.out.println("fz2jacop: no model file specified");
			System.out.println("fz2jacop: use --help for more information.");
			System.exit(0);
		}
		else if (args.length == 1) {
			String arg = args[0];
			if (arg.equals("-h") || arg.equals("--help")) {
				System.out.println(
						"Usage: java org.jacop.fz.Fz2jacop [<options>] <file>.fzn\n"+
						"Options:\n"+
						"    -h, --help\n"+
						"        Print this message.\n"+
						"    -a, --all, --all-solutions\n"+
						"    -v, --verbose\n"+
						"    -t <value>, --time-out <value>\n"+
						"        <value> - time in second.\n"+
						"    -s, --statistics\n"+
						"    -n <value>, --num-solutions <value>\n"+
						"        <value> - limit on solution number.\n"+
						"    -i, --interval print intervals instead of values for floating variables\n"+
						"    -p <value>, --precision <value> defines precision for floating operations\n"+
						"        overrides precision definition in search annotation."
				);
				System.exit(0);
			}
			else { // input file
			    fileName = args[0];
			}
		}
		else { // args.length > 1
			int i=0; 
			while (i<args.length-1) {
				// decode options
				if (args[i].equals("-a") || args[i].equals("--all-solutions") || args[i].equals("--all")) {
					all = true;
					i++;
				}
				else if (args[i].equals("-t") || args[i].equals("--time-out")) {
					time_out = Integer.parseInt(args[++i]);
					i++;
				}
				else if (args[i].equals("-s") || args[i].equals("--statistics")) {
					statistics = true;
					i++;
				}
				else if (args[i].equals("-n") || args[i].equals("--num-solutions")) {
					number_solutions = Integer.parseInt(args[++i]);
					if (number_solutions > 1) 
					    all = true;
					i++;
				}
				else if (args[i].equals("-v") || args[i].equals("--verbose")) {
					    verbose = true;
					i++;
				}
				else if (args[i].equals("-i") || args[i].equals("--interval")) {
				    interval = true;
				    i++;
				}
				else if (args[i].equals("-p") || args[i].equals("--precision")) {
				        precisionDefined = true;
					precision = Double.parseDouble(args[++i]);
					if (precision >= 0)
					    FloatDomain.setPrecision(precision);
					else {
					    precision = FloatDomain.precision();
					    System.err.println("%% Precisison parameter not correct; using default precision " + precision);
					}
					i++;
				}
				else {
					System.out.println("fz2jacop: not recognized option "+ args[i]);
					i++;
				}
			}	    

			fileName = args[args.length-1];
		}
	}

	/**
	 * It returns the file input stream for the file containing flatzinc description. 
	 * @return file containing flatzinc description.
	 */
	public FileInputStream getFile() {
	    try {
		file = new java.io.FileInputStream(fileName);
	    } catch (java.io.FileNotFoundException e) {
		System.out.println("Flatzinc2JaCoP Parser Version 0.1:  File " + fileName + " not found.");
		System.exit(0);
	    }

	    return file;
	}

	/**
	 * It returns the file name for the file containing flatzinc description. 
	 * @return file name containing flatzinc description.
	 */
	public String getFileName() {
		return fileName;
	}

	/**
	 * It returns true if the search for all solution has been requested.
	 * @return true if the search for all solution should take place, false otherwise. 
	 */
	public boolean getAll() {
		return all;
	}

	/**
	 * It returns true if the verbose mode has been requested.
	 * @return true if the verbose mode is active, false otherwise. 
	 */
	public boolean getVerbose() {
		return verbose;
	}

	/**
	 * It returns true if the search statistics are to be displayed. 
	 * 
	 * @return true if the search statistics are to be displayed, false otherwise.
	 */
	public boolean getStatistics() {
		return statistics;
	}

	/**
	 * It returns time out set for the search. 
	 * 
	 * @return the value of the timeOut (in seconds), 0 if no time-out was set.
	 */
	public int getTimeOut() {
		return time_out;
	}

	/**
	 * It returns the number of solutions the solver should search for. 
	 * 
	 * @return the number of solutions the search should search for.
	 */
	public int getNumberSolutions() {
		return number_solutions;
	}

	/**
	 * It returns true if the interval print mode has been requested.
	 * @return true if the interval print mode is active, false otherwise. 
	 */
	public boolean getInterval() {
		return interval;
	}

	/**
	 * It defines whether to run the solver. 
	 */
	public void doNotRunSearch() {
	    this.runSearch = false;
	}

	/**
	 * It returns true if the search must be run and false otherwise.
	 * @return true if run search, false otherwise. 
	 */
	public boolean runSearch() {
		return runSearch;
	}


	/**
	 * It returns precision defined in  the command line
	 * @return precision. 
	 */
	public double getPrecision() {
		return precision;
	}

	/**
	 * It defines precision. 
	 */
	public boolean precision() {
		return precisionDefined;
	}
	
}









