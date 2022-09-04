/*
 * Options.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz;

import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;
import java.io.FileInputStream;

/**
 * It parses the options provided to flatzinc parser/executable. It contains
 * information about all options used for a given flatzinc file.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.9
 */
public class Options {

    FileInputStream file;

    String fileName;

    boolean all = false;

    boolean verbose = false;

    boolean statistics = false;

    boolean freeSearch = false;
    
    int time_out = 0;

    int number_solutions = -1;

    boolean interval = false;

    boolean precisionDefined = false;
    double precision;

    double format;

    boolean boundConsistency = false;

    boolean runSearch = true;

    boolean use_sat = false;

    boolean complementary_search = false;

    float decay = 0.99f;

    double step = 0.0d;
    
    boolean debug = false;

    String outputFilename = "";

    /**
     * It constructs an Options object and parses all the parameters/options provided
     * to flatzinc to jacop parser.
     *
     * @param args arguments to flatzinc to jacop parser.
     */
    public Options(String[] args) {

        if (args.length == 0) {
            System.out.println("fz2jacop: no model file specified");
            System.out.println("fz2jacop: use --help for more information.");
            System.exit(0);
        } else if (args.length == 1) {
            String arg = args[0];
            if (arg.equals("-h") || arg.equals("--help")) {
                System.out.println("Usage: java org.jacop.fz.Fz2jacop [<options>] <file>.fzn\n" + "Options:\n"
                    + "    -h, --help\n"
                    + "        Print this message.\n"
                    + "    -a, --all, --all-solutions\n"
                    + "    -v, --verbose\n"
                    + "    -t <value>, --time-out <value>\n" + "        <value> - time in milisecond.\n"
                    + "    -s, --statistics\n"
                    + "    -n <value>, --num-solutions <value>\n" + "        <value> - limit on solution number.\n"
                    + "    -f free search; no need to follow search annotations.\n"
                    + "    -r <value> --random-seed <value> use value as the random seed for random number generators the solver is using.\n"
                    + "    -b, --bound - use bounds consistency whenever possible;\n"
                    + "        overrides annotation \":: domain\" and selects constraints\n"
                    + "        implementing bounds consistency (default false).\n"
                    + "    -sat use SAT solver for boolean constraints.\n"
                    + "    -cs, --complementary-search - gathers all model, non-defined\n"
                    + "         variables to create the final search\n"
                    + "    -i, --interval print intervals instead of values for floating variables\n"
                    + "    --precision <value> defines precision for floating operations\n"
                    + "        overrides precision definition in search annotation.\n"
                    + "    --format <value> defines print-out format (uses precision method)\n"
                    + "        for floating-point variables.\n"
                    + "    -o, --outputfile defines file for solver output\n"
                    + "    -d, --decay decay factor for accumulated failure count (afc)\n"
                    + "         and activity-based variable selection heuristic\n"
                    + "    --step <value> distance step for cost function for floating-point optimization")
                    ;
                System.exit(0);
            } else { // input file
                fileName = args[0];
            }
        } else { // args.length > 1
            int i = 0;
            while (i < args.length - 1) {
                // decode options
                if (args[i].equals("-a") || args[i].equals("--all-solutions") || args[i].equals("--all")) {
                    all = true;
                    if (number_solutions == -1)
                        number_solutions = Integer.MAX_VALUE;
                    else
                        System.err.println("%% Option -a ignored since number of solutions has been specified by option -n");
                    i++;
                } else if (args[i].equals("-t") || args[i].equals("--time-out")) {
                    time_out = Integer.parseInt(args[++i]);
                    i++;
                } else if (args[i].equals("-s") || args[i].equals("--statistics")) {
                    statistics = true;
                    i++;
                } else if (args[i].equals("-f") || args[i].equals("--free-search")) {
                    freeSearch = true;
                    i++;
                } else if (args[i].equals("-sat")) {
                    use_sat = true;
                    i++;
                } else if (args[i].equals("-n") || args[i].equals("--num-solutions")) {
                    if (number_solutions == Integer.MAX_VALUE)
                        System.err.println("%% Option -a ignored since number of solutions has been specified by option -n");
                    number_solutions = Integer.parseInt(args[++i]);
                    if (number_solutions > 1)
                        all = true;
                    i++;
                } else if (args[i].equals("-v") || args[i].equals("--verbose")) {
                    verbose = true;
                    i++;
                } else if (args[i].equals("-i") || args[i].equals("--interval")) {
                    interval = true;
                    i++;
                } else if (args[i].equals("--precision")) { // removed args[i].equals("-p") || KKU 2019-10-31
                    precisionDefined = true;
                    precision = Double.parseDouble(args[++i]);
                    if (precision >= 0)
                        FloatDomain.setPrecision(precision);
                    else {
                        precision = FloatDomain.precision();
                        System.err.println("%% Precisison parameter not correct; using default precision " + precision);
                    }
                    i++;
                } else if (args[i].equals("--format")) { // removed args[i].equals("-f") || KKU 2019-10-31
                    format = Double.parseDouble(args[++i]);
                    if (format >= 0)
                        FloatDomain.setFormat(format);
                    else {
                        format = Double.MAX_VALUE;
                        System.err.println("%% Format parameter not correct;");
                    }
                    i++;
                } else if (args[i].equals("-b") || args[i].equals("--bound")) {
                    boundConsistency = true;
                    i++;
                } else if (args[i].equals("-cs") || args[i].equals("--complementary-search")) {
                    complementary_search = true;
                    i++;
                } else if (args[i].equals("-debug")) {
                    debug = true;
                    i++;
                } else if (args[i].equals("-o") || args[i].equals("--outputfile")) {
                    outputFilename = args[++i];
                    i++;
                } else if (args[i].equals("-d") || args[i].equals("--decay")) {
                    decay = Float.parseFloat(args[++i]);
                    if (decay < 0.0f || decay > 1.0f)
                        System.err.println("%% Decay parameter incorrect; assumed default value 0.99");
                    i++;
                } else if (args[i].equals("--step")) {
                    step = Double.parseDouble(args[++i]);
                    if (step < 0.0f) {
                        System.err.println("%% Step for floating-point optimization is incorrect; assumed default step");
                        step = 0.0d;
                    }
                    FloatDomain.setStep(step);
                    i++;
                } else if (args[i].equals("-r") || args[i].equals("--random-seed")) {
                    long seed = Long.parseLong(args[++i]);
                    Store.setSeed(seed);
                    i++;
                } else {
                    System.out.println("%% fz2jacop: not recognized option " + args[i] + "; ignored");
                    i++;
                }
            }

            fileName = args[args.length - 1];
        }
    }

    /**
     * It returns the file input stream for the file containing flatzinc description.
     *
     * @return file containing flatzinc description.
     */
    public FileInputStream getFile() {
        try {
            file = new FileInputStream(fileName);
        } catch (java.io.FileNotFoundException e) {
            System.out.println("% Flatzinc2JaCoP Parser Version 1.0:  File " + fileName + " not found.");
            System.exit(0);
        }

        return file;
    }

    /**
     * It returns the file name for the file containing flatzinc description.
     *
     * @return file name containing flatzinc description.
     */
    public String getFileName() {
        return fileName;
    }

    /**
     * It returns true if the search for all solution has been requested.
     *
     * @return true if the search for all solution should take place, false otherwise.
     */
    public boolean getAll() {
        return all;
    }

    /**
     * It returns true if the verbose mode has been requested.
     *
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
     *
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
     *
     * @return true if run search, false otherwise.
     */
    public boolean runSearch() {
        return runSearch;
    }


    /**
     * It defines whether to use bound consistency.
     *
     * @return true if bound consistency prefered, false otherwise (defult).
     */
    public boolean getBoundConsistency() {
        return boundConsistency;
    }

    /**
     * It returns precision defined in the command line.
     *
     * @return precision.
     */
    public double getPrecision() {
        return precision;
    }

    /**
     * It informs whether precision is defined.
     *
     * @return true if precision for floating point solver is defined
     */
    public boolean precision() {
        return precisionDefined;
    }

    /**
     * It defines whether sat is used.
     *
     * @return true sat is used, false otherwise
     */
    public boolean useSat() {
        return use_sat;
    }

    /**
     * It defines whether to use debug information print-out.
     *
     * @return true if debugging information is printed, false otherwise
     */
    public boolean debug() {
        return debug;
    }

    /**
     * It defines whether search annotation can be ignored.
     *
     * @return true if search annotation can be ignored
     */
    public boolean freeSearch() {
        return freeSearch;
    }

    public String getOutputFilename() {
        return outputFilename;
    }

    public float getDecay() {
        return decay;
    }

    /**
     * It defines wheter additional search should use output variables only (false, default).
     * or should try to collect all non introduced variables (true).
     *
     * @return additional search should use output variables only (false, default).
     * or should try to collect all non introduced variables (true)
     */
    public boolean complementarySearch() {
        return complementary_search;
    }
}
