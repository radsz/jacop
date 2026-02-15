/*
 * Options.java
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

package org.jacop.fz;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;

/**
 * It parses the options provided to flatzinc parser/executable. It contains information about all
 * options used for a given flatzinc file.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class Options {

  public RestartType restartType = RestartType.NONE;
  FileInputStream file;
  String fileName;
  boolean all;
  boolean verbose;
  boolean statistics;
  boolean freeSearch;
  int time_out;
  int number_solutions = -1;
  boolean interval;
  boolean precisionDefined;
  double precision;
  double format;
  boolean boundConsistency;
  boolean runSearch = true;
  boolean use_sat;
  boolean complementary_search;
  float decay = 0.99f;
  double step = 0.0d;
  boolean debug;
  String outputFilename = "";
  int restartLimit;
  int scale = 250;
  double base = 1.5;

  /**
   * It constructs an Options object and parses all the parameters/options provided to flatzinc to
   * jacop parser.
   *
   * @param args arguments to flatzinc to jacop parser.
   */
  public Options(String[] args) {

    if (args.length == 0) {
      IO.println("fz2jacop: no model file specified");
      IO.println("fz2jacop: use --help for more information.");
      System.exit(0);
    } else if (args.length == 1) {
      parseSingleArg(args[0]);
    } else {
      parseMultipleArgs(args);
    }
  }

  private void parseSingleArg(String arg) {
    if ("-h".equals(arg) || "--help".equals(arg)) {
      printHelpAndExit();
    }
    fileName = arg;
  }

  private void printHelpAndExit() {
    IO.println(
        """
        Usage: java org.jacop.fz.Fz2jacop [<options>] <file>.fzn
        Options:
            -h, --help
                Print this message.
            -a, --all, --all-solutions
            -v, --verbose
            -t <value>, --time-out <value>
                <value> - time in milisecond.
            -s, --statistics
            -n <value>, --num-solutions <value>
                <value> - limit on solution number.
            -f free search; no need to follow search annotations.
            -r <value> --random-seed <value> use value as the random seed for random number generators the solver is using.
            -b, --bound - use bounds consistency whenever possible;
                overrides annotation ":: domain" and selects constraints
                implementing bounds consistency (default false).
            -sat use SAT solver for boolean constraints.
            -cs, --complementary-search - gathers all model, non-defined
                 variables to create the final search
            -i, --interval print intervals instead of values for floating variables
            --precision <value> defines precision for floating operations
                overrides precision definition in search annotation.
            --format <value> defines print-out format (uses precision method)
                for floating-point variables.
            -o, --outputfile defines file for solver output
            -d, --decay decay factor for accumulated failure count (afc)
                 and activity-based variable selection heuristic
            --step <value> distance step for cost function for floating-point optimization
            --restart <value> defines restart search; one of "none", "constant", "linear", "luby", "geometric"
            --restart-base <value> base for geomteric restart search
            --restart-scale <value> scale for restart search
            --restart-limit <value> limits number of restarts in restart search
        """);
    System.exit(0);
  }

  private void parseMultipleArgs(String[] args) {
    int i = 0;
    while (i < args.length - 1) {
      i = parseOption(args, i);
    }
    fileName = args[args.length - 1];
  }

  private int parseOption(String[] args, int i) {
    String opt = args[i];
    switch (opt) {
      case "-a", "--all-solutions", "--all" -> i = handleAllSolutions(i);
      case "-t", "--time-out" -> i = handleTimeOut(args, i);
      case "-s", "--statistics" -> i = handleStatistics(i);
      case "-f", "--free-search" -> i = handleFreeSearch(i);
      case "-sat" -> i = handleSat(i);
      case "-n", "--num-solutions" -> i = handleNumSolutions(args, i);
      case "-v", "--verbose" -> i = handleVerbose(i);
      case "-i", "--interval" -> i = handleInterval(i);
      case "--precision" -> i = handlePrecision(args, i);
      case "--format" -> i = handleFormat(args, i);
      case "-b", "--bound" -> i = handleBound(i);
      case "-cs", "--complementary-search" -> i = handleComplementarySearch(i);
      case "-debug" -> i = handleDebug(i);
      case "-o", "--outputfile" -> i = handleOutputFile(args, i);
      case "-d", "--decay" -> i = handleDecay(args, i);
      case "--step" -> i = handleStep(args, i);
      case "-r", "--random-seed" -> i = handleRandomSeed(args, i);
      case "--restart" -> i = handleRestart(args, i);
      case "--restart-base" -> i = handleRestartBase(args, i);
      case "--restart-scale" -> i = handleRestartScale(args, i);
      case "--restart-limit" -> i = handleRestartLimit(args, i);
      default -> {
        IO.println("%% fz2jacop: not recognized option " + opt + "; ignored");
        i++;
      }
    }
    return i;
  }

  private int handleAllSolutions(int i) {
    all = true;
    if (number_solutions == -1) {
      number_solutions = Integer.MAX_VALUE;
    } else {
      System.err.println(
          "%% Option -a ignored since number of solutions has been specified by option -n");
    }
    return i + 1;
  }

  private int handleTimeOut(String[] args, int i) {
    time_out = Integer.parseInt(args[++i]);
    return i + 1;
  }

  private int handleStatistics(int i) {
    statistics = true;
    return i + 1;
  }

  private int handleFreeSearch(int i) {
    freeSearch = true;
    return i + 1;
  }

  private int handleSat(int i) {
    use_sat = true;
    return i + 1;
  }

  private int handleNumSolutions(String[] args, int i) {
    if (number_solutions == Integer.MAX_VALUE) {
      System.err.println(
          "%% Option -a ignored since number of solutions has been specified by option -n");
    }
    number_solutions = Integer.parseInt(args[++i]);
    if (number_solutions > 1) {
      all = true;
    }
    return i + 1;
  }

  private int handleVerbose(int i) {
    verbose = true;
    return i + 1;
  }

  private int handleInterval(int i) {
    interval = true;
    return i + 1;
  }

  private int handlePrecision(String[] args, int i) {
    precisionDefined = true;
    precision = Double.parseDouble(args[++i]);
    if (precision >= 0) {
      FloatDomain.setPrecision(precision);
    } else {
      precision = FloatDomain.precision();
      System.err.println(
          "%% Precisison parameter not correct; using default precision " + precision);
    }
    return i + 1;
  }

  private int handleFormat(String[] args, int i) {
    format = Double.parseDouble(args[++i]);
    if (format >= 0) {
      FloatDomain.setFormat(format);
    } else {
      format = Double.MAX_VALUE;
      System.err.println("%% Format parameter not correct;");
    }
    return i + 1;
  }

  private int handleBound(int i) {
    boundConsistency = true;
    return i + 1;
  }

  private int handleComplementarySearch(int i) {
    complementary_search = true;
    return i + 1;
  }

  private int handleDebug(int i) {
    debug = true;
    return i + 1;
  }

  private int handleOutputFile(String[] args, int i) {
    outputFilename = args[++i];
    return i + 1;
  }

  private int handleDecay(String[] args, int i) {
    decay = Float.parseFloat(args[++i]);
    if (decay < 0.0f || decay > 1.0f) {
      System.err.println("%% Decay parameter incorrect; assumed default value 0.99");
    }
    return i + 1;
  }

  private int handleStep(String[] args, int i) {
    step = Double.parseDouble(args[++i]);
    if (step < 0.0f) {
      System.err.println(
          "%% Step for floating-point optimization is incorrect; assumed default step");
      step = 0.0d;
    }
    FloatDomain.setStep(step);
    return i + 1;
  }

  private int handleRandomSeed(String[] args, int i) {
    long seed = Long.parseLong(args[++i]);
    Store.setSeed(seed);
    return i + 1;
  }

  private int handleRestart(String[] args, int i) {
    restartType = parseRestartType(args[++i]);
    return i + 1;
  }

  private RestartType parseRestartType(String type) {
    return switch (type) {
      case "none" -> RestartType.NONE;
      case "constant" -> RestartType.CONSTANT;
      case "linear" -> RestartType.LINEAR;
      case "luby" -> RestartType.LUBY;
      case "geometric" -> RestartType.GEOMETRIC;
      default ->
          throw new IllegalArgumentException("Wrong argument " + type + " for option \"-restart\"");
    };
  }

  private int handleRestartBase(String[] args, int i) {
    base = Double.parseDouble(args[++i]);
    return i + 1;
  }

  private int handleRestartScale(String[] args, int i) {
    scale = Integer.parseInt(args[++i]);
    return i + 1;
  }

  private int handleRestartLimit(String[] args, int i) {
    restartLimit = Integer.parseInt(args[++i]);
    return i + 1;
  }

  /**
   * It returns the file input stream for the file containing flatzinc description.
   *
   * @return file containing flatzinc description.
   */
  public FileInputStream getFile() {
    try {
      file = new FileInputStream(fileName);
    } catch (FileNotFoundException _) {
      IO.println("% Flatzinc2JaCoP Parser Version 1.0:  File " + fileName + " not found.");
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

  /** It defines whether to run the solver. */
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

  /** Sat is used. */
  public void setSat() {
    use_sat = true;
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
   * It defines wheter additional search should use output variables only (false, default). or
   * should try to collect all non introduced variables (true).
   *
   * @return additional search should use output variables only (false, default). or should try to
   *     collect all non introduced variables (true)
   */
  public boolean complementarySearch() {
    return complementary_search;
  }

  public RestartType getRestartType() {
    return restartType;
  }

  public double getRestartBase() {
    return base;
  }

  public int getRestartScale() {
    return scale;
  }

  public int getRestartLimit() {
    return restartLimit;
  }

  /** Restart strategy types for search. */
  public enum RestartType {
    NONE,
    CONSTANT,
    LINEAR,
    LUBY,
    GEOMETRIC
  }
}
