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
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;
import org.jacop.presolve.Derivation;
import org.jacop.presolve.Probing;

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
  boolean freeSearchWithoutAnnotation = true;
  boolean newFreeSearchEngine = true;
  final Map<String, String> freeConfig = new HashMap<>();
  boolean restartGiven;
  int timeOut;

  /** The time the options were read; the time-out counts from it. */
  private final long startTime = System.currentTimeMillis();

  int numberSolutions = -1;
  boolean interval;
  boolean precisionDefined;
  double precision;
  double format;
  boolean boundConsistency;
  boolean runSearch = true;
  boolean useSat;
  boolean lcg;
  // the default can be changed by the system property jacop.presolve, for example to run the
  // FlatZinc test suites with presolve
  Presolve presolve =
      Objects.requireNonNullElse(
          presolveMode(System.getProperty("jacop.presolve", "off")), Presolve.OFF);
  boolean presolveImplied;
  boolean symmetry = true;
  boolean presolveDual = true;
  int presolveRounds = Derivation.DEFAULT_ROUNDS;
  Probing.Mode probe =
      Objects.requireNonNullElse(
          probeMode(System.getProperty("jacop.presolve.probe", "off")), Probing.Mode.OFF);
  long probeBudget = 1000;
  boolean complementarySearch;
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
      System.exit(1);
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
            --free-engine <value> engine for free search; one of "new" (default), "legacy"
            --default-search <value> search for a model without search annotation; one of
                "free" (default; as with -f), "input" (input order, splitting the domains)
            --free-config <key=value,...> settings of the new free search engine, for experiments:
                heuristic=domwdeg|cacd|chs|afc, lc=<k>, phase=0|1, restarts=geometric|luby|none,
                scale=<failures>, base=<growth of geometric restarts> (100, 1.5; optimisation 10, 1.05),
                restart-on-solution=0|1, objective-last=0|1, interleave=restart|solution|none,
                nogoods=0|1 (nogoods from restarts, default 1),
                impact=<n> (bound-impact values for optimisation, on domains up to n values; 0 = off),
                impact-until=first|always, impact-every=<k> (probe in the first run and every k-th),
                restart-reset=0|1 (restart limits start again after each solution; 1 for optimisation),
                flush=<k> (forget the dom/wdeg weights every k restarts; 0 = never; 32 for optimisation),
                lcg-lb=<share> (with --lcg: conflicts of objective lower-bound runs per
                conflict of branch and bound, default 0.5; 0 = off)
            -r <value> --random-seed <value> use value as the random seed for random number generators the solver is using.
            -b, --bound - use bounds consistency whenever possible;
                overrides annotation ":: domain" and selects constraints
                implementing bounds consistency (default false).
            -sat use SAT solver for boolean constraints.
            --lcg solve integer and Boolean models with lazy clause generation (JaSAT as
                the SAT core); the search annotation is followed without restarts, or with -f
                alternated per restart with branching on the most active variables.
            --presolve <value> presolve the model before search; one of "off" (default), "on",
                "check" (as "on", and every solution is checked against the loaded model)
            --presolve-implied <value> with presolve, post the constraints implied by
                all-different constraints (sum bounds); "off" (default) or "on"
            --symmetry <value> with presolve, break the variable symmetries of the model with
                lex-leader constraints; one of "on" (default), "off". Off when a satisfaction
                problem asks for more than one solution (-a, -n).
            --presolve-dual <value> dual reductions in presolve, "on" (default) or "off"; they
                run only when one solution or an optimum is searched for
            --presolve-rounds <value> the most rounds of presolve rules, each followed by
                propagation, before presolve stops short of a fixpoint (default 10).
            --presolve-probe <value> with --presolve, probe the root in the presolve rounds; one
                of "off" (default), "shave" (bound shaving and failed-literal probing of 0-1
                variables), "sac" (as "shave", and every value of small domains)
            --presolve-probe-budget <ms> time probing may take (default 1000)
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
      case "--free-engine" -> i = handleFreeEngine(args, i);
      case "--free-config" -> i = handleFreeConfig(args, i);
      case "--default-search" -> i = handleDefaultSearch(args, i);
      case "-sat" -> i = handleSat(i);
      case "--lcg" -> i = handleLcg(i);
      case "--presolve" -> i = handlePresolve(args, i);
      case "--presolve-implied" -> i = handlePresolveImplied(args, i);
      case "--symmetry" -> i = handleSymmetry(args, i);
      case "--presolve-dual" -> i = handlePresolveDual(args, i);
      case "--presolve-rounds" -> i = handlePresolveRounds(args, i);
      case "--presolve-probe" -> i = handleProbe(args, i);
      case "--presolve-probe-budget" -> i = handleProbeBudget(args, i);
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
    if (numberSolutions == -1) {
      numberSolutions = Integer.MAX_VALUE;
    } else {
      System.err.println(
          "%% Option -a ignored since number of solutions has been specified by option -n");
    }
    return i + 1;
  }

  private int handleTimeOut(String[] args, int i) {
    timeOut = Integer.parseInt(args[++i]);
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

  private int handleFreeEngine(String[] args, int i) {
    String engine = args[++i];
    switch (engine) {
      case "legacy" -> newFreeSearchEngine = false;
      case "new" -> newFreeSearchEngine = true;
      default -> System.err.println("%% Free search engine " + engine + " not known; ignored");
    }
    return i + 1;
  }

  private int handleDefaultSearch(String[] args, int i) {
    String search = args[++i];
    switch (search) {
      case "free" -> freeSearchWithoutAnnotation = true;
      case "input" -> freeSearchWithoutAnnotation = false;
      default -> System.err.println("%% Default search " + search + " not known; ignored");
    }
    return i + 1;
  }

  private int handleFreeConfig(String[] args, int i) {
    for (String setting : args[++i].split(",")) {
      String[] kv = setting.split("=", 2);
      if (kv.length == 2) {
        freeConfig.put(kv[0].strip(), kv[1].strip());
      } else {
        System.err.println("%% Free search setting " + setting + " not understood; ignored");
      }
    }
    return i + 1;
  }

  private int handleSat(int i) {
    useSat = true;
    return i + 1;
  }

  private int handleLcg(int i) {
    lcg = true;
    return i + 1;
  }

  private int handlePresolve(String[] args, int i) {
    Presolve mode = presolveMode(args[++i]);
    if (mode != null) {
      presolve = mode;
    }
    return i + 1;
  }

  private int handlePresolveImplied(String[] args, int i) {
    switch (args[++i]) {
      case "on" -> presolveImplied = true;
      case "off" -> presolveImplied = false;
      default -> System.err.println("%% Presolve-implied mode " + args[i] + " not known; ignored");
    }
    return i + 1;
  }

  private int handleSymmetry(String[] args, int i) {
    String mode = args[++i];
    switch (mode) {
      case "on" -> symmetry = true;
      case "off" -> symmetry = false;
      default -> System.err.println("%% Symmetry mode " + mode + " not known; ignored");
    }
    return i + 1;
  }

  private int handlePresolveDual(String[] args, int i) {
    switch (args[++i]) {
      case "on" -> presolveDual = true;
      case "off" -> presolveDual = false;
      default -> System.err.println("%% Presolve dual mode " + args[i] + " not known; ignored");
    }
    return i + 1;
  }

  private int handlePresolveRounds(String[] args, int i) {
    int rounds = Integer.parseInt(args[++i]);
    if (rounds >= 1) {
      presolveRounds = rounds;
    } else {
      System.err.println("%% Presolve rounds must be at least 1; " + rounds + " ignored");
    }
    return i + 1;
  }

  private int handleProbe(String[] args, int i) {
    Probing.Mode mode = probeMode(args[++i]);
    if (mode != null) {
      probe = mode;
    }
    return i + 1;
  }

  private static Probing.Mode probeMode(String mode) {
    return switch (mode) {
      case "off" -> Probing.Mode.OFF;
      case "shave" -> Probing.Mode.SHAVE;
      case "sac" -> Probing.Mode.SAC;
      default -> {
        System.err.println("%% Probing mode " + mode + " not known; ignored");
        yield null;
      }
    };
  }

  private int handleProbeBudget(String[] args, int i) {
    probeBudget = Long.parseLong(args[++i]);
    return i + 1;
  }

  private static Presolve presolveMode(String mode) {
    return switch (mode) {
      case "off" -> Presolve.OFF;
      case "on" -> Presolve.ON;
      case "check" -> Presolve.CHECK;
      default -> {
        System.err.println("%% Presolve mode " + mode + " not known; ignored");
        yield null;
      }
    };
  }

  private int handleNumSolutions(String[] args, int i) {
    if (numberSolutions == Integer.MAX_VALUE) {
      System.err.println(
          "%% Option -a ignored since number of solutions has been specified by option -n");
    }
    numberSolutions = Integer.parseInt(args[++i]);
    if (numberSolutions > 1) {
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
    complementarySearch = true;
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
    restartGiven = true;
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
      System.exit(1);
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
    return timeOut;
  }

  /**
   * It returns the part of the time-out that is left. The time-out covers the whole run, building
   * the model included, so it counts from the time the options were read.
   *
   * @return the time left in milliseconds, at least 1; 0 if no time-out was set.
   */
  public int getRemainingTimeOut() {
    if (timeOut <= 0) {
      return 0;
    }
    return (int) Math.max(1, timeOut - (System.currentTimeMillis() - startTime));
  }

  /**
   * It checks whether the time-out has passed.
   *
   * @return true if a time-out was set and it has passed.
   */
  public boolean timeOutPassed() {
    return timeOut > 0 && System.currentTimeMillis() - startTime > timeOut;
  }

  /**
   * It returns the number of solutions the solver should search for.
   *
   * @return the number of solutions the search should search for.
   */
  public int getNumberSolutions() {
    return numberSolutions;
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
   * It defines whether Boolean constraints are translated to clauses: for the SAT solver (-sat) or
   * for the LCG solver (--lcg).
   *
   * @return true sat is used, false otherwise
   */
  public boolean useSat() {
    return useSat || lcg;
  }

  /**
   * It defines whether the model is solved with lazy clause generation.
   *
   * @return true when --lcg was given
   */
  public boolean lcg() {
    return lcg;
  }

  /** Whether the model is presolved before search, and how. */
  public enum Presolve {
    /** The model is searched in the store it was loaded into. */
    OFF,
    /** Search runs on a store derived by presolve; the loaded store only receives solutions. */
    ON,
    /** As ON, but the loaded store keeps its constraints and checks every solution. */
    CHECK
  }

  /**
   * It defines whether the model is presolved before search (--presolve).
   *
   * @return the presolve mode, OFF by default
   */
  public Presolve presolve() {
    return presolve;
  }

  /**
   * It defines whether presolve posts implied constraints (--presolve-implied).
   *
   * @return false by default
   */
  public boolean presolveImplied() {
    return presolveImplied;
  }

  /**
   * It defines whether presolve breaks the symmetries of the model (--symmetry).
   *
   * @return true by default
   */
  public boolean symmetry() {
    return symmetry;
  }

  /**
   * It defines whether presolve may use dual reductions (--presolve-dual); they run only when the
   * search wants one solution or an optimum.
   *
   * @return true unless switched off
   */
  public boolean presolveDual() {
    return presolveDual;
  }

  /**
   * It defines the most rounds of presolve rules (--presolve-rounds).
   *
   * @return the most rounds, {@link Derivation#DEFAULT_ROUNDS} by default
   */
  public int presolveRounds() {
    return presolveRounds;
  }

  /**
   * It defines what presolve probes at the root (--presolve-probe).
   *
   * @return the probing mode, OFF by default
   */
  public Probing.Mode probe() {
    return probe;
  }

  /**
   * It defines the time root probing may take (--presolve-probe-budget).
   *
   * @return the budget in milliseconds, 1000 by default
   */
  public long probeBudget() {
    return probeBudget;
  }

  /** Sat is used. */
  public void setSat() {
    useSat = true;
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

  /**
   * It defines whether a model without search annotation is solved with free search, as with -f
   * (default), or by labelling its variables in input order (--default-search input).
   *
   * @return true if a model without search annotation is solved with free search
   */
  public boolean freeSearchWithoutAnnotation() {
    return freeSearchWithoutAnnotation;
  }

  /**
   * It defines whether free search uses the FreeSearch engine instead of chained depth-first
   * searches.
   *
   * @return true if free search uses the FreeSearch engine.
   */
  public boolean newFreeSearchEngine() {
    return newFreeSearchEngine;
  }

  /**
   * Returns a setting of the new free search engine given with --free-config.
   *
   * @param key the setting.
   * @param defaultValue the value when the setting is not given.
   * @return the value of the setting.
   */
  public String freeConfig(String key, String defaultValue) {
    return freeConfig.getOrDefault(key, defaultValue);
  }

  /**
   * Returns whether a restart strategy was given with --restart.
   *
   * @return true if --restart was given.
   */
  public boolean restartGiven() {
    return restartGiven;
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
    return complementarySearch;
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
