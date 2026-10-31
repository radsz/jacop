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
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import org.jacop.constraints.lp.LinearRelaxation;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;
import org.jacop.presolve.Derivation;
import org.jacop.presolve.Probing;
import org.jacop.presolve.Rule;

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
  boolean searchStatistics;
  boolean freeSearch;
  boolean freeSearchWithoutAnnotation = true;
  boolean newFreeSearchEngine = true;
  final Map<String, String> freeConfig = new HashMap<>();
  private long randomSeed;
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
  // the default can be changed by the system property jacop.lcg ("on" or "off"), for example to
  // run the FlatZinc test suites, whose expected outputs were recorded without LCG
  boolean lcg = !"off".equals(System.getProperty("jacop.lcg", "on"));
  // whether --lcg was given; without it, LCG is left out for models it does not support
  boolean lcgGiven;
  boolean lp = true;
  // --proof: the path prefix of the VeriPB proof (.pbp) and its OPB model (.opb), or null
  String proof;
  LinearRelaxation.Simplex lpSimplex = LinearRelaxation.Simplex.DENSE;
  int threads = 1;
  // the portfolio thread this model is solved in, or null
  Portfolio.Worker portfolioWorker;
  // the default can be changed by the system property jacop.presolve, for example to run the
  // FlatZinc test suites with presolve
  Presolve presolve =
      Objects.requireNonNullElse(
          presolveMode(System.getProperty("jacop.presolve", "off")), Presolve.OFF);
  boolean presolveImplied;
  boolean symmetry = true;
  boolean presolveDual = true;
  int presolveRounds = Derivation.DEFAULT_ROUNDS;
  Rule.Timing presolveLevel =
      Objects.requireNonNullElse(
          presolveLevel(System.getProperty("jacop.presolve.level", "exhaustive")),
          Rule.Timing.EXHAUSTIVE);
  double presolveAbort = Derivation.DEFAULT_ABORT_FACTOR;
  long presolveTime = -1;
  double presolveRestart;
  boolean presolveTabling = Boolean.getBoolean("jacop.presolve.tabling");
  Probing.Mode probe =
      Objects.requireNonNullElse(
          probeMode(System.getProperty("jacop.presolve.probe", "sac")), Probing.Mode.SAC);
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
                Print the standard FlatZinc statistics (nodes, failures, restarts, peakDepth, ...).
            --search-statistics
                As -s, and also the statistics of JaCoP's own components (lcg*, presolve*, lp*,
                lns*, ls*, symmetry*, probe*, portfolio*, ...). -debug together with -s does the same.
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
                value-impact=<n> (optimisation: values chosen by their bound on the objective,
                ties to the last solution, on domains up to n values; default 64, 0 = off),
                value-impact-time=<share> (most of the time spent on those probes, default 0.25),
                restart-reset=0|1 (restart limits start again after each solution; 1 for optimisation),
                flush=<k> (forget the dom/wdeg weights every k restarts; 0 = never; 32 for optimisation),
                lcg-branching=alternate|auto|literals|activity (with --lcg: alternate (default)
                takes turns at restarts with the annotation, or dom/wdeg without one, the SAT
                solver's decisions on literals with phase false, and activity branching on the
                most active variable; literals only those decisions; auto as literals, with
                activity branching from 1000 conflicts to a first solution; activity the activity
                branching, in runs alternated with the annotation),
                interleave=restart|solution|none (with --lcg: default restart; none with literals
                and auto),
                lcg-lb=<share> (with --lcg: conflicts of objective lower-bound runs per
                conflict of branch and bound, default 0.5; 0 = off),
                lcg-core=<share> (with --lcg and a linear objective: share of the time for
                core-guided search before branch and bound, default 0.5, 0.1 with
                objective cost variables; 0 = off),
                lcg-core-call=<conflicts> (core-guided search stops when one solver call needs
                more, default 5000),
                lcg-booleans-first=on|off|turns (with --lcg: activity branching decides the 0/1
                variables before the others (on, default), or all variables in one order of
                activity (off); turns changes between the two at each restart),
                lcg-keep=0|1 (with --lcg: 1 lets a run that improved the best solution keep its
                way of branching at the next restart; steadier between seeds, default 0),
                lcg-split=<n> (with --lcg: a linear constraint of more than n terms becomes sums of
                blocks of about sqrt of its size, for shorter explanations; default 40; 0 = off),
                probe=<share> (optimisation: failures of objective probes, runs with the objective
                at its lower bound or a growing offset above it, per failure of the other runs;
                default 0.05, 0 = off), probe-fails=<n> (fail limit of the first probe, default 100),
                lns=0|1 (adaptive large neighbourhood search for optimisation, default 1),
                lns-share=<share> (propagations of neighbourhood runs per propagation of the other
                runs, default 0.8; with --lcg time per unit of time, default 3), lns-fails=<failures> (one neighbourhood run, default 100),
                lns-conflicts=<conflicts> (with --lcg: one neighbourhood run, default 200),
                lcg-core-delay=<share> (share of the time for branch and bound between a short
                core-guided probe and the rest of core-guided search, default 0.05; 0 = core-guided
                search first), lcg-core-probe=<share> (share of the time for that probe, default 0.02)
                ls=<share> (with -f, also with --lcg: local search before the search, for this share
                of the time left; default 0 = off), ls-max=<ms> (caps that time),
                ls-patience=<ms> (local search stops after this long without a solution or fewer
                violated constraints, default 1000), ls-moves=fj|walk (fj, the default:
                feasibility jump, the best jump of a sample of variables, all violated constraints
                weigh more at a minimum; walk: a step moves a variable of one violated constraint)
            -r <value> --random-seed <value> use value as the random seed for random number generators the solver is using (default 0).
            -b, --bound - use bounds consistency whenever possible;
                overrides annotation ":: domain" and selects constraints
                implementing bounds consistency (default false).
            -sat use SAT solver for boolean constraints.
            --lcg [on|off] solve integer and Boolean models with lazy clause generation (JaSAT
                as the SAT core); the search annotation is followed without restarts, or with -f
                the SAT core's decisions on literals take turns with activity branching and
                the annotation (see lcg-branching of --free-config). On by default ("--lcg off"
                turns it off); left out by default for models with float variables, for
                satisfaction problems asking for more than one solution (-a, -n), and with -sat.
            --proof <prefix> with --lcg (turned on), write a VeriPB 3 proof of the search to
                <prefix>.pbp and the OPB model it is checked against to <prefix>.opb
                (veripb <prefix>.opb <prefix>.pbp); one thread, branch and bound without
                core-guided, lower-bound and neighbourhood runs, --lp off, bounds consistency
                (as -b). The model is the store
                at the start of the search, over linear, clause and reified linear constraints.
            --lp <value> the linear relaxation of the linear constraints as a propagator, solved
                by a dual simplex during search; its deductions are integer combinations of the
                rows, explained under --lcg; one of "on" (default, the dense simplex), "off",
                "sparse" (the sparse simplex, for large sparse relaxations), "lazy" (the sparse
                simplex with rows added and removed lazily).
            -p <value>, --parallel <value> solve with a portfolio of <value> threads: the
                options given, then free search and lazy clause generation with other
                settings; they share the objective value of the best solution. One thread
                (default 1) for all solutions of satisfaction problems (-a, -n) and for
                models with float variables.
            --presolve <value> presolve the model before search; one of "off" (default), "on",
                "check" (as "on", and every solution is checked against the loaded model)
            --presolve-implied <value> with presolve, post the constraints implied by
                all-different constraints (sum bounds); "off" (default) or "on"
            --symmetry <value> with presolve, break the symmetries of the model: variable
                symmetries with lex-leader constraints (a lex chain for interchangeable columns),
                interchangeable values with value precedence; one of "on" (default), "off". Off
                when a satisfaction problem asks for more than one solution (-a, -n).
            --presolve-dual <value> dual reductions in presolve, "on" (default) or "off"; they
                run only when one solution or an optimum is searched for
            --presolve-rounds <value> the most rounds of presolve rules, each followed by
                propagation, before presolve stops short of a fixpoint (default 10).
            --presolve-level <value> the costliest presolve rules to run: "fast" (linear
                rules only), "medium" (also at-most-ones, duplicate and dominated constraints,
                cumulative reductions) or "exhaustive" (default; also probing, tabling and implied
                constraints). A costlier class runs only after a round of
                the cheaper ones found little.
            --presolve-abort <value> the share of the variables a round of presolve rules must
                change to go back to the fast rules (default 0.001); below it the rounds move to
                the next class, and after the costliest class they stop
            --presolve-restart <value> under --lcg, presolve the root again at a restart once
                the root facts learnt since the last time number this share of the integer
                variables (SCIP's restartfac is 0.025): constraints the root satisfies are left
                out. Default 0 (off); independent of --presolve
            --presolve-time <ms> time the rounds of presolve rules may take (default a
                twentieth of the time limit, unlimited without one)
            --presolve-tabling replace small groups of constraints by the tables of their
                solutions when presolving (default false)
            --presolve-probe <value> with --presolve, probe the root in the presolve rounds; one
                of "off", "shave" (bound shaving and failed-literal probing of 0-1
                variables), "sac" (default; as "shave", and every value of small
                domains)
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

  private void parseMultipleArgs(String[] given) {
    String[] args = splitValues(given);
    int i = 0;
    while (i < args.length - 1) {
      i = parseOption(args, i);
    }
    fileName = args[args.length - 1];
  }

  // --name=value before the file name is the same as --name value
  private static String[] splitValues(String[] args) {
    List<String> split = new ArrayList<>();
    for (int i = 0; i < args.length - 1; i++) {
      int eq = args[i].indexOf('=');
      if (args[i].startsWith("--") && eq > 2) {
        split.add(args[i].substring(0, eq));
        split.add(args[i].substring(eq + 1));
      } else {
        split.add(args[i]);
      }
    }
    split.add(args[args.length - 1]);
    return split.toArray(new String[0]);
  }

  private int parseOption(String[] args, int i) {
    String opt = args[i];
    switch (opt) {
      case "-a", "--all-solutions", "--all" -> i = handleAllSolutions(i);
      case "-t", "--time-out" -> i = handleTimeOut(args, i);
      case "-s", "--statistics" -> i = handleStatistics(i);
      case "--search-statistics", "-searchStatistics" -> i = handleSearchStatistics(i);
      case "-f", "--free-search" -> i = handleFreeSearch(i);
      case "--free-engine" -> i = handleFreeEngine(args, i);
      case "--free-config" -> i = handleFreeConfig(args, i);
      case "--default-search" -> i = handleDefaultSearch(args, i);
      case "-sat" -> i = handleSat(i);
      case "--lcg" -> i = handleLcg(args, i);
      case "--lp" -> i = handleLp(args, i);
      case "--proof" -> i = handleProof(args, i);
      case "-p", "--parallel" -> i = handleParallel(args, i);
      case "--presolve" -> i = handlePresolve(args, i);
      case "--presolve-implied" -> i = handlePresolveImplied(args, i);
      case "--symmetry" -> i = handleSymmetry(args, i);
      case "--presolve-dual" -> i = handlePresolveDual(args, i);
      case "--presolve-rounds" -> i = handlePresolveRounds(args, i);
      case "--presolve-level" -> i = handlePresolveLevel(args, i);
      case "--presolve-abort" -> i = handlePresolveAbort(args, i);
      case "--presolve-time" -> i = handlePresolveTime(args, i);
      case "--presolve-restart" -> i = handlePresolveRestart(args, i);
      case "--presolve-tabling" -> i = handlePresolveTabling(i);
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

  private int handleSearchStatistics(int i) {
    statistics = true;
    searchStatistics = true;
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

  private int handleProof(String[] args, int i) {
    proof = args[++i];
    lcg = true;
    lcgGiven = true;
    return i + 1;
  }

  private int handleSat(int i) {
    useSat = true;
    // -sat solves with CP and a SAT solver for the Boolean constraints, not with LCG
    if (!lcgGiven) {
      lcg = false;
    }
    return i + 1;
  }

  // --lcg alone turns LCG on; --lcg on|off sets it
  private int handleLcg(String[] args, int i) {
    lcgGiven = true;
    if (i + 1 < args.length - 1 && ("on".equals(args[i + 1]) || "off".equals(args[i + 1]))) {
      lcg = "on".equals(args[++i]);
    } else {
      lcg = true;
    }
    return i + 1;
  }

  private int handleLp(String[] args, int i) {
    switch (args[++i]) {
      case "on" -> {
        lp = true;
        lpSimplex = LinearRelaxation.Simplex.DENSE;
      }
      case "off" -> lp = false;
      case "sparse" -> {
        lp = true;
        lpSimplex = LinearRelaxation.Simplex.SPARSE;
      }
      case "lazy" -> {
        lp = true;
        lpSimplex = LinearRelaxation.Simplex.LAZY;
      }
      default -> System.err.println("%% Linear relaxation mode " + args[i] + " not known; ignored");
    }
    return i + 1;
  }

  private int handleParallel(String[] args, int i) {
    threads = Math.max(1, Integer.parseInt(args[++i]));
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

  private int handlePresolveLevel(String[] args, int i) {
    Rule.Timing level = presolveLevel(args[++i]);
    if (level != null) {
      presolveLevel = level;
    }
    return i + 1;
  }

  private static Rule.Timing presolveLevel(String level) {
    return switch (level) {
      case "fast" -> Rule.Timing.FAST;
      case "medium" -> Rule.Timing.MEDIUM;
      case "exhaustive" -> Rule.Timing.EXHAUSTIVE;
      default -> {
        System.err.println("%% Presolve level " + level + " not known; ignored");
        yield null;
      }
    };
  }

  private int handlePresolveAbort(String[] args, int i) {
    double f = Double.parseDouble(args[++i]);
    if (f >= 0) {
      presolveAbort = f;
    } else {
      System.err.println("%% Presolve abort factor must be at least 0; " + f + " ignored");
    }
    return i + 1;
  }

  private int handlePresolveTime(String[] args, int i) {
    long t = Long.parseLong(args[++i]);
    if (t >= 0) {
      presolveTime = t;
    } else {
      System.err.println("%% Presolve time must be at least 0; " + t + " ignored");
    }
    return i + 1;
  }

  private int handlePresolveRestart(String[] args, int i) {
    double f = Double.parseDouble(args[++i]);
    if (f >= 0) {
      presolveRestart = f;
    } else {
      System.err.println("%% Presolve restart factor must be at least 0; " + f + " ignored");
    }
    return i + 1;
  }

  private int handlePresolveTabling(int i) {
    presolveTabling = true;
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
    randomSeed = seed;
    return i + 1;
  }

  /**
   * Returns the seed given with -r, or 0 when none was given.
   *
   * @return the seed
   */
  public long getRandomSeed() {
    return randomSeed;
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
   * It returns true if the statistics of JaCoP's own components (LCG, presolve, LP, LNS, local
   * search, symmetry, probing, portfolio) are printed as well as the standard FlatZinc ones: with
   * --search-statistics, or with -s and -debug.
   *
   * @return true if the extra statistics are printed, false otherwise.
   */
  public boolean searchStatistics() {
    return statistics && (searchStatistics || debug);
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

  /**
   * It defines whether to run the solver. A model loaded without search keeps every constraint in
   * the loaded store: LCG, on by default, is turned off unless it was asked for.
   */
  public void doNotRunSearch() {
    this.runSearch = false;
    dropDefaultLcg();
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
    // a proof states each explanation by unit propagation, which derives bounds, not domains
    return boundConsistency || proof != null;
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
   * @return true when the model is solved with LCG: --lcg was given, or it is on by default
   */
  public boolean lcg() {
    return lcg;
  }

  /**
   * Turns off LCG that is on by default, for a model it does not support (float variables, more
   * than one solution of a satisfaction problem), so the model is solved as without --lcg. LCG
   * asked for with --lcg stays on; the solver reports why it ignores it.
   */
  void dropDefaultLcg() {
    if (!lcgGiven) {
      lcg = false;
    }
  }

  /**
   * It defines whether the linear relaxation is added as a propagator (--lp).
   *
   * @return false when --lp off was given
   */
  public boolean lp() {
    // LP deductions combine rows, which a proof's unit propagation does not derive
    return lp && proof == null;
  }

  /**
   * The path prefix of the VeriPB proof that --proof asks for: the proof goes to prefix.pbp and the
   * OPB model it is checked against to prefix.opb.
   *
   * @return the prefix, or null without --proof
   */
  public String proof() {
    return proof;
  }

  /**
   * It defines the simplex of the linear relaxation (--lp on, sparse or lazy).
   *
   * @return the simplex
   */
  public LinearRelaxation.Simplex lpSimplex() {
    return lpSimplex;
  }

  /**
   * The number of threads of the parallel portfolio (-p); 1 solves the model in the calling thread.
   *
   * @return the number of threads
   */
  public int threads() {
    return proof == null ? threads : 1;
  }

  /** The portfolio thread this model is solved in, or null outside a portfolio. */
  Portfolio.Worker portfolioWorker() {
    return portfolioWorker;
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
   * It defines the costliest timing class of presolve rules to run (--presolve-level).
   *
   * @return the class, {@link Rule.Timing#EXHAUSTIVE} by default
   */
  public Rule.Timing presolveLevel() {
    return presolveLevel;
  }

  /**
   * It defines the share of the variables a round of presolve rules must change to go back to the
   * fast rules (--presolve-abort).
   *
   * @return the share, {@link Derivation#DEFAULT_ABORT_FACTOR} by default
   */
  public double presolveAbort() {
    return presolveAbort;
  }

  /**
   * It defines when lazy clause generation presolves the root again at a restart
   * (--presolve-restart).
   *
   * @return the share of the integer variables learnt as root facts since the last time, 0 (off) by
   *     default
   */
  public double presolveRestart() {
    return presolveRestart;
  }

  /**
   * It defines the time the rounds of presolve rules may take (--presolve-time).
   *
   * @return the time in milliseconds, or -1 for the default (a twentieth of the time limit)
   */
  public long presolveTime() {
    return presolveTime;
  }

  /**
   * It defines whether presolve replaces small groups of constraints by tables
   * (--presolve-tabling).
   *
   * @return true if presolve tabulates, false by default
   */
  public boolean presolveTabling() {
    return presolveTabling;
  }

  /**
   * It defines what presolve probes at the root (--presolve-probe).
   *
   * @return the probing mode, SAC by default
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
