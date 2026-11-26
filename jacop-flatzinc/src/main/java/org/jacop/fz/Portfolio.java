/*
 * Portfolio.java
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
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.function.Function;
import java.util.function.ObjIntConsumer;
import java.util.regex.Pattern;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.jasat.lcg.SharedClauses;
import org.jacop.jasat.lcg.SharedTree;
import org.jacop.search.free.SharedSolution;

/**
 * A parallel portfolio for FlatZinc models (option -p). Each thread reads the model into a store of
 * its own and solves it with its own settings: the first with the options given, the others with
 * free search and lazy clause generation under other heuristics. The threads share the objective
 * value of the best solution found so far, which bounds the search of the others, and the values of
 * the model's variables in it, which free search threads replay to start their neighbourhoods and
 * values from it. The first thread that finishes its search decides the result: a solution for
 * satisfaction, an optimum, or that there is none.
 *
 * <p>The threads print to their own capture, which tells when a thread has explored its whole
 * search space; the portfolio alone prints solutions and the final status.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
@SuppressWarnings("java:S106") // stdout is the interface of a FlatZinc solver
final class Portfolio {

  private static final String LCG = "--lcg";

  private static final String FREE_CONFIG = "--free-config";

  /**
   * The settings of the threads after the first, in this order; -f and --lcg are given here. The
   * order comes from each setting run alone on 240 hard instances (osolpro
   * benchmarks/portfolio-configs) and is the best one both after --lcg on -f (the default with -f)
   * and after --lcg on (the default without options): LCG branching on the solver's literals solves
   * the most instances the others do not, then free search without LCG, then depth-first search on
   * the annotation without and with LCG. The LCG settings that differ only in core-guided or
   * lower-bound search (lcg, lcg-bb) solve the same instances as one another. Local search (ls) and
   * then default come before free-chs-luby: with -f -p 4 at 600 s, ls in place of free-chs-luby
   * solves 9 of 17 job shops instead of 7, gives cutstock type04 a solution and better objectives
   * to largescheduling and cargo, and is neutral on the wide set (186 of 220 against 185; osolpro
   * benchmarks/ls-default).
   */
  private static final String[][] CONFIGS = {
    {"lcg-lits", LCG, "on", "-f", FREE_CONFIG, "lcg-branching=literals"},
    // local search for half the time, as long as it progresses, then free search from its solution
    {"ls", LCG, "off", "-f", FREE_CONFIG, "ls=0.5,ls-patience=5000"},
    {"default", LCG, "off"},
    {"free-chs-luby", LCG, "off", "-f", FREE_CONFIG, "heuristic=chs,restarts=luby,scale=100"},
    {"lcg-fixed", LCG, "on"},
    {"free-afc", LCG, "off", "-f", FREE_CONFIG, "heuristic=afc,phase=0"},
    {"free", LCG, "off", "-f"},
    {"lcg", LCG, "on", "-f"},
    {"lcg-bb", LCG, "on", "-f", FREE_CONFIG, "lcg-core=0,lcg-lb=0"},
    {"free-cacd", LCG, "off", "-f", FREE_CONFIG, "heuristic=cacd"},
    {"free-luby-keep", LCG, "off", "-f", FREE_CONFIG, "restarts=luby,scale=50,flush=0"}
  };

  /** The most threads the portfolio uses: the options given and each setting above. */
  static final int MAX_THREADS = CONFIGS.length + 1;

  /**
   * The setting of the threads that divide one search tree (option {@code --free-config
   * portfolio-split=<threads>}): LCG free search as branch and bound, each thread under the cube of
   * the tree it took; see {@link SharedTree}. The thread joins the tree with {@code
   * lcg-tree-split=1}, not with {@code lcg-split}, which is the term limit of long linear
   * constraints: {@code lcg-split=1} split every linear constraint of two terms or more into
   * blocks.
   */
  static final String[] SPLIT_SETTING = {
    "lcg-split", LCG, "on", "-f", FREE_CONFIG, "lcg-tree-split=1,lcg-core=0,lcg-lb=0"
  };

  /**
   * The setting of the threads that divide one depth-first search on the annotation by work
   * stealing (option {@code --free-config portfolio-dfs-split=<threads>}, 2 by default with free
   * search and at least 4 threads, 0 turns it off); see {@link DfsSplit}. Symmetry breaking is off:
   * its constraints may have variables with no name in the model, which a cube cannot name, and
   * then no thread could join the tree and each would search all of it.
   */
  static final String[] DFS_SPLIT_SETTING = {
    "dfs-split", LCG, "off", "--symmetry", "off", FREE_CONFIG, "dfs-split=1"
  };

  /** The name of the thread of {@link #boundSetting}. */
  static final String BOUND_THREAD = "lcg-bisect";

  private static final String SEARCH_COMPLETE = "==========";

  /** The value shared for a variable that is not fixed in a solution. */
  static final int UNKNOWN = Integer.MIN_VALUE;

  /** How long after the time-out the portfolio answers when a thread has not stopped yet. */
  private static final long STOP_MARGIN_MILLIS = 300;

  /** How long the portfolio waits for its stopped threads to end after printing the answer. */
  private static final long JOIN_MILLIS = 10_000;

  // the statistics of a thread printed per thread with --search-statistics (the solver's own keys)
  private static final List<String> WORKER_STATISTICS =
      List.of(
          "solveTime",
          "nodes",
          "failures",
          "restarts",
          "propagations",
          "solutions",
          "objective",
          "lcgSatConflicts",
          "lcgSatPropagations",
          "lcgLearntAvg",
          "lcgSlowConflicts",
          "lnsRuns",
          "lnsImproved");

  private static final String UNSATISFIABLE = "=====UNSATISFIABLE=====";

  // floats are solved in one thread: their precision and derivatives are kept in static fields
  private static final Pattern FLOAT_VAR = Pattern.compile("\\bvar\\s+(float\\b|-?\\d+\\.\\d)");

  private static final ThreadLocal<OutputStream> CAPTURE = new ThreadLocal<>();

  private final Options options;
  private final List<Worker> workers = new ArrayList<>();
  // learnt clauses and root bounds of the LCG threads
  private final SharedClauses sharedClauses = new SharedClauses();
  // the search tree the threads of SPLIT_SETTING divide among themselves
  private final SharedTree sharedTree = new SharedTree();
  // the search tree the threads of DFS_SPLIT_SETTING divide among themselves
  private final SharedTree dfsTree = new SharedTree();
  private final Object lock = new Object();
  // where the portfolio prints: stdout as it was when the portfolio started
  private PrintStream stdout = System.out;
  // stdout while the portfolio runs, given back by the last thread to end if it outlives run()
  private PrintStream dispatch;
  private boolean restorePending;
  // ends a command-line run that is still going after its time-out
  private Thread watchdog;

  // the objective value (of the minimised cost variable) of the best solution, read by all threads
  private volatile int bestCost = Integer.MAX_VALUE;
  private String bestSolution;
  // the values of the model's variables in the best solution, by name; UNKNOWN when not fixed
  private String[] bestNames;
  private int[] bestValues;
  private Worker bestWorker;
  // the times a thread replayed the best solution
  private int imports;
  private boolean optimisation;
  private boolean maximisation;
  private int solutions;
  private int running;
  // the threads that read and solved the model, or showed it unsatisfiable (exit status 0)
  private int accepted;
  private boolean finished;
  private boolean complete;
  // the answer has been printed, by run() or at shutdown
  private boolean printed;
  // every thread rejected the model (an error in it, or one JaCoP does not support): the run ends
  // as one thread does, with no status and exit status 1
  private boolean rejected;
  // the error lines the threads printed, each printed once for all of them
  private final Set<String> errors = ConcurrentHashMap.newKeySet();
  // the factor the threads divided the objective by (ObjectiveScaling)
  private long objectiveScale = 1;

  // the best solution and bound of all threads, for --gap and the objectiveBound statistic
  private ObjectiveGap gap;
  // a thread's bound holds only for the restarts of relax and reconstruct or on_restart
  private boolean inexactBound;

  Portfolio(Options options) {
    this.options = options;
  }

  /** Whether the portfolio has ended with its search complete: its best solution is optimal. */
  boolean provedComplete() {
    synchronized (lock) {
      return finished && complete;
    }
  }

  /**
   * Returns why the model cannot be solved by a portfolio, or null when it can.
   *
   * @param options the options given
   * @return the reason, or null
   */
  static String unsupported(Options options) {
    if (options.getNumberSolutions() != -1 && !options.getAll()) {
      return "a number of solutions (-n) is asked for";
    }
    if (!options.getOutputFilename().isEmpty()) {
      return "the output goes to a file (-o)";
    }
    String model;
    try {
      model = Files.readString(Path.of(options.getFileName()), StandardCharsets.ISO_8859_1);
    } catch (IOException _) {
      return "the model cannot be read";
    }
    if (FLOAT_VAR.matcher(model).find()) {
      return "the model has float variables";
    }
    if (options.getAll() && isSatisfaction(model)) {
      return "all solutions are asked for";
    }
    return null;
  }

  /**
   * Whether an error line should be printed: outside a portfolio always, in a thread of a portfolio
   * only when no thread of it printed the same line, since every thread reads the same model and
   * reports the same error in it.
   *
   * @param line the line
   * @return true to print it
   */
  static boolean firstReport(String line) {
    return !(CAPTURE.get() instanceof StatusCapture c) || c.errors == null || c.errors.add(line);
  }

  private static boolean isSatisfaction(String model) {
    int solve = model.lastIndexOf("solve");
    return solve >= 0 && model.indexOf("satisfy", solve) >= 0;
  }

  /**
   * Starts the watchdog of a command-line run: when the run is still going after the given delay,
   * it prints the answer as at the time-out (the best solution, or {@code =====UNKNOWN=====})
   * unless it is out already, and runs halt. The portfolio answers at its time-out itself once its
   * threads have started; the watchdog ends a run that is still reading the model then (a large
   * file on a slow disk: road_33, 86 MB, answered 1.9 s after -t 2000 from Portfolio.readModel).
   *
   * @param delayMillis when to fire, from now
   * @param halt how to end the run
   */
  void startWatchdog(long delayMillis, Runnable halt) {
    PrintStream out = System.out;
    long start = System.currentTimeMillis();
    watchdog =
        Thread.ofVirtual()
            .name("jacop-portfolio-time-limit")
            .unstarted(
                () -> {
                  try {
                    Thread.sleep(delayMillis);
                  } catch (InterruptedException _) {
                    // cancelled: the run ended on its own
                    Thread.currentThread().interrupt();
                    return;
                  }
                  timeLimit(out, start, halt);
                });
    watchdog.start();
  }

  /** Stops the watchdog, if any: the run has ended. */
  void cancelWatchdog() {
    if (watchdog != null) {
      watchdog.interrupt();
    }
  }

  /**
   * What the watchdog does when it fires: prints the answer as at the time-out unless it was
   * printed already, and then runs halt; it does nothing once the answer is out, since the run then
   * ends on its own.
   *
   * @param out where to print
   * @param start when the run started, for the solveTime statistic
   * @param halt how to end the run
   */
  void timeLimit(PrintStream out, long start, Runnable halt) {
    synchronized (lock) {
      if (printed) {
        return;
      }
      // no solution of a thread is taken from now on
      finished = true;
      lock.notifyAll();
    }
    if (printResult(out, true, start)) {
      synchronized (lock) {
        halt.run();
      }
    }
  }

  /**
   * Solves the model with a portfolio of threads and prints the result as one thread would.
   *
   * @param args the command line arguments
   * @return the exit status: 0 when the threads ran, 1 when none could solve the model
   */
  int run(String[] args) {
    stdout = System.out;
    dispatch = new PrintStream(new Dispatch(stdout), true, stdout.charset());
    System.setOut(dispatch);
    try {
      return run(args, stdout);
    } finally {
      // a thread that has not ended within the wait prints nothing after the run returns: in
      // process, its status line would land in the output of whatever runs next
      for (Worker w : workers) {
        w.closeOutput();
      }
      synchronized (lock) {
        // a thread still running would print its own status lines into stdout
        restorePending = running > 0;
        if (!restorePending) {
          restoreStdout();
        }
      }
    }
  }

  private void restoreStdout() {
    if (System.out == dispatch) {
      System.setOut(stdout);
    }
  }

  private int run(String[] args, PrintStream out) {
    long start = System.currentTimeMillis();
    long timeOutAt = timeOutAt(options, start);
    List<String> base = baseArguments(args);
    int threads = Math.min(options.threads(), MAX_THREADS);
    boolean satisfaction = isSatisfaction(readModel(options));
    SimpleNode model = "0".equals(options.freeConfig("portfolio-one-parse", "1")) ? null : parse();
    if (model == null && options.timeOutPassed()) {
      // the reading stopped at the time-out, and each thread would read the model again only to
      // stop there too
      printResult(out, true, start);
      return 0;
    }
    // the threads that divide one search tree, in place of the last settings
    int split = Math.min(threads, Integer.parseInt(options.freeConfig("portfolio-split", "0")));
    if (split < 2) {
      split = 0;
    }
    // free search with 4 threads or more gives two threads to one split CP tree by default: on the
    // wide set at 600 s (-f -p 4) it solved 203 instances against 200 with the plain settings
    // (not next to LCG split threads)
    String dfsDefault = options.freeSearch() && threads >= 4 && split == 0 ? "2" : "0";
    int dfsSplit =
        Math.min(
            threads - split,
            Integer.parseInt(options.freeConfig("portfolio-dfs-split", dfsDefault)));
    if (dfsSplit < 2) {
      dfsSplit = 0;
    }
    split += dfsSplit;
    List<String> splitFlags = Arrays.asList(SPLIT_SETTING).subList(1, SPLIT_SETTING.length);
    List<String> dfsFlags = Arrays.asList(DFS_SPLIT_SETTING).subList(1, DFS_SPLIT_SETTING.length);
    if (split < threads) {
      workers.add(new Worker("given", arguments(base, List.of(), false)));
    }
    String given = search(options.lcg(), options.freeSearch(), options.freeConfig, satisfaction);
    double bisect = Double.parseDouble(options.freeConfig("portfolio-bisect", "0"));
    int others = Math.max(0, threads - 1 - split);
    for (String[] config : settings(given, others, satisfaction, bisect)) {
      List<String> flags = Arrays.asList(config).subList(1, config.length);
      workers.add(new Worker(config[0], arguments(base, flags, true)));
    }
    for (int k = 0; k < dfsSplit; k++) {
      workers.add(new Worker(DFS_SPLIT_SETTING[0] + k, arguments(base, dfsFlags, true)));
    }
    for (int k = 0; k < split - dfsSplit; k++) {
      workers.add(new Worker(SPLIT_SETTING[0] + k, arguments(base, splitFlags, true)));
    }
    String file = args[args.length - 1];
    synchronized (lock) {
      running = workers.size();
    }
    for (Worker w : workers) {
      Thread t = new Thread(() -> w.run(file, model), "jacop-portfolio-" + w.name);
      t.setDaemon(true);
      w.thread = t;
      t.start();
    }
    // a run killed before it answers (SIGTERM) prints the best solution, as one thread does
    Thread atShutdown = new Thread(() -> printAtShutdown(out, start), "jacop-portfolio-exit");
    if (options.getStatistics()) {
      Runtime.getRuntime().addShutdownHook(atShutdown);
    }
    boolean timedOut = await(timeOutAt);
    for (Worker w : workers) {
      w.stop();
    }
    printResult(out, timedOut, start);
    if (options.getStatistics()) {
      try {
        Runtime.getRuntime().removeShutdownHook(atShutdown);
      } catch (IllegalStateException _) {
        // the JVM is shutting down: the hook finds the answer printed
      }
    }
    List<Thread> threadsToJoin = new ArrayList<>();
    for (Worker w : workers) {
      threadsToJoin.add(w.thread);
    }
    join(threadsToJoin, timeOutAt);
    synchronized (lock) {
      // under the lock, so that the watchdog does not halt the run in the middle of the block
      if (options.searchStatistics()) {
        out.print(workerStatistics());
        out.flush();
      }
      return rejected ? 1 : 0;
    }
  }

  /**
   * The statistics of each thread, as {@code portfolioThread.<name>.<key>} lines in a block of
   * their own after the answer, so that a slow or idle thread of a portfolio can be told apart: the
   * keys of {@link #WORKER_STATISTICS} the thread printed last, and how it ended. A thread that has
   * not ended within the wait after the answer shows what it printed so far.
   *
   * @return the block, empty when no thread printed any
   */
  private String workerStatistics() {
    StringBuilder s = new StringBuilder();
    for (Worker w : workers) {
      Map<String, String> stats = w.capture.statistics();
      String prefix = "%%%mzn-stat: portfolioThread." + w.name + ".";
      s.append(prefix).append("ended=").append(w.ending()).append('\n');
      for (String key : WORKER_STATISTICS) {
        String value = stats.get(key);
        if (value != null) {
          s.append(prefix).append(key).append('=').append(value).append('\n');
        }
      }
    }
    if (!s.isEmpty()) {
      s.append("%%%mzn-stat-end\n");
    }
    return s.toString();
  }

  /**
   * Waits for the stopped threads to end after the answer is printed. The threads stop within
   * milliseconds in search, later when stopped while reading the model; a thread in a start-up
   * phase that does not look at the time-out is not waited for past it: the threads are daemons,
   * and the answer is out.
   *
   * @param threads the threads
   * @param timeOutAt when the time-out passes (System.currentTimeMillis()), 0 without one
   */
  static void join(List<Thread> threads, long timeOutAt) {
    long joinDeadline = System.currentTimeMillis() + JOIN_MILLIS;
    if (timeOutAt > 0) {
      joinDeadline =
          Math.min(
              joinDeadline, Math.max(System.currentTimeMillis(), timeOutAt) + STOP_MARGIN_MILLIS);
    }
    for (Thread t : threads) {
      try {
        t.join(Math.max(1, joinDeadline - System.currentTimeMillis()));
      } catch (InterruptedException _) {
        Thread.currentThread().interrupt();
        break;
      }
    }
  }

  /**
   * When the time-out of the run passes. It counts from the start of the run, as in one thread; it
   * counted from the start of the portfolio, and the portfolio answered 2 s after it.
   *
   * @param options the options given
   * @param now the current time (System.currentTimeMillis())
   * @return the time, or 0 without a time-out
   */
  static long timeOutAt(Options options, long now) {
    return options.getTimeOut() > 0 ? now + options.getRemainingTimeOut() : 0;
  }

  /**
   * Waits until a thread finishes its search or all threads end. Returns true on a time-out.
   *
   * @param timeOutAt when the time-out passes (System.currentTimeMillis()), 0 without one
   */
  private boolean await(long timeOutAt) {
    synchronized (lock) {
      while (!finished && running > 0) {
        long wait = 0;
        if (timeOutAt > 0) {
          // the threads stop at the time-out themselves; a thread that overruns it does not hold
          // back the answer, which MiniZinc takes only up to a second after the time-out
          wait = timeOutAt + STOP_MARGIN_MILLIS - System.currentTimeMillis();
          if (wait <= 0) {
            finished = true;
            return true;
          }
        }
        try {
          lock.wait(wait);
        } catch (InterruptedException _) {
          Thread.currentThread().interrupt();
          finished = true;
          return false;
        }
      }
      finished = true;
      return !complete && timeOutAt > 0 && System.currentTimeMillis() >= timeOutAt;
    }
  }

  /**
   * What the shutdown hook of a run with statistics does when the run is killed before it answers
   * (SIGTERM): prints the answer as at the time-out, unless it was printed already.
   *
   * @param out where to print
   * @param start when the run started, for the solveTime statistic
   */
  void printAtShutdown(PrintStream out, long start) {
    printResult(out, true, start);
  }

  // prints the answer unless it was printed already; returns whether it printed it now
  private boolean printResult(PrintStream out, boolean timedOut, long start) {
    StringBuilder s = new StringBuilder();
    synchronized (lock) {
      if (printed) {
        return false;
      }
      printed = true;
      // no solution of a thread is taken from now on: under -a it would be printed after the
      // answer. The shutdown hook prints while the threads still run
      finished = true;
      lock.notifyAll();
      rejected = !workers.isEmpty() && running == 0 && accepted == 0 && bestSolution == null;
      // each thread reported its error: a rejected model has no status, as in one thread
      if (!rejected) {
        status(s, timedOut);
      }
      if (options.getStatistics()) {
        if (options.searchStatistics()) {
          s.append("%%%mzn-stat: portfolioThreads=").append(workers.size()).append('\n');
          if (bestWorker != null) {
            s.append("%%%mzn-stat: portfolioBest=").append(bestWorker.name).append('\n');
          }
          if (imports > 0) {
            s.append("%%%mzn-stat: portfolioImports=").append(imports).append('\n');
          }
          if (dfsTree.joined() > 0) {
            s.append("%%%mzn-stat: portfolioDfsSplitThreads=")
                .append(dfsTree.joined())
                .append("\n%%%mzn-stat: portfolioDfsSplits=")
                .append(dfsTree.splits())
                .append("\n%%%mzn-stat: portfolioDfsCubesClosed=")
                .append(dfsTree.closedCubes())
                .append("\n%%%mzn-stat: portfolioDfsSplitWaitMillis=")
                .append(dfsTree.waitedMillis())
                .append('\n');
          }
          if (sharedTree.joined() > 0) {
            s.append("%%%mzn-stat: portfolioSplitThreads=")
                .append(sharedTree.joined())
                .append("\n%%%mzn-stat: portfolioSplits=")
                .append(sharedTree.splits())
                .append("\n%%%mzn-stat: portfolioCubesClosed=")
                .append(sharedTree.closedCubes())
                .append("\n%%%mzn-stat: portfolioSplitWaitMillis=")
                .append(sharedTree.waitedMillis())
                .append('\n');
          }
          if (sharedClauses.size() > 0) {
            s.append("%%%mzn-stat: portfolioSharedClauses=")
                .append(sharedClauses.size())
                .append('\n');
          }
        }
        s.append("%%%mzn-stat: solutions=").append(solutions).append('\n');
        if (optimisation && bestSolution != null) {
          s.append("%%%mzn-stat: objective=").append(objective(bestCost)).append('\n');
        }
        s.append("%%%mzn-stat: solveTime=")
            .append((System.currentTimeMillis() - start) / 1000.0)
            .append("\n%%%mzn-stat-end\n");
      }
    }
    out.print(s);
    out.flush();
    return true;
  }

  // the best solution (without -a) and the final status, as one thread prints them
  private void status(StringBuilder s, boolean timedOut) {
    if (bestSolution != null) {
      if (!options.getAll()) {
        s.append(bestSolution);
      }
      if (complete && optimisation) {
        if (gap != null) {
          gap.optimal(); // a thread proved the best solution optimal
        }
        s.append(SEARCH_COMPLETE).append('\n');
      } else if (timedOut) {
        s.append("%% =====TIME-OUT=====\n");
      }
    } else if (complete) {
      s.append(UNSATISFIABLE).append('\n');
    } else {
      s.append("=====UNKNOWN=====\n");
      if (timedOut) {
        s.append("%% =====TIME-OUT=====\n");
      }
    }
  }

  // the cost variable is the negated objective under maximisation, and it may hold the objective
  // divided by a scale (ObjectiveScaling)
  private long objective(int cost) {
    return (maximisation ? -(long) cost : cost) * objectiveScale;
  }

  /**
   * The options given without those the portfolio handles itself: the number of threads,
   * statistics, the seed (already set), and the model file.
   */
  private static List<String> baseArguments(String[] args) {
    List<String> base = new ArrayList<>();
    for (int i = 0; i < args.length - 1; i++) {
      switch (args[i]) {
        case "-p", "--parallel", "-r", "--random-seed", "-t", "--time-out" -> i++;
        case "-s", "--statistics", "-a", "--all", "--all-solutions" -> {
          // printed by the portfolio
        }
        default -> base.add(args[i]);
      }
    }
    return base;
  }

  /** The arguments of a thread: the options given, with its own search settings if any. */
  private List<String> arguments(List<String> base, List<String> flags, boolean ownSearch) {
    List<String> a = new ArrayList<>();
    for (int i = 0; i < base.size(); i++) {
      String arg = base.get(i);
      if (!ownSearch || !isSearchFlag(arg)) {
        a.add(arg);
      } else if (LCG.equals(arg) && i + 1 < base.size() && isOnOff(base.get(i + 1))) {
        i++;
      }
    }
    a.addAll(flags);
    if (options.searchStatistics() && !a.contains("--search-statistics")) {
      // the thread prints its statistics into its capture, for workerStatistics(); -s -v leaves
      // only -v to the thread
      a.add("--search-statistics");
    }
    if (options.getTimeOut() > 0) {
      a.add("-t");
      a.add(Integer.toString(options.getRemainingTimeOut()));
    }
    return a;
  }

  private static boolean isOnOff(String arg) {
    return "on".equals(arg) || "off".equals(arg);
  }

  private static boolean isSearchFlag(String arg) {
    return "-f".equals(arg) || "--free-search".equals(arg) || LCG.equals(arg);
  }

  /**
   * The settings of the threads after the first: the first ones of {@link #CONFIGS} that run a
   * search no earlier thread runs on a model of this kind.
   *
   * @param given the search of the first thread, as {@link #search(List, boolean)} gives it
   * @param count how many settings at most
   * @param satisfaction whether the model has no objective
   * @return the settings, in the order of {@link #CONFIGS}
   */
  static List<String[]> settings(String given, int count, boolean satisfaction) {
    Set<String> searches = new HashSet<>();
    searches.add(given);
    List<String[]> chosen = new ArrayList<>();
    for (String[] config : CONFIGS) {
      if (chosen.size() >= count) {
        break;
      }
      if (searches.add(search(Arrays.asList(config).subList(1, config.length), satisfaction))) {
        chosen.add(config);
      }
    }
    return chosen;
  }

  /**
   * The settings of the threads after the first, as {@link #settings(String, int, boolean)} gives
   * them, with the bound thread of {@link #boundSetting} first when bisect is above 0 and the model
   * has an objective; it takes the place of the last setting.
   *
   * @param given the search of the first thread
   * @param count how many settings at most
   * @param satisfaction whether the model has no objective
   * @param bisect the relative gap of the bound thread, 0 for none
   * @return the settings
   */
  static List<String[]> settings(String given, int count, boolean satisfaction, double bisect) {
    List<String[]> chosen = settings(given, count, satisfaction);
    if (bisect > 0 && !satisfaction && count > 0) {
      chosen.add(0, boundSetting(bisect));
      if (chosen.size() > count) {
        chosen.remove(chosen.size() - 1);
      }
    }
    return chosen;
  }

  /**
   * The setting of a thread that works on the objective's lower bound (option {@code --free-config
   * portfolio-bisect=<gap>}): LCG free search by dichotomic probes of the objective between its
   * lower bound and the portfolio's best solution, until the relative gap is within the given
   * share, then branch and bound. The thread proves bounds for the others, which take them through
   * the shared clauses and the portfolio's bound; it has no core-guided phase, which the thread
   * with the options given (LCG free search by default) runs already. It shares no clauses: with
   * its clauses (learnt next to probe assumptions) jp-encoding and community-detection lost their
   * proofs at 240 s in the other threads; its bounds still reach the portfolio's objective bound.
   *
   * @param gap the relative gap, a fraction
   * @return the setting, its name first
   */
  static String[] boundSetting(double gap) {
    return new String[] {
      BOUND_THREAD,
      "--lcg",
      "on",
      "-f",
      "--free-config",
      "lcg-bisect=" + gap + ",lcg-core=0,share-clauses=0"
    };
  }

  /**
   * The search a setting runs on a model of this kind, as a key: two settings with the same key
   * would run the same search. Without an objective the settings of the objective (core-guided and
   * lower-bound search, LNS, probes) change nothing, so lcg-bb is lcg on a satisfaction model.
   */
  static String search(List<String> flags, boolean satisfaction) {
    Map<String, String> config = new TreeMap<>();
    int i = flags.indexOf(FREE_CONFIG);
    if (i >= 0) {
      for (String kv : flags.get(i + 1).split(",")) {
        String[] p = kv.split("=", 2);
        config.put(p[0].strip(), p.length > 1 ? p[1].strip() : "");
      }
    }
    int lcg = flags.indexOf(LCG);
    boolean on = lcg >= 0 && (lcg + 1 == flags.size() || !"off".equals(flags.get(lcg + 1)));
    return search(on, flags.contains("-f"), config, satisfaction);
  }

  private static String search(
      boolean lcg, boolean free, Map<String, String> config, boolean satisfaction) {
    Map<String, String> c = new TreeMap<>(config);
    // the settings of the portfolio's layout are not the search of a thread
    c.keySet().removeIf(k -> k.startsWith("portfolio-"));
    if (satisfaction) {
      c.keySet().removeIf(Portfolio::objectiveSetting);
    }
    return (lcg ? "lcg " : "") + (free ? "free " : "") + c;
  }

  private static boolean objectiveSetting(String key) {
    return key.startsWith("lcg-core")
        || key.startsWith("lcg-lb")
        || "lcg-shave".equals(key)
        || "lcg-bisect".equals(key)
        || key.startsWith("lns")
        || key.startsWith("probe");
  }

  /**
   * Reads the model once for all threads, which build their stores from the tree it gives; it is
   * about a third of their start-up. Each thread builds from a copy of its own (Parser.build),
   * since the front end rewrites constraint items in place, and drops the copy once its model is
   * built. A model that does not parse gives null, and each thread reads it again and reports the
   * error as one thread does.
   */
  private SimpleNode parse() {
    try (FileInputStream in = new FileInputStream(options.getFileName())) {
      Parser parser = new Parser(in);
      parser.setOptions(options);
      return parser.parseModel();
    } catch (IOException | ParseException | TokenMgrError | RuntimeException _) {
      return null;
    }
  }

  private static String readModel(Options options) {
    try {
      return Files.readString(Path.of(options.getFileName()), StandardCharsets.ISO_8859_1);
    } catch (IOException _) {
      return "";
    }
  }

  /**
   * Takes a solution of a thread: the first one for satisfaction, which ends the search, and for
   * optimisation each one better than the best so far.
   */
  private void solution(
      Worker w, String text, Integer cost, boolean maximise, String[] names, int[] values) {
    synchronized (lock) {
      if (finished) {
        return;
      }
      if (cost == null) {
        bestSolution = text;
        bestWorker = w;
        solutions++;
        finished = true;
        lock.notifyAll();
      } else {
        if (cost >= bestCost) {
          return;
        }
        if (gap(maximise).solution(cost) || provedByBound()) {
          gapReached();
        }
        optimisation = true;
        maximisation = maximise;
        bestCost = cost;
        bestSolution = text;
        bestNames = names;
        bestValues = values;
        bestWorker = w;
        solutions++;
      }
      if (options.getAll()) {
        stdout.print(text);
        stdout.flush();
        // -n k: the run ends after k solutions, as in one thread; each thread counted only its own
        if (solutions >= options.getNumberSolutions()) {
          finished = true;
          lock.notifyAll();
        }
      }
    }
  }

  private ObjectiveGap gap(boolean maximise) {
    if (gap == null) {
      PrintStream out = stdout;
      gap =
          new ObjectiveGap(
              options.gap(),
              maximise,
              options.searchStatistics() ? line -> printBound(out, line) : null);
      gap.scale(objectiveScale);
    }
    return gap;
  }

  // a bound at the best solution proves it optimal, with or without --gap
  private boolean provedByBound() {
    return !inexactBound && gap.proved();
  }

  // the best solution is within --gap of the bound, or at a bound, which ends the search
  private void gapReached() {
    synchronized (lock) {
      complete = provedByBound();
      finished = true;
      lock.notifyAll();
    }
  }

  private static void printBound(PrintStream out, String line) {
    out.println(line);
    out.flush();
  }

  /** One thread of the portfolio, as seen by the model it solves. */
  final class Worker {

    final String name;
    private final List<String> args;
    private final List<Runnable> stops = new CopyOnWriteArrayList<>();
    private volatile boolean stopped;
    // held while the thread prints its answer or an error; closed once the portfolio has returned
    private final Object output = new Object();
    private boolean outputClosed;
    private final List<Runnable> closes = new CopyOnWriteArrayList<>();
    private Thread thread;
    // what the thread printed, set before the thread starts
    private final StatusCapture capture = new StatusCapture();
    private volatile boolean ended;

    Worker(String name, List<String> args) {
      this.name = name;
      this.args = args;
    }

    private void run(String file, SimpleNode model) {
      capture.errors = errors;
      CAPTURE.set(capture);
      boolean ran = false;
      try {
        List<String> a = new ArrayList<>(args);
        a.add(file);
        Options opt = new Options(a.toArray(new String[0]));
        opt.portfolioWorker = this;
        if (model != null) {
          ran = Fz2jacop.solveInPortfolio(opt, model) == 0;
        } else {
          try (FileInputStream in = opt.getFile()) {
            ran = Fz2jacop.solveInPortfolio(opt, in) == 0;
          }
        }
      } catch (IOException | RuntimeException e) {
        // the same error in every thread is reported by the first
        print(
            () -> {
              if (firstReport(e.toString())) {
                FzConsole.printlnErr("%% portfolio thread " + name + " stopped: " + e);
              }
            });
      } finally {
        CAPTURE.remove();
        ended = true;
        ended(ran, ran && !stopped && capture.complete);
      }
    }

    private void ended(boolean ran, boolean searchComplete) {
      synchronized (lock) {
        running--;
        if (ran) {
          accepted++;
        }
        if (searchComplete && !finished) {
          complete = true;
          finished = true;
        }
        if (restorePending && running == 0) {
          restoreStdout();
        }
        lock.notifyAll();
      }
    }

    /**
     * The objective value of the best solution of the portfolio, as a value of the minimised cost
     * variable; {@link Integer#MAX_VALUE} while there is none.
     *
     * @return the bound
     */
    int sharedBound() {
      return bestCost;
    }

    /**
     * Reports a solution.
     *
     * @param text the solution as printed
     * @param cost the value of the minimised cost variable, or null for satisfaction
     * @param maximise whether the cost variable is the negated objective
     * @param names the names of the model's variables, an array the thread keeps from one solution
     *     to the next
     * @param values their values in the solution, {@link #UNKNOWN} for a variable not fixed
     */
    void solution(String text, Integer cost, boolean maximise, String[] names, int[] values) {
      Portfolio.this.solution(this, text, cost, maximise, names, values);
    }

    /**
     * Sets the factor the objective was divided by in the model of the threads (ObjectiveScaling),
     * which every thread finds the same.
     *
     * @param factor the factor
     */
    void objectiveScale(long factor) {
      synchronized (lock) {
        objectiveScale = factor;
        if (gap != null) {
          gap.scale(factor);
        }
      }
    }

    /**
     * Reports a bound this thread proved: no solution better than the best one of the portfolio has
     * a smaller value of the minimised cost variable.
     *
     * @param lower the bound
     * @param maximise whether the cost variable is the negated objective
     * @param exact false for a bound of the restarts of relax and reconstruct or on_restart, which
     *     ends the search at --gap but never proves a solution optimal
     */
    void bound(long lower, boolean maximise, boolean exact) {
      synchronized (lock) {
        inexactBound |= !exact;
        if (!finished && (gap(maximise).bound(lower) || provedByBound())) {
          gapReached();
        }
      }
    }

    /**
     * The clauses the LCG threads share.
     *
     * @return the clauses
     */
    SharedTree sharedTree() {
      return sharedTree;
    }

    SharedTree dfsTree() {
      return dfsTree;
    }

    boolean isStopped() {
      return stopped;
    }

    SharedClauses sharedClauses() {
      return sharedClauses;
    }

    /**
     * Returns the best solution of the portfolio as a solution for this thread to replay.
     *
     * @param variable the variable of this thread's store with a name of the model, or null
     * @return the shared solution
     */
    SharedSolution sharedSolution(Function<String, IntVar> variable) {
      return new Replay(variable);
    }

    /**
     * Registers how to stop the search of this thread; it runs at once when the thread is stopped
     * already.
     *
     * @param stop the action, which may run more than once
     */
    void onStop(Runnable stop) {
      stops.add(stop);
      if (stopped) {
        stop.run();
      }
    }

    /**
     * Whether the portfolio has stopped this thread.
     *
     * @return true once stopped
     */
    boolean stopped() {
      return stopped;
    }

    /**
     * How the thread ended, as the statistics give it: complete (its search proved the answer),
     * stopped (by the portfolio, which had its answer), done (it ended on its own, for example at
     * its time-out) or running (it had not ended when the statistics were printed).
     */
    private String ending() {
      if (!ended) {
        return "running";
      }
      if (capture.complete) {
        return "complete";
      }
      return stopped ? "stopped" : "done";
    }

    /**
     * Prints what the thread prints at the end of its run (its answer, its statistics or an error)
     * unless the portfolio has returned already.
     *
     * @param print what prints
     * @return true if it printed
     */
    boolean print(Runnable print) {
      synchronized (output) {
        if (outputClosed) {
          return false;
        }
        print.run();
        return true;
      }
    }

    /**
     * Registers how to close the output of the model this thread solves; it runs at once when the
     * output is closed already.
     *
     * @param close the action, which may run more than once
     */
    void onClose(Runnable close) {
      closes.add(close);
      boolean closed;
      synchronized (output) {
        closed = outputClosed;
      }
      if (closed) {
        close.run();
      }
    }

    // the portfolio has returned: what the thread prints from now on goes nowhere
    private void closeOutput() {
      synchronized (output) {
        outputClosed = true;
      }
      for (Runnable r : closes) {
        r.run();
      }
    }

    private void stop() {
      stopped = true;
      for (Runnable r : stops) {
        r.run();
      }
    }

    /** The best solution of the portfolio, fixed on the variables of this thread's store. */
    private final class Replay implements SharedSolution {

      private final Function<String, IntVar> variable;
      // the variables of this thread for the names of the last solution replayed
      private String[] names;
      private IntVar[] vars;

      Replay(Function<String, IntVar> variable) {
        this.variable = variable;
      }

      @Override
      public int objective() {
        return bestCost;
      }

      @Override
      public void impose(Store store) {
        synchronized (lock) {
          imports++;
        }
        values(
            (x, v) -> {
              if (!x.singleton() && x.domain.contains(v)) {
                x.domain.inValue(store.level, x, v);
              }
            });
      }

      @Override
      public void values(ObjIntConsumer<IntVar> action) {
        String[] n;
        int[] values;
        synchronized (lock) {
          n = bestNames;
          values = bestValues;
        }
        if (n == null) {
          return;
        }
        if (n != names) {
          names = n;
          vars = new IntVar[n.length];
          for (int i = 0; i < n.length; i++) {
            vars[i] = variable.apply(n[i]);
          }
        }
        for (int i = 0; i < vars.length; i++) {
          if (vars[i] != null && values[i] != UNKNOWN) {
            action.accept(vars[i], values[i]);
          }
        }
      }
    }
  }

  /** Sends the output of portfolio threads to their capture, and that of other threads on. */
  private static final class Dispatch extends OutputStream {

    private final OutputStream out;

    Dispatch(OutputStream out) {
      this.out = out;
    }

    @Override
    public void write(int b) throws IOException {
      target().write(b);
    }

    @Override
    public void write(byte[] b, int off, int len) throws IOException {
      target().write(b, off, len);
    }

    @Override
    public void flush() throws IOException {
      target().flush();
    }

    private OutputStream target() {
      OutputStream t = CAPTURE.get();
      return t == null ? out : t;
    }
  }

  /**
   * The output of a thread: the line that says its search is complete, and the statistics lines of
   * {@link #WORKER_STATISTICS}, the last value of each.
   */
  private static final class StatusCapture extends OutputStream {

    private static final String STAT = "%%%mzn-stat: ";
    // longer than any status line and any statistics line kept
    private static final int LINE_LIMIT = 128;

    private final StringBuilder line = new StringBuilder();
    private final Map<String, String> statistics = new HashMap<>();
    volatile boolean complete;
    // the error lines of all threads of the portfolio
    Set<String> errors;

    @Override
    public void write(int b) {
      if (b == '\n') {
        String l = line.toString().strip();
        if (SEARCH_COMPLETE.equals(l) || UNSATISFIABLE.equals(l)) {
          complete = true;
        } else if (l.startsWith(STAT)) {
          statistic(l);
        }
        line.setLength(0);
      } else if (line.length() < LINE_LIMIT) {
        line.append((char) b);
      }
    }

    private void statistic(String l) {
      int eq = l.indexOf('=');
      if (eq < 0 || line.length() >= LINE_LIMIT) {
        return;
      }
      String key = l.substring(STAT.length(), eq);
      if (WORKER_STATISTICS.contains(key)) {
        synchronized (statistics) {
          statistics.put(key, l.substring(eq + 1));
        }
      }
    }

    /** A copy of the statistics kept so far. */
    Map<String, String> statistics() {
      synchronized (statistics) {
        return new HashMap<>(statistics);
      }
    }

    @Override
    public void write(byte[] b, int off, int len) {
      for (int i = off; i < off + len; i++) {
        write(b[i]);
      }
    }
  }
}
