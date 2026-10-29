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
import java.util.List;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.regex.Pattern;

/**
 * A parallel portfolio for FlatZinc models (option -p). Each thread reads the model into a store of
 * its own and solves it with its own settings: the first with the options given, the others with
 * free search and lazy clause generation under other heuristics. The threads share the objective
 * value of the best solution found so far, which bounds the search of the others, and the first
 * thread that finishes its search decides the result: a solution for satisfaction, an optimum, or
 * that there is none.
 *
 * <p>The threads print to their own capture, which tells when a thread has explored its whole
 * search space; the portfolio alone prints solutions and the final status.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
@SuppressWarnings("java:S106") // stdout is the interface of a FlatZinc solver
final class Portfolio {

  /** The settings of the threads after the first, in this order; -f and --lcg are given here. */
  private static final String[][] CONFIGS = {
    {"free", "-f"},
    {"lcg", "--lcg", "-f"},
    {"free-chs-luby", "-f", "--free-config", "heuristic=chs,restarts=luby,scale=100"},
    {"lcg-bb", "--lcg", "-f", "--free-config", "lcg-core=0,lcg-lb=0"},
    {"free-cacd", "-f", "--free-config", "heuristic=cacd"},
    {"free-afc", "-f", "--free-config", "heuristic=afc,phase=0"},
    {"lcg-fixed", "--lcg"},
    {"free-luby-keep", "-f", "--free-config", "restarts=luby,scale=50,flush=0"}
  };

  /** The most threads the portfolio uses: the options given and each setting above. */
  static final int MAX_THREADS = CONFIGS.length + 1;

  private static final String COMPLETE = "==========";

  /** How long the portfolio waits for its stopped threads to end after printing the answer. */
  private static final long JOIN_MILLIS = 10_000;

  private static final String UNSATISFIABLE = "=====UNSATISFIABLE=====";

  // floats are solved in one thread: their precision and derivatives are kept in static fields
  private static final Pattern FLOAT_VAR = Pattern.compile("\\bvar\\s+(float\\b|-?\\d+\\.\\d)");

  private static final ThreadLocal<OutputStream> CAPTURE = new ThreadLocal<>();

  private final Options options;
  private final List<Worker> workers = new ArrayList<>();
  private final Object lock = new Object();
  // where the portfolio prints: stdout as it was when the portfolio started
  private PrintStream stdout;
  // stdout while the portfolio runs, given back by the last thread to end if it outlives run()
  private PrintStream dispatch;
  private boolean restorePending;

  // the objective value (of the minimised cost variable) of the best solution, read by all threads
  private volatile int bestCost = Integer.MAX_VALUE;
  private String bestSolution;
  private Worker bestWorker;
  private boolean optimisation;
  private boolean maximisation;
  private int solutions;
  private int running;
  private boolean finished;
  private boolean complete;

  private Portfolio(Options options) {
    this.options = options;
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

  private static boolean isSatisfaction(String model) {
    int solve = model.lastIndexOf("solve");
    return solve >= 0 && model.indexOf("satisfy", solve) >= 0;
  }

  /**
   * Solves the model with a portfolio of threads and prints the result as one thread would.
   *
   * @param args the command line arguments
   * @param options the options given
   * @return the exit status: 0 when the threads ran, 1 when none could solve the model
   */
  static int solve(String[] args, Options options) {
    return new Portfolio(options).run(args);
  }

  private int run(String[] args) {
    stdout = System.out;
    dispatch = new PrintStream(new Dispatch(stdout), true, stdout.charset());
    System.setOut(dispatch);
    try {
      return run(args, stdout);
    } finally {
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
    List<String> base = baseArguments(args);
    int threads = Math.min(options.threads(), MAX_THREADS);
    workers.add(new Worker("given", arguments(base, List.of(), false)));
    for (String[] config : CONFIGS) {
      if (workers.size() == threads) {
        break;
      }
      if (!sameAsGiven(config)) {
        List<String> flags = Arrays.asList(config).subList(1, config.length);
        workers.add(new Worker(config[0], arguments(base, flags, true)));
      }
    }
    String file = args[args.length - 1];
    synchronized (lock) {
      running = workers.size();
    }
    for (Worker w : workers) {
      Thread t = new Thread(() -> w.run(file), "jacop-portfolio-" + w.name);
      t.setDaemon(true);
      w.thread = t;
      t.start();
    }
    boolean timedOut = await(start);
    for (Worker w : workers) {
      w.stop();
    }
    printResult(out, timedOut, start);
    // the threads stop within milliseconds in search, later when stopped while reading the model
    long joinDeadline = System.currentTimeMillis() + JOIN_MILLIS;
    for (Worker w : workers) {
      try {
        w.thread.join(Math.max(1, joinDeadline - System.currentTimeMillis()));
      } catch (InterruptedException _) {
        Thread.currentThread().interrupt();
        break;
      }
    }
    return 0;
  }

  /** Waits until a thread finishes its search or all threads end. Returns true on a time-out. */
  private boolean await(long start) {
    long timeOut = options.getTimeOut();
    synchronized (lock) {
      while (!finished && running > 0) {
        long wait = 0;
        if (timeOut > 0) {
          // the threads stop at the time-out themselves; this is a safety margin
          wait = start + timeOut + 2000 - System.currentTimeMillis();
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
      return !complete && timeOut > 0 && System.currentTimeMillis() - start >= timeOut;
    }
  }

  private void printResult(PrintStream out, boolean timedOut, long start) {
    StringBuilder s = new StringBuilder();
    synchronized (lock) {
      if (bestSolution != null) {
        if (!options.getAll()) {
          s.append(bestSolution);
        }
        if (complete && optimisation) {
          s.append(COMPLETE).append('\n');
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
      if (options.getStatistics()) {
        s.append("%%%mzn-stat: portfolioThreads=").append(workers.size()).append('\n');
        if (bestWorker != null) {
          s.append("%%%mzn-stat: portfolioBest=").append(bestWorker.name).append('\n');
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
  }

  // the cost variable is the negated objective under maximisation
  private int objective(int cost) {
    return maximisation ? -cost : cost;
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
    for (String arg : base) {
      if (!ownSearch || !isSearchFlag(arg)) {
        a.add(arg);
      }
    }
    a.addAll(flags);
    if (options.getTimeOut() > 0) {
      a.add("-t");
      a.add(Integer.toString(options.getRemainingTimeOut()));
    }
    return a;
  }

  private static boolean isSearchFlag(String arg) {
    return "-f".equals(arg) || "--free-search".equals(arg) || "--lcg".equals(arg);
  }

  /** Whether a setting is what the options given select already, so it would repeat that thread. */
  private boolean sameAsGiven(String[] config) {
    List<String> flags = Arrays.asList(config);
    return flags.contains("--lcg") == options.lcg()
        && flags.contains("-f") == options.freeSearch()
        && !flags.contains("--free-config")
        && options.freeConfig.isEmpty();
  }

  /**
   * Takes a solution of a thread: the first one for satisfaction, which ends the search, and for
   * optimisation each one better than the best so far.
   */
  private void solution(Worker w, String text, Integer cost, boolean maximise) {
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
        optimisation = true;
        maximisation = maximise;
        bestCost = cost;
        bestSolution = text;
        bestWorker = w;
        solutions++;
      }
      if (options.getAll()) {
        stdout.print(text);
        stdout.flush();
      }
    }
  }

  private void ended(boolean searchComplete) {
    synchronized (lock) {
      running--;
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

  /** One thread of the portfolio, as seen by the model it solves. */
  final class Worker {

    final String name;
    private final List<String> args;
    private final List<Runnable> stops = new CopyOnWriteArrayList<>();
    private volatile boolean stopped;
    private Thread thread;

    Worker(String name, List<String> args) {
      this.name = name;
      this.args = args;
    }

    private void run(String file) {
      StatusCapture capture = new StatusCapture();
      CAPTURE.set(capture);
      boolean ran = false;
      try {
        List<String> a = new ArrayList<>(args);
        a.add(file);
        Options opt = new Options(a.toArray(new String[0]));
        opt.portfolioWorker = this;
        try (FileInputStream in = opt.getFile()) {
          ran = Fz2jacop.solveInPortfolio(opt, in) == 0;
        }
      } catch (IOException | RuntimeException e) {
        FzConsole.printlnErr("%% portfolio thread " + name + " stopped: " + e);
      } finally {
        CAPTURE.remove();
        ended(ran && !stopped && capture.complete);
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
     */
    void solution(String text, Integer cost, boolean maximise) {
      Portfolio.this.solution(this, text, cost, maximise);
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

    private void stop() {
      stopped = true;
      for (Runnable r : stops) {
        r.run();
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

  /** The output of a thread: only the line that says its search is complete matters. */
  private static final class StatusCapture extends OutputStream {

    private final StringBuilder line = new StringBuilder();
    boolean complete;

    @Override
    public void write(int b) {
      if (b == '\n') {
        String l = line.toString().strip();
        if (COMPLETE.equals(l) || UNSATISFIABLE.equals(l)) {
          complete = true;
        }
        line.setLength(0);
      } else if (line.length() < 64) {
        line.append((char) b);
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
