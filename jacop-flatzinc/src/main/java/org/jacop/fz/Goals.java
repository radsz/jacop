/*
 * Goals.java
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

import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.ByteBuffer;
import java.nio.channels.SeekableByteChannel;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.jacop.search.MultiObjective;
import org.jacop.search.MultiObjective.Status;
import org.jacop.search.MultiObjective.Subproblem;

/**
 * Several objectives of a FlatZinc model, given by an annotation of its solve item: MiniZinc's
 * {@code goal_hierarchy([...])} (std/experimental.mzn) asks for the lexicographic optimum and
 * JaCoP's {@code pareto([...])} (jacop.mzn) for the Pareto front. Their goals are {@code
 * min_goal(x)}, {@code int_min_goal(x)}, {@code max_goal(x)}, {@code int_max_goal(x)} for an
 * integer x and {@code sat_goal(b)} for a Boolean b, which is better true.
 *
 * <pre>
 * solve :: goal_hierarchy([int_min_goal(cost), max_goal(quality)]) satisfy;
 * solve :: pareto([min_goal(cost), min_goal(time)]) satisfy;
 * </pre>
 *
 * <p>{@link MultiObjective} splits the problem into single-objective subproblems. Each one is the
 * model with its bounds and exclusions as constraints and {@code minimize} or {@code maximize} of
 * one goal, solved by the front end as any model (with free search, lazy clause generation,
 * presolve or a portfolio when the options ask for it) in this JVM. Every goal is copied into a new
 * output variable, so the values of the goals can be read from the printed solutions, and those
 * lines are removed again before the solutions are printed.
 *
 * <p>For lexicographic optimisation the output is that of an optimisation: the best solution (with
 * -a, each solution better than the one before) and {@code ==========} when it is optimal. For the
 * Pareto front each point is printed as soon as it is proven, followed by {@code ==========} when
 * the front is complete. At a time-out the best solution not yet proven optimal is printed last.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
@SuppressWarnings("java:S106") // stdout is the interface of a FlatZinc solver
final class Goals implements MultiObjective.Subsolver<String> {

  /** The kind of a goal. */
  private enum Kind {
    MIN,
    MAX,
    SAT
  }

  /** A goal: its kind and the FlatZinc expression of the objective. */
  private record Goal(Kind kind, String expression) {}

  private static final String HIERARCHY = "goal_hierarchy";
  private static final String PARETO = "pareto";

  /** The prefix of the output variables the goals are copied into. */
  static final String PREFIX = "X_JACOP_GOAL_";

  private static final String COMPLETE = "==========";
  private static final String UNSATISFIABLE = "=====UNSATISFIABLE=====";
  private static final String UNKNOWN = "=====UNKNOWN=====";
  private static final String TIME_OUT = "%% =====TIME-OUT=====";

  /** How much of the end of the model is read to look for a goal annotation. */
  private static final int TAIL = 1 << 20;

  private static final Pattern SOLVE = Pattern.compile("(?m)^\\s*solve\\b");
  private static final Pattern CONSTRAINT = Pattern.compile("(?m)^\\s*constraint\\b");
  private static final Pattern GOAL = Pattern.compile("\\s*(\\w+)\\s*\\(\\s*([^()]*?)\\s*\\)\\s*");
  private static final Pattern GOAL_VALUE =
      Pattern.compile("^" + PREFIX + "(\\d+)_\\s*=\\s*(-?\\d+)\\s*;$");
  private static final Pattern IDENTIFIER = Pattern.compile("[A-Za-z][A-Za-z0-9_]*");

  private final Options options;
  private final String[] args;
  private final boolean pareto;
  private final List<Goal> goals;
  // the model up to the solve item, and the annotations of the solve item without the goals
  private final String declarations;
  private final String constraints;
  private final String annotations;

  private final PrintStream out = System.out;
  private final Set<String> comments = new HashSet<>();
  private final Map<String, Long> statistics = new LinkedHashMap<>();
  private String error;

  private Goals(
      Options options,
      String[] args,
      boolean pareto,
      List<Goal> goals,
      String declarations,
      String constraints,
      String annotations) {
    this.options = options;
    this.args = args;
    this.pareto = pareto;
    this.goals = goals;
    this.declarations = declarations;
    this.constraints = constraints;
    this.annotations = annotations;
  }

  /**
   * Reads the goals of the model of the options.
   *
   * @param options the options
   * @param args the command line arguments
   * @return the goals, or null when the solve item has no goal annotation that JaCoP supports (a
   *     goal JaCoP cannot optimise is reported on stderr and the model is solved without goals)
   */
  static Goals of(Options options, String[] args) {
    Path file = Path.of(options.getFileName());
    String model;
    try {
      String tail = tail(file);
      if (!tail.contains(HIERARCHY) && !tail.contains(PARETO + "(")) {
        return null;
      }
      model = Files.readString(file, StandardCharsets.ISO_8859_1);
    } catch (IOException _) {
      // the front end reports a model it cannot read
      return null;
    }
    return parse(options, args, model);
  }

  private static String tail(Path file) throws IOException {
    try (SeekableByteChannel c = Files.newByteChannel(file)) {
      long size = c.size();
      int length = (int) Math.min(size, TAIL);
      c.position(size - length);
      ByteBuffer b = ByteBuffer.allocate(length);
      while (b.hasRemaining() && c.read(b) >= 0) {
        // reads until the end
      }
      return new String(b.array(), 0, b.position(), StandardCharsets.ISO_8859_1);
    }
  }

  private static Goals parse(Options options, String[] args, String model) {
    Matcher solve = SOLVE.matcher(model);
    int start = -1;
    while (solve.find()) {
      start = solve.start();
    }
    if (start < 0) {
      return null;
    }
    String item = model.substring(start).strip();
    int end = item.lastIndexOf(';');
    if (end >= 0) {
      item = item.substring(0, end).strip();
    }
    boolean isPareto = false;
    int at = annotation(item, HIERARCHY);
    if (at < 0) {
      at = annotation(item, PARETO);
      isPareto = true;
    }
    if (at < 0) {
      return null;
    }
    String name = isPareto ? PARETO : HIERARCHY;
    int open = item.indexOf('(', at);
    int close = closing(item, open);
    if (close < 0) {
      return null;
    }
    if (!item.endsWith("satisfy")) {
      FzConsole.printlnErr(
          "%% " + name + " is ignored: it needs a solve item with satisfy, not " + item);
      return null;
    }
    List<Goal> goals = new ArrayList<>();
    String unsupported = goals(item.substring(open + 1, close), model, goals);
    if (unsupported != null) {
      FzConsole.printlnErr("%% " + name + " is ignored: " + unsupported);
      return null;
    }
    if (goals.isEmpty()) {
      return null;
    }
    // the annotation and the "::" before it
    int from = item.lastIndexOf("::", at);
    String annotations =
        (item.substring(0, from) + item.substring(close + 1, item.length() - "satisfy".length()))
            .replaceFirst("^\\s*solve", "")
            .strip();
    String head = model.substring(0, start);
    Matcher c = CONSTRAINT.matcher(head);
    int split = c.find() ? c.start() : head.length();
    return new Goals(
        options,
        args,
        isPareto,
        goals,
        head.substring(0, split),
        head.substring(split),
        annotations);
  }

  // the position of an annotation of the solve item, or -1
  private static int annotation(String item, String name) {
    Matcher m = Pattern.compile("::\\s*(" + name + ")\\s*\\(").matcher(item);
    return m.find() ? m.start(1) : -1;
  }

  // the position of the parenthesis that closes the one at open, or -1
  private static int closing(String s, int open) {
    int depth = 0;
    for (int i = open; i >= 0 && i < s.length(); i++) {
      char ch = s.charAt(i);
      if (ch == '(') {
        depth++;
      } else if (ch == ')' && --depth == 0) {
        return i;
      }
    }
    return -1;
  }

  /** Reads the goals of the list; returns why one is not supported, or null. */
  private static String goals(String argument, String model, List<Goal> goals) {
    String list = argument.strip();
    if (!list.startsWith("[") || !list.endsWith("]")) {
      return "its argument is not a list of goals: " + list;
    }
    list = list.substring(1, list.length() - 1).strip();
    if (list.isEmpty()) {
      return null;
    }
    for (String g : split(list)) {
      Matcher m = GOAL.matcher(g);
      if (!m.matches()) {
        return "goal " + g.strip() + " is not supported";
      }
      Kind kind =
          switch (m.group(1)) {
            case "min_goal", "int_min_goal" -> Kind.MIN;
            case "max_goal", "int_max_goal" -> Kind.MAX;
            case "sat_goal" -> Kind.SAT;
            default -> null;
          };
      String x = m.group(2);
      if (kind == null || isFloat(x, model)) {
        return "goal " + g.strip() + " is not supported (only integer and Boolean goals are)";
      }
      goals.add(new Goal(kind, x));
    }
    return null;
  }

  // splits at the commas outside brackets
  private static List<String> split(String list) {
    List<String> parts = new ArrayList<>();
    int depth = 0;
    int from = 0;
    for (int i = 0; i < list.length(); i++) {
      char ch = list.charAt(i);
      if (ch == '(' || ch == '[') {
        depth++;
      } else if (ch == ')' || ch == ']') {
        depth--;
      } else if (ch == ',' && depth == 0) {
        parts.add(list.substring(from, i));
        from = i + 1;
      }
    }
    parts.add(list.substring(from));
    return parts;
  }

  // whether a goal is a float: a float literal or a float variable (or array of them)
  private static boolean isFloat(String x, String model) {
    if (x.matches("-?\\d+\\.\\d.*")) {
      return true;
    }
    Matcher id = IDENTIFIER.matcher(x);
    if (!id.lookingAt()) {
      return false;
    }
    Matcher decl =
        Pattern.compile(
                "(?m)^\\s*(?:array\\s*\\[[^]]*]\\s*of\\s*)?var\\s+([^:;]*?):\\s*"
                    + Pattern.quote(id.group())
                    + "\\b")
            .matcher(model);
    return decl.find()
        && (decl.group(1).contains("float") || decl.group(1).matches(".*\\d\\.\\d.*"));
  }

  /**
   * Solves the model for its goals and prints the result.
   *
   * @return the exit status: 0 when the model was solved, 1 when a subproblem failed with an error
   */
  int solve() {
    long start = System.currentTimeMillis();
    boolean[] maximize = new boolean[goals.size()];
    for (int i = 0; i < maximize.length; i++) {
      maximize[i] = goals.get(i).kind() != Kind.MIN;
    }
    MultiObjective<String> mo = new MultiObjective<>(this, maximize);
    boolean all = options.getAll();
    if (pareto || all) {
      mo.setSolutionListener((values, solution) -> print(solution));
    }
    Status status = pareto ? mo.pareto() : mo.lexicographic();
    if (error != null) {
      return 1;
    }
    String best = mo.bestSolution();
    StringBuilder s = new StringBuilder();
    switch (status) {
      case OPTIMAL -> {
        if (!pareto && !all) {
          s.append(best);
        }
        s.append(COMPLETE).append('\n');
      }
      case FEASIBLE -> {
        // the solution the search stopped at is not printed yet unless it is a lexicographic one
        // printed with -a
        if (best != null && (pareto || !all)) {
          s.append(best);
        }
        s.append(TIME_OUT).append('\n');
      }
      case UNSATISFIABLE -> s.append(UNSATISFIABLE).append('\n');
      case UNKNOWN -> s.append(UNKNOWN).append('\n').append(TIME_OUT).append('\n');
    }
    if (options.getStatistics()) {
      s.append("%%%mzn-stat: goalSubproblems=").append(mo.subproblems()).append('\n');
      for (Map.Entry<String, Long> e : statistics.entrySet()) {
        s.append("%%%mzn-stat: ").append(e.getKey()).append('=').append(e.getValue()).append('\n');
      }
      if (pareto) {
        s.append("%%%mzn-stat: paretoPoints=").append(mo.front().size()).append('\n');
      } else if (mo.best() != null) {
        s.append("%%%mzn-stat: objective=").append(mo.best()[0]).append('\n');
      }
      s.append("%%%mzn-stat: solveTime=")
          .append((System.currentTimeMillis() - start) / 1000.0)
          .append("\n%%%mzn-stat-end\n");
    }
    print(s.toString());
    return 0;
  }

  private void print(String s) {
    out.print(s);
    out.flush();
  }

  /**
   * Solves a subproblem as a FlatZinc model in this JVM.
   *
   * @param p the subproblem
   * @param solutions takes the values of the goals and the solution as printed
   * @return true when the search was complete
   */
  @Override
  public boolean solve(Subproblem p, BiConsumer<int[], String> solutions) {
    if (error != null) {
      return false;
    }
    if (options.getTimeOut() > 0 && options.timeOutPassed()) {
      return false;
    }
    Path file = null;
    try {
      file = Files.createTempFile("jacop-goal", ".fzn");
      Files.writeString(file, model(p), StandardCharsets.ISO_8859_1);
      Phase phase = new Phase(solutions);
      int status;
      PrintStream capture = new PrintStream(phase, true, out.charset());
      System.setOut(capture);
      try {
        status = new Fz2jacop().callMain(arguments(file));
      } finally {
        capture.flush();
        System.setOut(out);
      }
      if (status != 0) {
        error = "subproblem " + p + " failed";
        return false;
      }
      return phase.complete;
    } catch (IOException e) {
      error = e.toString();
      FzConsole.printlnErr("%% " + error);
      return false;
    } finally {
      if (file != null) {
        try {
          Files.deleteIfExists(file);
        } catch (IOException _) {
          // a temporary file left behind
        }
      }
    }
  }

  /**
   * The FlatZinc model of a subproblem.
   *
   * @param p the subproblem
   * @return the model
   */
  String model(Subproblem p) {
    StringBuilder vars = new StringBuilder();
    StringBuilder cons = new StringBuilder();
    for (int i = 0; i < goals.size(); i++) {
      Goal g = goals.get(i);
      String x = goal(i);
      vars.append(g.kind() == Kind.SAT ? "var 0..1: " : "var int: ")
          .append(x)
          .append(":: output_var;\n");
      if (g.kind() == Kind.SAT) {
        cons.append("constraint bool2int(").append(g.expression()).append(',').append(x);
      } else {
        cons.append("constraint int_eq(").append(x).append(',').append(g.expression());
      }
      cons.append(");\n");
      int lo = p.lower()[i];
      int hi = p.upper()[i];
      if (lo == hi) {
        cons.append("constraint int_eq(").append(x).append(',').append(lo).append(");\n");
      } else {
        if (lo != Integer.MIN_VALUE) {
          cons.append("constraint int_le(").append(lo).append(',').append(x).append(");\n");
        }
        if (hi != Integer.MAX_VALUE) {
          cons.append("constraint int_le(").append(x).append(',').append(hi).append(");\n");
        }
      }
    }
    for (int j = 0; j < p.excluded().size(); j++) {
      int[] point = p.excluded().get(j);
      StringBuilder clause = new StringBuilder();
      for (int i = 0; i < point.length; i++) {
        // some goal strictly better than the point
        String b = PREFIX + "EX_" + j + "_" + i + "_";
        vars.append("var bool: ").append(b).append(";\n");
        cons.append("constraint int_le_reif(");
        if (p.maximize()[i]) {
          cons.append((long) point[i] + 1).append(',').append(goal(i));
        } else {
          cons.append(goal(i)).append(',').append((long) point[i] - 1);
        }
        cons.append(',').append(b).append(");\n");
        clause.append(i == 0 ? "" : ",").append(b);
      }
      cons.append("constraint bool_clause([").append(clause).append("],[]);\n");
    }
    return declarations
        + vars
        + constraints
        + cons
        + "solve "
        + annotations
        + (p.maximize()[p.objective()] ? " maximize " : " minimize ")
        + goal(p.objective())
        + ";\n";
  }

  private static String goal(int i) {
    return PREFIX + i + "_";
  }

  /** The arguments of a subproblem: those given, with -a and the time left. */
  private String[] arguments(Path file) {
    List<String> a = new ArrayList<>();
    for (int i = 0; i < args.length - 1; i++) {
      switch (args[i]) {
        case "-t", "--time-out", "-n", "--num-solutions", "-o", "--outputfile" -> i++;
        case "-a", "--all", "--all-solutions" -> {
          // added below
        }
        default -> a.add(args[i]);
      }
    }
    a.add("-a");
    if (options.getTimeOut() > 0) {
      a.add("-t");
      a.add(Integer.toString(options.getRemainingTimeOut()));
    }
    a.add(file.toString());
    return a.toArray(new String[0]);
  }

  /**
   * The output of a subproblem: its solutions go to the subsolver's caller without the lines of the
   * goal variables, its status says whether its search was complete, and its statistics add up over
   * the subproblems. Comments are printed once.
   */
  private final class Phase extends OutputStream {

    private final BiConsumer<int[], String> solutions;
    private final StringBuilder line = new StringBuilder();
    private final StringBuilder solution = new StringBuilder();
    private final int[] values = new int[goals.size()];
    boolean complete;

    Phase(BiConsumer<int[], String> solutions) {
      this.solutions = solutions;
    }

    @Override
    public void write(int b) {
      if (b == '\n') {
        line(line.toString());
        line.setLength(0);
      } else {
        line.append((char) b);
      }
    }

    @Override
    public void write(byte[] b, int off, int len) {
      for (int i = off; i < off + len; i++) {
        write(b[i] & 0xff);
      }
    }

    private void line(String l) {
      String s = l.strip();
      if (s.equals("----------")) {
        solution.append(l).append('\n');
        solutions.accept(values.clone(), solution.toString());
        solution.setLength(0);
      } else if (s.equals(COMPLETE) || s.equals(UNSATISFIABLE)) {
        complete = true;
      } else if (s.startsWith("%%%mzn-stat")) {
        statistic(s);
      } else if (s.startsWith("%")) {
        // a subproblem without a better solution often fails while it is read
        if (!s.startsWith("%% =====")
            && !s.startsWith("%% problem detected for")
            && comments.add(s)) {
          print(l + "\n");
        }
      } else if (s.startsWith(PREFIX)) {
        Matcher m = GOAL_VALUE.matcher(s);
        if (m.matches()) {
          values[Integer.parseInt(m.group(1))] = Integer.parseInt(m.group(2));
        }
      } else if (!s.isEmpty() || !solution.isEmpty()) {
        if (!s.startsWith("=====")) {
          solution.append(l).append('\n');
        }
      }
    }

    // adds up the counts of the subproblems
    private void statistic(String s) {
      int eq = s.indexOf('=');
      if (eq < 0) {
        return;
      }
      String key = s.substring("%%%mzn-stat:".length(), eq).strip();
      if (!Set.of("nodes", "failures", "propagations", "restarts", "solutions").contains(key)) {
        return;
      }
      try {
        long v = Long.parseLong(s.substring(eq + 1).strip().replace(",", ""));
        statistics.merge(key, v, Long::sum);
      } catch (NumberFormatException _) {
        // not a count
      }
    }
  }
}
