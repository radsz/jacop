/*
 * DecompositionCheck.java
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.decomposition;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.time.Instant;
import java.time.temporal.ChronoUnit;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HexFormat;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import org.jacop.decomposition.FznModel.Constraint;
import org.jacop.decomposition.FznModel.Expr;
import org.jacop.decomposition.FznModel.Ident;
import org.jacop.decomposition.FznModel.Item;
import org.jacop.decomposition.FznModel.ItemKind;
import org.junit.jupiter.api.Test;

/**
 * Checks JaCoP's global constraints against their MiniZinc standard decompositions on the FlatZinc
 * test problems.
 *
 * <p>For each problem it first counts the solutions with JaCoP's own constraints (the reference
 * run). An optimisation problem is turned into a satisfaction problem whose solutions are the
 * solutions at least as good as the best objective found, so its solutions can be counted too.
 * Then, for each global constraint of the problem in turn, it replaces every occurrence of that
 * constraint with the decomposition from {@link StdDecompositions}, counts the solutions again and
 * compares: the search tree changes, but the number of solutions and the set of printed solutions
 * must not. The counting models search in a static order (input order, smallest value first), so
 * both models list their solutions in the same order; when a search does not finish within the
 * limits, the solutions found by both runs must be the same sequence ({@code PARTIAL}).
 *
 * <p>Every result is appended to the state file, so a run that is stopped resumes with the next
 * problem or constraint that has not been checked. A difference is reported as {@code DIFF},
 * narrowed to one occurrence of the constraint when one occurrence alone reproduces it, and the
 * decomposed model is written to the output directory for investigation.
 *
 * <p>It is a tool, not part of the build. Run it with
 *
 * <pre>
 * mvn -Pmin -pl jacop-benchmarks test -Dtest=DecompositionCheck -Dsurefire.rerunFailingTestsCount=0
 * </pre>
 *
 * <p>System properties (all optional):
 *
 * <ul>
 *   <li>{@code decomp.category}: time category directory under {@code src/test/fz} (upTo5sec).
 *   <li>{@code decomp.state}: state file (src/test/fz/decomposition/state-CATEGORY.tsv).
 *   <li>{@code decomp.timeout}: seconds per solver run (30).
 *   <li>{@code decomp.solutions}: solution limit per counting run (200000).
 *   <li>{@code decomp.constraints}: comma-separated constraint names to check (all supported).
 *   <li>{@code decomp.problems}: regular expression on problem names (all).
 *   <li>{@code decomp.maxProblems}: stop after this many problems were worked on (no limit).
 *   <li>{@code decomp.retry}: comma-separated verdicts to check again, such as DIFF,ERROR.
 *   <li>{@code decomp.threads}: problems checked in parallel (1).
 *   <li>{@code decomp.out}: directory for decomposed models of differences
 *       (target/decomposition-check).
 * </ul>
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class DecompositionCheck {

  private static final String FZ = "src/test/fz/";

  private final String category = System.getProperty("decomp.category", "upTo5sec");
  private final int timeoutMillis =
      Integer.parseInt(System.getProperty("decomp.timeout", "30")) * 1000;
  private final int solutionLimit =
      Integer.parseInt(System.getProperty("decomp.solutions", "200000"));
  private final Set<String> constraintFilter = csv(System.getProperty("decomp.constraints", ""));
  private final Pattern problemFilter =
      Pattern.compile(System.getProperty("decomp.problems", ".*"));
  private final int maxProblems =
      Integer.parseInt(System.getProperty("decomp.maxProblems", "" + Integer.MAX_VALUE));
  private final Set<String> retry = csv(System.getProperty("decomp.retry", ""));
  private final int threads = Integer.parseInt(System.getProperty("decomp.threads", "1"));
  private final Path out = Path.of(System.getProperty("decomp.out", "target/decomposition-check"));

  private CheckState state;
  private final AtomicInteger worked = new AtomicInteger();
  private final Map<String, Integer> summary = new TreeMap<>();

  @Test
  void check() throws Exception {
    run();
  }

  public static void main(String[] args) throws Exception {
    new DecompositionCheck().run();
  }

  void run() throws Exception {
    Path stateFile =
        Path.of(
            System.getProperty("decomp.state", FZ + "decomposition/state-" + category + ".tsv"));
    state = new CheckState(stateFile);
    Files.createDirectories(out);
    List<String> problems = Files.readAllLines(Path.of(FZ + category + "/list.txt"));
    System.out.println(
        "DecompositionCheck: "
            + problems.size()
            + " problems in "
            + category
            + ", state "
            + stateFile);
    ExecutorService pool = Executors.newFixedThreadPool(threads);
    for (String p : problems) {
      String problem = p.strip();
      if (problem.isEmpty() || !problemFilter.matcher(problem).find()) {
        continue;
      }
      pool.submit(
          () -> {
            if (worked.get() >= maxProblems) {
              return;
            }
            try {
              checkProblem(problem);
            } catch (Exception | StackOverflowError e) {
              System.out.println("  " + problem + ": " + e);
              count("EXCEPTION");
            }
          });
    }
    pool.shutdown();
    pool.awaitTermination(365, TimeUnit.DAYS);
    System.out.println("DecompositionCheck summary: " + summary);
  }

  private synchronized void count(String verdict) {
    summary.merge(verdict, 1, Integer::sum);
  }

  // ---------------------------------------------------------------------------------------------

  /** The reference run of a problem; {@code run} is null when it comes from the state file. */
  private static final class Baseline {
    final String objective;
    final String status;
    final long solutions;
    final long distinct;
    final String digest;
    SolverRun run;

    Baseline(String objective, String status, long solutions, long distinct, String digest) {
      this.objective = objective;
      this.status = status;
      this.solutions = solutions;
      this.distinct = distinct;
      this.digest = digest;
    }
  }

  private void checkProblem(String problem) throws IOException {
    Path fzn = Path.of(FZ + category + "/" + problem + ".fzn");
    String text = Files.readString(fzn, StandardCharsets.UTF_8);
    String hash = sha(text);
    if (state.nothingToCheck(problem, hash)) {
      return;
    }
    FznModel model = FznModel.parse(text);
    Map<String, List<Integer>> occurrences = new LinkedHashMap<>();
    for (Constraint c : model.constraints) {
      if (StdDecompositions.supports(c.name()) || c.name().startsWith("jacop_")) {
        occurrences.computeIfAbsent(c.name(), k -> new ArrayList<>()).add(c.index());
      }
    }
    if (occurrences.isEmpty()) {
      state.append("N", problem, hash, "no global constraint", now());
      return;
    }
    List<String> pending = new ArrayList<>();
    for (Map.Entry<String, List<Integer>> e : occurrences.entrySet()) {
      String name = e.getKey();
      if (!constraintFilter.isEmpty() && !constraintFilter.contains(name)) {
        continue;
      }
      String[] done = state.check(problem, hash, name);
      if (done != null && !retry.contains(done[5])) {
        continue;
      }
      if (!StdDecompositions.supports(name)) {
        if (done == null) {
          state.append(
              "C",
              problem,
              hash,
              name,
              "" + e.getValue().size(),
              "NO_DECOMPOSITION",
              "",
              "",
              "",
              "",
              "",
              "",
              now(),
              "");
          count("NO_DECOMPOSITION");
        }
        continue;
      }
      pending.add(name);
    }
    if (pending.isEmpty()) {
      return;
    }
    if (worked.incrementAndGet() > maxProblems) {
      return;
    }
    List<String> options = options(fzn);
    Baseline baseline = baseline(problem, hash, model, options);
    if (baseline == null) {
      return;
    }
    for (String name : pending) {
      checkConstraint(problem, hash, model, options, baseline, name, occurrences.get(name));
    }
  }

  private Baseline baseline(String problem, String hash, FznModel model, List<String> options)
      throws IOException {
    String[] b = state.baseline(problem, hash);
    if (b != null && !"ERROR".equals(b[5])) {
      return new Baseline(b[4], b[5], Long.parseLong(b[6]), Long.parseLong(b[7]), b[8]);
    }
    String objective = "";
    if (!"satisfy".equals(model.solveKind) && model.constant(model.objective) == null) {
      if (!(model.objective instanceof Ident(String name))
          || model.decls.get(name) == null
          || model.decls.get(name).type != FznModel.BaseType.INT) {
        state.append("N", problem, hash, "objective is not an int variable", now());
        return null;
      }
      Path opt = write(problem, "optimise", render(model, Set.of(), null, null, false, true));
      SolverRun r = SolverRun.run(opt, options, false, 0, timeoutMillis);
      Files.deleteIfExists(opt);
      String value = SolverRun.value(r.lastSolution, name);
      if (r.status == SolverRun.Status.ERROR || value == null && r.solutions > 0) {
        state.append(
            "B", problem, hash, model.solveKind, "", "ERROR", "", "", "", "", "" + r.millis, now());
        System.out.println("  " + problem + ": optimisation run failed " + r.error);
        count("REFERENCE_ERROR");
        return null;
      }
      // without a solution the bound is left out and all solutions are counted
      objective = value == null ? "" : value;
    }
    SolverRun r = runCount(problem, model, Set.of(), null, objective, options, "reference");
    String status = r.status.name();
    state.append(
        "B",
        problem,
        hash,
        model.solveKind,
        objective,
        status,
        "" + r.solutions,
        "" + r.distinctCount(),
        r.digest(),
        "" + r.nodes,
        "" + r.millis,
        now());
    if (r.status == SolverRun.Status.ERROR) {
      System.out.println("  " + problem + ": reference run failed " + r.error);
      count("REFERENCE_ERROR");
      return null;
    }
    Baseline baseline = new Baseline(objective, status, r.solutions, r.distinctCount(), r.digest());
    baseline.run = r;
    return baseline;
  }

  /** The reference run with its solutions, run again when it was read from the state file. */
  private SolverRun referenceRun(
      String problem, FznModel model, List<String> options, Baseline baseline) throws IOException {
    if (baseline.run == null) {
      baseline.run = runCount(problem, model, Set.of(), null, baseline.objective, options, "ref");
    }
    return baseline.run;
  }

  /** Counts the solutions of the model with the given constraints decomposed. */
  private SolverRun runCount(
      String problem,
      FznModel model,
      Set<Integer> replaced,
      FznBuilder builder,
      String objective,
      List<String> options,
      String tag)
      throws IOException {
    Path file = write(problem, tag, countModel(model, replaced, builder, objective));
    SolverRun r = SolverRun.run(file, options, true, solutionLimit, timeoutMillis);
    if (r.solutions >= solutionLimit && r.status == SolverRun.Status.COMPLETE) {
      r.status = SolverRun.Status.INCOMPLETE;
    }
    Files.deleteIfExists(file);
    return r;
  }

  private String countModel(
      FznModel model, Set<Integer> replaced, FznBuilder builder, String objective) {
    String bound = null;
    if (!"satisfy".equals(model.solveKind) && !objective.isEmpty()) {
      String obj = FznModel.render(model.objective);
      bound =
          "minimize".equals(model.solveKind)
              ? "int_le(" + obj + "," + objective + ")"
              : "int_le(" + objective + "," + obj + ")";
    }
    return render(model, replaced, builder, bound, true, false);
  }

  private FznBuilder decompose(FznModel model, List<Integer> indices) {
    FznBuilder builder = new FznBuilder(model, "X_DECOMP_");
    for (int i : indices) {
      Constraint c = model.constraints.get(i);
      StdDecompositions.decompose(builder, c.name(), c.args());
    }
    return builder;
  }

  private void checkConstraint(
      String problem,
      String hash,
      FznModel model,
      List<String> options,
      Baseline baseline,
      String name,
      List<Integer> indices)
      throws IOException {
    FznBuilder builder;
    try {
      builder = decompose(model, indices);
    } catch (UnsupportedOperationException | IllegalArgumentException e) {
      state.append(
          "C",
          problem,
          hash,
          name,
          "" + indices.size(),
          "UNSUPPORTED",
          "",
          "",
          "",
          "",
          "",
          "",
          now(),
          e.getMessage());
      count("UNSUPPORTED");
      return;
    }
    SolverRun r =
        runCount(problem, model, Set.copyOf(indices), builder, baseline.objective, options, name);
    String note;
    if ("COMPLETE".equals(baseline.status) && r.status == SolverRun.Status.COMPLETE) {
      boolean same =
          r.solutions == baseline.solutions
              && r.distinctCount() == baseline.distinct
              && r.digest().equals(baseline.digest);
      note =
          same
              ? ""
              : "reference has "
                  + baseline.solutions
                  + " solutions ("
                  + baseline.distinct
                  + " distinct), decomposed "
                  + r.solutions
                  + " ("
                  + r.distinctCount()
                  + " distinct)";
    } else {
      note = compare(referenceRun(problem, model, options, baseline), r);
    }
    String verdict;
    if (r.status == SolverRun.Status.ERROR) {
      verdict = "ERROR";
      note = r.error;
    } else if (!note.isEmpty()) {
      verdict = "DIFF";
    } else if ("COMPLETE".equals(baseline.status) && r.status == SolverRun.Status.COMPLETE) {
      verdict = "PASS";
    } else {
      verdict = "PARTIAL";
      SolverRun reference = referenceRun(problem, model, options, baseline);
      note = "first " + Math.min(reference.solutions, r.solutions) + " solutions agree";
      if (r.solutions < CROSS_CHECKS && reference.solutions > r.solutions) {
        // the decomposed search is too slow to compare enough solutions: fix the first reference
        // solutions in the decomposed model instead, which must accept each of them
        String rejected =
            acceptsFirst(
                problem, model, Set.copyOf(indices), builder, baseline, options, reference);
        if (rejected == null) {
          note += ", decomposed accepts the first reference solutions";
        } else {
          verdict = "DIFF";
          note = "decomposed rejects reference solution " + oneLine(rejected);
        }
      }
    }
    if ("DIFF".equals(verdict) || "ERROR".equals(verdict)) {
      note =
          (note + " " + investigate(problem, model, options, baseline, name, indices, r)).strip();
    }
    state.append(
        "C",
        problem,
        hash,
        name,
        "" + indices.size(),
        verdict,
        r.status.name(),
        "" + r.solutions,
        "" + r.distinctCount(),
        r.digest(),
        "" + r.nodes,
        "" + r.millis,
        now(),
        note);
    count(verdict);
    System.out.println(
        "  " + problem + " " + name + " x" + indices.size() + ": " + verdict + " " + note);
  }

  private static final int CROSS_CHECKS = 3;

  /**
   * Fixes the output variables of the first solutions of a run in a model; returns the first
   * solution that the model does not accept, or null when it accepts all of them.
   */
  private String acceptsFirst(
      String problem,
      FznModel model,
      Set<Integer> replaced,
      FznBuilder builder,
      Baseline baseline,
      List<String> options,
      SolverRun run)
      throws IOException {
    int checked = 0;
    for (String solution : run.distinct.keySet()) {
      if (checked++ >= CROSS_CHECKS) {
        break;
      }
      String text = countModel(model, replaced, builder, baseline.objective);
      int solve = text.lastIndexOf("\nsolve") + 1;
      StringBuilder fixes = new StringBuilder();
      for (String f : fix(model, solution)) {
        fixes.append("constraint ").append(f).append(";\n");
      }
      Path file = write(problem, "fix", text.substring(0, solve) + fixes + text.substring(solve));
      SolverRun r = SolverRun.run(file, options, false, 1, timeoutMillis);
      Files.deleteIfExists(file);
      if (r.status == SolverRun.Status.COMPLETE && r.solutions == 0) {
        return solution;
      }
    }
    return null;
  }

  /** Constraints that fix the integer and Boolean output variables to a printed solution. */
  static List<String> fix(FznModel model, String solution) {
    List<String> result = new ArrayList<>();
    for (String line : solution.split("\n")) {
      int eq = line.indexOf('=');
      FznModel.Decl d = eq < 0 ? null : model.decls.get(line.substring(0, eq).strip());
      if (d == null || d.type == FznModel.BaseType.FLOAT || d.type == FznModel.BaseType.SET) {
        continue;
      }
      String value = line.substring(eq + 1).strip();
      value = value.endsWith(";") ? value.substring(0, value.length() - 1) : value;
      Expr parsed = new FznModel.Lexer(value).expr();
      List<Expr> vars;
      List<Expr> values;
      if (d.isArray) {
        if (!(parsed instanceof FznModel.Call(String fn, List<Expr> args))
            || !(args.getLast() instanceof FznModel.ArrayLit(List<Expr> elements))) {
          continue;
        }
        vars = model.elements(new Ident(d.name));
        values = elements;
      } else {
        vars = List.of(new Ident(d.name));
        values = List.of(parsed);
      }
      for (int i = 0; i < Math.min(vars.size(), values.size()); i++) {
        if (model.constant(vars.get(i)) == null) {
          String builtin = model.isBool(vars.get(i)) ? "bool_eq" : "int_eq";
          result.add(
              builtin
                  + "("
                  + FznModel.render(vars.get(i))
                  + ","
                  + FznModel.render(values.get(i))
                  + ")");
        }
      }
    }
    return result;
  }

  /**
   * Compares two runs of the same search. The counting models use a static search order, so the
   * solutions come in the same order whatever the propagation: the shorter list must be a prefix of
   * the longer one, and a finished search must not have fewer solutions than the other run. Returns
   * an empty string when the runs agree.
   */
  static String compare(SolverRun reference, SolverRun decomposed) {
    if (reference.status == SolverRun.Status.ERROR || decomposed.status == SolverRun.Status.ERROR) {
      return "";
    }
    int m = Math.min(reference.order.size(), decomposed.order.size());
    for (int i = 0; i < m; i++) {
      if (!reference.order.get(i).equals(decomposed.order.get(i))) {
        return "solution " + (i + 1) + " differs";
      }
    }
    if (reference.status == SolverRun.Status.COMPLETE
        && decomposed.solutions > reference.solutions) {
      return "decomposed has more than the " + reference.solutions + " reference solutions";
    }
    if (decomposed.status == SolverRun.Status.COMPLETE
        && reference.solutions > decomposed.solutions) {
      return "decomposed has only " + decomposed.solutions + " solutions, reference more";
    }
    return "";
  }

  /**
   * Writes the decomposed model and the first solutions that only one model has. When the
   * constraint occurs several times, looks for one occurrence that alone reproduces the difference.
   */
  private String investigate(
      String problem,
      FznModel model,
      List<String> options,
      Baseline baseline,
      String name,
      List<Integer> indices,
      SolverRun decomposed)
      throws IOException {
    String base = problem.replace('/', '_') + "__" + name;
    Path saved = out.resolve(base + ".fzn");
    Files.writeString(
        saved,
        countModel(model, Set.copyOf(indices), decompose(model, indices), baseline.objective));
    SolverRun reference = referenceRun(problem, model, options, baseline);
    StringBuilder diff = new StringBuilder();
    diff.append("% reference ")
        .append(reference.status)
        .append(' ')
        .append(reference.solutions)
        .append(" solutions, decomposed ")
        .append(decomposed.status)
        .append(' ')
        .append(decomposed.solutions)
        .append(" solutions\n");
    diff.append("% decomposed error: ").append(decomposed.error).append('\n');
    int shown = 0;
    for (String s : reference.distinct.keySet()) {
      if (!decomposed.contains(s) && shown++ < 5) {
        diff.append("% only in reference:\n").append(s);
      }
    }
    shown = 0;
    for (String s : decomposed.distinct.keySet()) {
      if (!reference.contains(s) && shown++ < 5) {
        diff.append("% only in decomposed:\n").append(s);
      }
    }
    Files.writeString(out.resolve(base + ".diff"), diff.toString());
    String culprit = "";
    if (indices.size() > 1) {
      for (int k = 0; k < Math.min(indices.size(), 40); k++) {
        List<Integer> one = List.of(indices.get(k));
        SolverRun r =
            runCount(
                problem,
                model,
                Set.copyOf(one),
                decompose(model, one),
                baseline.objective,
                options,
                name + "-" + k);
        if (r.status == SolverRun.Status.ERROR || !compare(reference, r).isEmpty()) {
          culprit = " occurrence " + k + " (constraint item " + indices.get(k) + ") alone differs";
          Files.writeString(
              out.resolve(base + "__" + k + ".fzn"),
              countModel(model, Set.copyOf(one), decompose(model, one), baseline.objective));
          break;
        }
      }
    }
    return ("see " + saved + culprit).strip();
  }

  // ---------------------------------------------------------------------------------------------

  /**
   * Writes the model back as FlatZinc, with the replaced constraints left out and the builder's
   * variables and constraints added. With {@code satisfy} the solve item becomes a satisfaction
   * item with the same annotations and {@code bound} is added; with {@code outputObjective} the
   * objective variable is printed.
   */
  static String render(
      FznModel model,
      Set<Integer> replaced,
      FznBuilder builder,
      String bound,
      boolean satisfy,
      boolean outputObjective) {
    StringBuilder b = new StringBuilder();
    boolean declared = false;
    String objective =
        outputObjective && model.objective instanceof Ident(String name) ? name : null;
    for (Item item : model.items) {
      if (!declared && (item.kind == ItemKind.CONSTRAINT || item.kind == ItemKind.SOLVE)) {
        if (builder != null) {
          b.append(builder.declarationText());
        }
        declared = true;
      }
      switch (item.kind) {
        case CONSTRAINT -> {
          if (!replaced.contains(item.constraint.index())) {
            b.append(item.text).append(";\n");
          }
        }
        case SOLVE -> {
          if (builder != null) {
            b.append(builder.constraintText());
          }
          if (bound != null) {
            b.append("constraint ").append(bound).append(";\n");
          }
          if (satisfy) {
            b.append("solve").append(staticSearch(item.decl.annotations)).append(" satisfy;\n");
          } else {
            b.append(item.text).append(";\n");
          }
        }
        case VARIABLE -> {
          String t = item.text;
          if (item.decl.name.equals(objective) && !item.decl.annotations.contains("output_var")) {
            Matcher m =
                Pattern.compile("(:\\s*" + Pattern.quote(objective) + ")(?=\\s*(::|=|$))")
                    .matcher(t);
            t = m.replaceFirst("$1 :: output_var");
          }
          b.append(t).append(";\n");
        }
        default -> b.append(item.text).append(";\n");
      }
    }
    return b.toString();
  }

  private static final Pattern DYNAMIC_VARIABLE_CHOICE =
      Pattern.compile(
          "\\b(first_fail|anti_first_fail|smallest|largest|occurrence|most_constrained|max_regret"
              + "|dom_w_deg|[a-z_]*(afc|activity|action|weighted_degree|impact)[a-z_]*)\\b");
  private static final Pattern DYNAMIC_VALUE_CHOICE =
      Pattern.compile("\\b(indomain_middle|indomain_median|indomain_random|indomain)\\b");

  /**
   * Turns the search annotations into a static search: input order and smallest value first (except
   * where the value order is already static), so that every model of a problem lists its solutions
   * in the same order.
   */
  static String staticSearch(String annotations) {
    String s = DYNAMIC_VARIABLE_CHOICE.matcher(annotations).replaceAll("input_order");
    return DYNAMIC_VALUE_CHOICE.matcher(s).replaceAll("indomain_min");
  }

  private Path write(String problem, String tag, String text) throws IOException {
    Path dir = out.resolve("tmp");
    Files.createDirectories(dir);
    Path file =
        Files.createTempFile(
            dir,
            problem.replace('/', '_') + "__" + tag.replaceAll("[^A-Za-z0-9_-]", "_") + "__",
            ".fzn");
    Files.writeString(file, text, StandardCharsets.UTF_8);
    return file;
  }

  private static List<String> options(Path fzn) throws IOException {
    Path opt = fzn.getParent().resolve("options.opt");
    if (!Files.exists(opt)) {
      return List.of();
    }
    List<String> lines = Files.readAllLines(opt);
    return List.of(lines.get(0).strip(), lines.get(1).strip());
  }

  private static String oneLine(String s) {
    String t = s.replace('\n', ' ').strip();
    return t.length() > 300 ? t.substring(0, 300) + "..." : t;
  }

  private static Set<String> csv(String s) {
    return s.isBlank() ? Set.of() : Set.copyOf(Arrays.asList(s.split("\\s*,\\s*")));
  }

  private static String now() {
    return Instant.now().truncatedTo(ChronoUnit.SECONDS).toString();
  }

  static String sha(String text) {
    try {
      byte[] h = MessageDigest.getInstance("SHA-256").digest(text.getBytes(StandardCharsets.UTF_8));
      return HexFormat.of().formatHex(h, 0, 8);
    } catch (NoSuchAlgorithmException e) {
      throw new IllegalStateException(e);
    }
  }
}
