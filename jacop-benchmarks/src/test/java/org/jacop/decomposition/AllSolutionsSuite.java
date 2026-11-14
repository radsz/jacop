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
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Instant;
import java.time.temporal.ChronoUnit;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;
import java.util.zip.GZIPInputStream;
import org.jacop.decomposition.FznBuilder.Term;
import org.jacop.decomposition.FznModel.Constraint;
import org.jacop.decomposition.FznModel.Expr;
import org.jacop.decomposition.FznModel.Ident;
import org.junit.jupiter.api.Test;

/**
 * The all-solutions suite: small problems whose every solution JaCoP finds within the time limit,
 * solved again in other ways that must give exactly the same solutions. A bug that removes a
 * solution, or lets a wrong one through, shows as a difference.
 *
 * <p>For each problem (FlatZinc, smallest files first), an optimisation problem is first solved to
 * its best value {@code v} and turned into the satisfaction problem {@code objective <= v} ({@code
 * >=} for maximisation). Then:
 *
 * <ol>
 *   <li>the reference run enumerates every solution with JaCoP's own constraints, a static search
 *       ({@code input_order}, {@code indomain_min}) and no option; the problem joins the suite only
 *       when this run finishes within {@code suite.timeout};
 *   <li>{@code all:f}: the same with free search ({@code -a -f}) must give the same set;
 *   <li>{@code decomp:C}: for every global constraint {@code C} of the problem, the model with all
 *       occurrences of {@code C} replaced by MiniZinc's standard decomposition ({@link
 *       StdDecompositions}) must give the same set;
 *   <li>{@code objK:MODE}: LCG cannot enumerate solutions, so solution sets are compared through
 *       random linear objectives over the output variables. The minimum of objective {@code K} over
 *       the reference solutions is known; the native model minimised with {@code MODE} ({@code
 *       plain}, {@code f}, {@code lcg}, {@code lcg-f}) and each decomposed model with {@code --lcg}
 *       must prove the same minimum, and every solution they print must be one of the reference
 *       solutions.
 * </ol>
 *
 * <p>Problems are picked to keep the suite balanced across constraints: the next problem is the
 * smallest one that contains the global constraint with the fewest suite problems so far, with at
 * most {@code suite.familyCap} problems per model directory and {@code suite.cap} per constraint.
 * Every result is appended to the state file as soon as it is known; a new run continues where the
 * last one stopped. {@code suite.report} writes the coverage table.
 *
 * <p>It is a tool, not part of the build:
 *
 * <pre>
 * mvn -Pmin -pl jacop-benchmarks test -Dtest=AllSolutionsSuite -Dsurefire.rerunFailingTestsCount=0 \
 *     -Dsuite.threads=3 -Dsuite.roots=jacop=src/test/fz
 * </pre>
 *
 * <p>Properties: {@code suite.roots} ({@code name=dir,...}, FlatZinc files {@code *.fzn} and {@code
 * *.fzn.gz} below each dir), {@code suite.state}, {@code suite.timeout} (seconds per run, 300),
 * {@code suite.solutions} (solution limit of a counting run, 2000000), {@code suite.threads} (1),
 * {@code suite.cap} (30), {@code suite.familyCap} (3), {@code suite.maxBytes} (largest FlatZinc
 * file, 1000000), {@code suite.maxDecomposedBytes} (largest decomposed file, 50000000), {@code
 * suite.objectives} (2), {@code suite.maxProblems}, {@code suite.hours} (stop picking new problems
 * after this time), {@code suite.problems} (regular expression on names), {@code suite.retry}
 * (verdicts to check again), {@code suite.report} (coverage file), {@code suite.mznlib} (JaCoP's
 * MiniZinc library, for the list of all constraints), {@code suite.out} (models of differences).
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
class AllSolutionsSuite {

  private static final String FZ = "src/test/fz/";
  private static final Pattern GLOBAL = Pattern.compile("\\b(jacop_[a-z0-9_]+)\\s*\\(");

  private final int timeoutMillis =
      Integer.parseInt(System.getProperty("suite.timeout", "300")) * 1000;
  private final int solutionLimit =
      Integer.parseInt(System.getProperty("suite.solutions", "2000000"));
  private final int threads = Integer.parseInt(System.getProperty("suite.threads", "1"));
  private final int cap = Integer.parseInt(System.getProperty("suite.cap", "30"));
  private final int familyCap = Integer.parseInt(System.getProperty("suite.familyCap", "3"));
  private final long maxBytes = Long.parseLong(System.getProperty("suite.maxBytes", "1000000"));
  private final boolean allOutput =
      Boolean.parseBoolean(System.getProperty("suite.allOutput", "true"));
  private final int objectives = Integer.parseInt(System.getProperty("suite.objectives", "2"));
  private final int maxProblems =
      Integer.parseInt(System.getProperty("suite.maxProblems", "" + Integer.MAX_VALUE));
  private final long deadline =
      System.currentTimeMillis()
          + (long) (Double.parseDouble(System.getProperty("suite.hours", "1000000")) * 3_600_000);
  private final Pattern problemFilter = Pattern.compile(System.getProperty("suite.problems", ".*"));
  // largest decomposed FlatZinc file to run
  private final long maxDecomposedBytes = Long.getLong("suite.maxDecomposedBytes", 50_000_000L);

  private final Set<String> retry =
      new HashSet<>(
          Arrays.stream(System.getProperty("suite.retry", "").split(","))
              .filter(v -> !v.isEmpty())
              .toList());
  private final Path statePath =
      Path.of(System.getProperty("suite.state", FZ + "decomposition/suite-state.tsv"));
  private final List<Path> stateRead =
      Arrays.stream(System.getProperty("suite.stateRead", "").split(","))
          .filter(v -> !v.isEmpty())
          .map(Path::of)
          .toList();
  private final Path reportPath =
      Path.of(System.getProperty("suite.report", FZ + "decomposition/suite-coverage.md"));
  private final Path twins =
      System.getProperty("suite.twins") == null ? null : Path.of(System.getProperty("suite.twins"));
  private final Map<Path, String> twinNames = new HashMap<>();
  private final Path out = Path.of(System.getProperty("suite.out", "target/all-solutions-suite"));
  private final Path mznlib =
      Path.of(
          System.getProperty(
              "suite.mznlib", "../jacop-flatzinc/src/main/minizinc/org/jacop/minizinc"));

  /** A FlatZinc file that may join the suite. */
  record Candidate(
      String name, Path path, long size, Set<String> globals, String family, String sha) {}

  /** Last problem record of each problem: P name sha kind objective status ... */
  private final Map<String, String[]> problems = new HashMap<>();

  /** Checks done: name + '\t' + check -> record. */
  private final Map<String, String[]> checks = new HashMap<>();

  private final Map<String, Integer> coverage = new TreeMap<>();
  private final Map<String, Integer> familyCount = new HashMap<>();
  private final Set<String> inFlight = new HashSet<>();
  private final Set<String> attempted = new HashSet<>();
  private final List<Candidate> candidates = new ArrayList<>();
  private int started;

  @Test
  void suite() throws Exception {
    run();
  }

  public static void main(String[] args) throws Exception {
    new AllSolutionsSuite().run();
  }

  void run() throws Exception {
    Files.createDirectories(out.resolve("tmp"));
    readState();
    if (!Boolean.getBoolean("suite.reportOnly")) {
      scan();
      ExecutorService pool = Executors.newFixedThreadPool(threads);
      for (int t = 0; t < threads; t++) {
        pool.submit(this::worker);
      }
      pool.shutdown();
      pool.awaitTermination(365, TimeUnit.DAYS);
    }
    report();
  }

  // ---------------------------------------------------------------------------------------------
  // State.

  private void readState() throws IOException {
    if (!Files.exists(statePath)) {
      Files.createDirectories(statePath.toAbsolutePath().getParent());
      Files.writeString(
          statePath,
          "# All-solutions suite state, see AllSolutionsSuite. Tab-separated.\n"
              + "# P problem sha kind objective status solutions distinct digest millis timeout"
              + " date globals\n"
              + "# C problem sha check verdict status solutions millis date note\n");
    }
    List<Path> files = new ArrayList<>();
    for (Path p : stateRead) {
      if (Files.isDirectory(p)) {
        try (Stream<Path> s = Files.list(p)) {
          s.filter(f -> f.toString().endsWith(".tsv") || f.toString().endsWith(".tsv.gz"))
              .sorted()
              .forEach(files::add);
        }
      } else {
        files.add(p);
      }
    }
    files.removeIf(
        f -> f.toAbsolutePath().normalize().equals(statePath.toAbsolutePath().normalize()));
    files.add(statePath);
    for (Path file : files) {
      readStateFile(file);
    }
    for (String[] p : problems.values()) {
      if ("COMPLETE".equals(p[5])) {
        qualified(p);
      }
    }
  }

  private void readStateFile(Path file) throws IOException {
    List<String> lines;
    if (file.toString().endsWith(".gz")) {
      try (InputStream in = new GZIPInputStream(Files.newInputStream(file))) {
        lines = new String(in.readAllBytes(), StandardCharsets.UTF_8).lines().toList();
      }
    } else {
      lines = Files.readAllLines(file);
    }
    for (String line : lines) {
      if (line.isBlank() || line.startsWith("#")) {
        continue;
      }
      String[] f = line.split("\t", -1);
      if ("P".equals(f[0])) {
        problems.put(f[1], f);
      } else if ("C".equals(f[0])) {
        checks.put(f[1] + "\t" + f[2] + "\t" + f[3], f);
      }
    }
  }

  private void qualified(String[] p) {
    for (String g : globals(p)) {
      coverage.merge(g, 1, Integer::sum);
    }
    familyCount.merge(family(p[1]), 1, Integer::sum);
  }

  private static Set<String> globals(String[] p) {
    return p.length < 13 || p[12].isEmpty() ? Set.of() : new TreeSet<>(List.of(p[12].split(",")));
  }

  private synchronized void append(String... fields) {
    try {
      Files.writeString(
          statePath,
          String.join("\t", fields).replace('\n', ' ') + "\n",
          StandardCharsets.UTF_8,
          java.nio.file.StandardOpenOption.APPEND);
    } catch (IOException e) {
      throw new IllegalStateException(e);
    }
    if ("P".equals(fields[0])) {
      problems.put(fields[1], fields);
    } else {
      checks.put(fields[1] + "\t" + fields[2] + "\t" + fields[3], fields);
    }
  }

  // ---------------------------------------------------------------------------------------------
  // Candidates and the choice of the next problem.

  private void scan() throws IOException {
    String roots = System.getProperty("suite.roots", "jacop=" + FZ);
    for (String root : roots.split(",")) {
      int eq = root.indexOf('=');
      String prefix = root.substring(0, eq).strip();
      Path dir = Path.of(root.substring(eq + 1).strip());
      List<Path> files;
      try (Stream<Path> s = Files.walk(dir)) {
        files =
            s.filter(p -> p.toString().endsWith(".fzn") || p.toString().endsWith(".fzn.gz"))
                .filter(p -> !p.toString().contains("/decomposition/"))
                .filter(p -> !p.toString().contains(".std.fzn"))
                .toList();
      }
      for (Path p : files) {
        long size = Files.size(p) * (p.toString().endsWith(".gz") ? 8 : 1);
        String rel = dir.relativize(p).toString().replaceAll("\\.fzn(\\.gz)?$", "");
        String name = prefix + ":" + rel;
        if (size > maxBytes || !problemFilter.matcher(name).find()) {
          continue;
        }
        Set<String> globals = new TreeSet<>();
        String text = read(p);
        Matcher m = GLOBAL.matcher(text);
        while (m.find()) {
          globals.add(m.group(1));
        }
        twinNames.put(p, name);
        Path twin = twin(p);
        String sha = DecompositionCheck.sha(twin == null ? text : text + read(twin));
        candidates.add(new Candidate(name, p, size, globals, family(name), sha));
      }
    }
    candidates.sort(Comparator.comparingLong(Candidate::size).thenComparing(Candidate::name));
    System.out.println("AllSolutionsSuite: " + candidates.size() + " candidates");
  }

  private static String family(String name) {
    int slash = name.lastIndexOf('/');
    return slash < 0 ? name : name.substring(0, slash);
  }

  private boolean needsWork(Candidate c) {
    String[] p = problems.get(c.name);
    if (p == null || !p[2].equals(c.sha)) {
      return true;
    }
    if ("INCOMPLETE".equals(p[5])) {
      return Integer.parseInt(p[10]) < timeoutMillis / 1000;
    }
    if (retry.contains(p[5])) {
      return true;
    }
    if (retry.isEmpty()) {
      return false;
    }
    for (String[] k : checks.values()) {
      if (k[1].equals(c.name) && k[2].equals(p[2]) && retry.contains(k[4])) {
        return true;
      }
    }
    return false;
  }

  /** A family is given up once one of its instances no larger than this one was too slow. */
  private boolean tooSlowFamily(Candidate c) {
    for (Candidate d : candidates) {
      if (d.size > c.size) {
        return false;
      }
      String[] p = problems.get(d.name);
      if (d != c
          && d.family.equals(c.family)
          && p != null
          && "INCOMPLETE".equals(p[5])
          && Integer.parseInt(p[10]) >= timeoutMillis / 1000) {
        return true;
      }
    }
    return false;
  }

  private synchronized Candidate next() {
    if (started >= maxProblems || System.currentTimeMillis() > deadline) {
      return null;
    }
    Candidate best = null;
    int bestNeed = Integer.MAX_VALUE;
    for (Candidate c : candidates) {
      if (c.globals.isEmpty() || attempted.contains(c.name) || !needsWork(c)) {
        continue;
      }
      if (familyCount.getOrDefault(c.family, 0) >= familyCap) {
        continue;
      }
      int need = Integer.MAX_VALUE;
      for (String g : c.globals) {
        need = Math.min(need, coverage.getOrDefault(g, 0));
      }
      if (need < bestNeed && need < cap && !tooSlowFamily(c)) {
        best = c;
        bestNeed = need;
      }
    }
    if (best != null) {
      started++;
      inFlight.add(best.name);
      attempted.add(best.name);
      // counted as covered while it runs, so that other threads pick other constraints
      for (String g : best.globals) {
        coverage.merge(g, 1, Integer::sum);
      }
      familyCount.merge(best.family, 1, Integer::sum);
    }
    return best;
  }

  private synchronized void done(Candidate c, boolean joined) {
    inFlight.remove(c.name);
    if (!joined) {
      for (String g : c.globals) {
        coverage.merge(g, -1, Integer::sum);
      }
      familyCount.merge(c.family, -1, Integer::sum);
    }
  }

  private void worker() {
    Candidate c;
    while ((c = next()) != null) {
      boolean joined = false;
      try {
        joined = check(c);
      } catch (Exception | StackOverflowError e) {
        System.out.println("  " + c.name + ": " + e);
        e.printStackTrace(System.out);
      }
      done(c, joined);
    }
  }

  // ---------------------------------------------------------------------------------------------
  // Checking one problem.

  /** A random linear objective over output variables and its minimum over the reference. */
  static final class Objective {
    final List<String> names = new ArrayList<>();
    final List<Integer> positions = new ArrayList<>();
    final List<Expr> vars = new ArrayList<>();
    final List<Long> weights = new ArrayList<>();
    long min = Long.MAX_VALUE;

    /** The same objective over the variables of the same names in another flattening. */
    Objective on(FznModel other) {
      Objective o = new Objective();
      for (int i = 0; i < names.size(); i++) {
        FznModel.Decl d = other.decls.get(names.get(i));
        if (d == null) {
          throw new UnsupportedOperationException("no " + names.get(i) + " in the other model");
        }
        o.names.add(names.get(i));
        o.positions.add(positions.get(i));
        o.vars.add(
            d.isArray
                ? other.elements(new Ident(d.name)).get(positions.get(i))
                : new Ident(d.name));
        o.weights.add(weights.get(i));
      }
      o.min = min;
      return o;
    }

    long value(Map<String, List<Long>> solution) {
      long v = 0;
      for (int i = 0; i < names.size(); i++) {
        List<Long> values = solution.get(names.get(i));
        if (values == null || values.size() <= positions.get(i)) {
          throw new IllegalStateException("no value of " + names.get(i) + " in a solution");
        }
        v += weights.get(i) * values.get(positions.get(i));
      }
      return v;
    }
  }

  private boolean check(Candidate c) throws IOException {
    String text = read(c.path);
    String sha = c.sha;
    FznModel model = FznModel.parse(allOutput ? printAll(text) : text);
    String globals = String.join(",", c.globals);
    String objective = "";
    long t0 = System.currentTimeMillis();
    if (!"satisfy".equals(model.solveKind) && model.constant(model.objective) == null) {
      if (!(model.objective instanceof Ident(String name))
          || model.decls.get(name) == null
          || model.decls.get(name).type != FznModel.BaseType.INT) {
        problem(c, sha, model, "", "UNSUPPORTED", null, 0, globals);
        return false;
      }
      Path opt =
          write(c, "optimise", DecompositionCheck.render(model, Set.of(), null, null, false, true));
      SolverRun r = settle(SolverRun.run(opt, List.of(), false, 0, timeoutMillis));
      Files.deleteIfExists(opt);
      String value = SolverRun.value(r.lastSolution, name);
      if (r.status == SolverRun.Status.ERROR || value == null && r.solutions > 0) {
        problem(c, sha, model, "", "ERROR", r, System.currentTimeMillis() - t0, globals);
        System.out.println("  " + c.name + ": optimisation run failed " + r.error);
        return false;
      }
      objective = value == null ? "" : value;
    }
    String bound = bound(model, objective);
    List<Objective> objs = objectives(model, sha);
    // the same model flattened with MiniZinc's standard library, when there is one
    Set<String> printed = outputNames(allOutput ? FznModel.parse(text) : model);
    Path twin = printed.isEmpty() ? null : twin(c.path);
    FznModel parsedTwin = twin == null ? null : FznModel.parse(read(twin));
    if (parsedTwin != null) {
      // a variable that one flattening prints and the other turns into a constant or removes
      printed.retainAll(outputNames(parsedTwin));
    }
    FznModel std = printed.isEmpty() ? null : parsedTwin;
    List<Objective> stdObjs = std == null ? List.of() : objectives(model, sha, printed, 1, 7919);
    Set<Long> projections = new HashSet<>();
    Path refFile =
        write(c, "ref", DecompositionCheck.render(model, Set.of(), null, bound, true, false));
    SolverRun ref =
        SolverRun.run(
            refFile,
            List.of(),
            true,
            solutionLimit,
            timeoutMillis,
            s -> {
              Map<String, List<Long>> v = values(model, s);
              for (Objective o : objs) {
                o.min = Math.min(o.min, o.value(v));
              }
              if (std != null) {
                projections.add(projection(s, printed));
                for (Objective o : stdObjs) {
                  o.min = Math.min(o.min, o.value(v));
                }
              }
            });
    settle(ref);
    Files.deleteIfExists(refFile);
    if (ref.status == SolverRun.Status.COMPLETE && ref.solutions >= solutionLimit) {
      ref.status = SolverRun.Status.INCOMPLETE;
    }
    problem(c, sha, model, objective, ref.status.name(), ref, ref.millis, globals);
    System.out.println(
        "  "
            + c.name
            + " ["
            + globals
            + "] reference "
            + ref.status
            + " "
            + ref.solutions
            + " solutions in "
            + ref.millis
            + " ms");
    if (ref.status != SolverRun.Status.COMPLETE) {
      return false;
    }

    // every solution with free search
    countCheck(c, sha, model, bound, ref, "all:f", Set.of(), null, List.of("-f"));
    // every solution with each global constraint decomposed
    Map<String, List<Integer>> occurrences = new LinkedHashMap<>();
    for (Constraint k : model.constraints) {
      if (k.name().startsWith("jacop_")) {
        occurrences.computeIfAbsent(k.name(), x -> new ArrayList<>()).add(k.index());
      }
    }
    Map<String, FznBuilder> decomposed = new LinkedHashMap<>();
    for (Map.Entry<String, List<Integer>> e : occurrences.entrySet()) {
      String check = "decomp:" + e.getKey();
      if (!StdDecompositions.supports(e.getKey())) {
        record(c, sha, check, "NO_DECOMPOSITION", null, "");
        continue;
      }
      try {
        decomposed.put(e.getKey(), decompose(model, e.getValue()));
      } catch (UnsupportedOperationException | IllegalArgumentException ex) {
        record(c, sha, check, "UNSUPPORTED", null, ex.getMessage());
        continue;
      }
      countCheck(
          c,
          sha,
          model,
          bound,
          ref,
          check,
          Set.copyOf(e.getValue()),
          decomposed.get(e.getKey()),
          List.of());
    }
    if (std != null) {
      stdChecks(c, sha, std, objective, ref, projections, printed, stdObjs);
    }
    // the same solutions with LCG and the other modes, through random objectives
    for (int k = 0; k < objs.size(); k++) {
      Objective o = objs.get(k);
      for (String mode : List.of("plain", "f", "lcg", "lcg-f")) {
        objectiveCheck(c, sha, model, bound, ref, o, "obj" + k + ":" + mode, Set.of(), null, mode);
      }
      if (k == 0) {
        for (Map.Entry<String, FznBuilder> e : decomposed.entrySet()) {
          objectiveCheck(
              c,
              sha,
              model,
              bound,
              ref,
              o,
              "obj" + k + ":lcg:decomp:" + e.getKey(),
              Set.copyOf(occurrences.get(e.getKey())),
              decompose(model, occurrences.get(e.getKey())),
              "lcg");
        }
      }
    }
    return true;
  }

  private void problem(
      Candidate c,
      String sha,
      FznModel model,
      String objective,
      String status,
      SolverRun r,
      long millis,
      String globals) {
    append(
        "P",
        c.name,
        sha,
        model.solveKind,
        objective,
        status,
        r == null ? "" : "" + r.solutions,
        r == null ? "" : "" + r.distinctCount(),
        r == null ? "" : r.digest(),
        "" + millis,
        "" + timeoutMillis / 1000,
        now(),
        globals);
  }

  private boolean done(Candidate c, String sha, String check) {
    String[] f = checks.get(c.name + "\t" + sha + "\t" + check);
    return f != null && !retry.contains(f[4]);
  }

  private void record(
      Candidate c, String sha, String check, String verdict, SolverRun r, String n) {
    append(
        "C",
        c.name,
        sha,
        check,
        verdict,
        r == null ? "" : r.status.name(),
        r == null ? "" : "" + r.solutions,
        r == null ? "" : "" + r.millis,
        now(),
        n == null ? "" : n);
    if (!"PASS".equals(verdict) && !"PARTIAL".equals(verdict)) {
      System.out.println("  " + c.name + " " + check + ": " + verdict + " " + n);
    }
  }

  private static String bound(FznModel model, String objective) {
    if ("satisfy".equals(model.solveKind) || objective.isEmpty()) {
      return null;
    }
    String obj = FznModel.render(model.objective);
    return "minimize".equals(model.solveKind)
        ? "int_le(" + obj + "," + objective + ")"
        : "int_le(" + objective + "," + obj + ")";
  }

  private static FznBuilder decompose(FznModel model, List<Integer> indices) {
    FznBuilder builder = new FznBuilder(model, "X_DECOMP_");
    for (int i : indices) {
      Constraint k = model.constraints.get(i);
      StdDecompositions.decompose(builder, k.name(), k.args());
    }
    return builder;
  }

  private void countCheck(
      Candidate c,
      String sha,
      FznModel model,
      String bound,
      SolverRun ref,
      String check,
      Set<Integer> replaced,
      FznBuilder builder,
      List<String> options)
      throws IOException {
    if (done(c, sha, check)) {
      return;
    }
    String text = DecompositionCheck.render(model, replaced, builder, bound, true, false);
    if (text.length() > maxDecomposedBytes) {
      // a time decomposition of a long horizon: JaCoP runs out of memory reading it
      record(c, sha, check, "UNSUPPORTED", null, "decomposition of " + text.length() + " bytes");
      return;
    }
    Path file = write(c, check, text);
    SolverRun r = settle(SolverRun.run(file, options, true, solutionLimit, timeoutMillis));
    String verdict;
    String note = "";
    Set<Long> extra = new HashSet<>(r.hashes());
    extra.removeAll(ref.hashes());
    if (r.status == SolverRun.Status.ERROR) {
      verdict = "ERROR";
      note = r.error;
    } else if (!extra.isEmpty()) {
      verdict = "WRONG";
      note = extra.size() + " solutions that the reference does not have";
    } else if (r.status == SolverRun.Status.COMPLETE && r.distinctCount() < ref.distinctCount()) {
      verdict = "MISSED";
      note = "finished with " + r.distinctCount() + " of " + ref.distinctCount() + " solutions";
    } else if (r.status == SolverRun.Status.COMPLETE) {
      // a variable that MiniZinc marks as defined by a half-reification (int_eq_imp) is free when
      // its condition holds, is not printed, and gives the reference repeated printed solutions;
      // a search that labels only the printed variables then prints each once
      boolean refRepeats = ref.solutions != ref.distinctCount();
      boolean same =
          refRepeats ? r.distinctCount() == ref.distinctCount() : r.solutions == ref.solutions;
      verdict = same ? "PASS" : "DUPLICATES";
      note = verdict.equals("PASS") ? "" : r.solutions + " printed, " + ref.solutions + " expected";
    } else {
      verdict = "PARTIAL";
      note = r.distinctCount() + " of " + ref.distinctCount() + " solutions before the limit";
    }
    keep(c, check, verdict, text, options, ref, r);
    Files.deleteIfExists(file);
    record(c, sha, check, verdict, r, note);
  }

  private void objectiveCheck(
      Candidate c,
      String sha,
      FznModel model,
      String bound,
      SolverRun ref,
      Objective o,
      String check,
      Set<Integer> replaced,
      FznBuilder builder,
      String mode)
      throws IOException {
    if (done(c, sha, check)) {
      return;
    }
    FznBuilder b = builder == null ? new FznBuilder(model, "X_DECOMP_") : builder;
    Term obj = objectiveTerm(b, o);
    String text = DecompositionCheck.render(model, replaced, b, bound, true, false);
    if (text.length() > maxDecomposedBytes) {
      record(c, sha, check, "UNSUPPORTED", null, "decomposition of " + text.length() + " bytes");
      return;
    }
    int solve = text.lastIndexOf("satisfy;");
    text = text.substring(0, solve) + "minimize " + obj.text() + ";\n";
    List<String> options =
        switch (mode) {
          case "f" -> List.of("-f", "--lcg", "off");
          case "lcg" -> List.of("--lcg");
          case "lcg-f" -> List.of("--lcg", "-f");
          default -> List.of("--lcg", "off");
        };
    Path file = write(c, check, text);
    SolverRun r = settle(SolverRun.run(file, options, false, 0, timeoutMillis));
    Set<Long> extra = new HashSet<>(r.hashes());
    extra.removeAll(ref.hashes());
    String verdict;
    String note = "";
    if (r.status == SolverRun.Status.ERROR) {
      verdict = "ERROR";
      note = r.error;
    } else if (!extra.isEmpty()) {
      verdict = "WRONG";
      note = extra.size() + " printed solutions that the reference does not have";
    } else if (ref.solutions == 0) {
      verdict = r.status == SolverRun.Status.COMPLETE ? "PASS" : "PARTIAL";
    } else if (r.status == SolverRun.Status.COMPLETE && r.solutions == 0) {
      verdict = "MISSED";
      note = "reports no solution, the reference has " + ref.distinctCount();
    } else if (r.status == SolverRun.Status.COMPLETE) {
      long v = o.value(values(model, r.lastSolution));
      verdict = v == o.min ? "PASS" : "MISSED";
      note = v == o.min ? "" : "proved minimum " + v + ", the reference has " + o.min;
    } else {
      verdict = "PARTIAL";
    }
    keep(c, check, verdict, text, options, ref, r);
    Files.deleteIfExists(file);
    record(c, sha, check, verdict, r, note);
  }

  /**
   * The FlatZinc of the same model and data flattened with MiniZinc's standard library: {@code
   * <inst>.std.fzn} next to the file, or {@code <suite.twins>/<root>/<rel>.std.fzn}.
   */
  private Path twin(Path p) {
    String s = p.toString().replaceAll("\\.fzn(\\.gz)?$", "");
    for (String ext : List.of(".std.fzn", ".std.fzn.gz")) {
      Path t = Path.of(s + ext);
      if (Files.exists(t)) {
        return t;
      }
    }
    String name = twinNames.get(p);
    if (twins != null && name != null) {
      Path t = twins.resolve(name.replaceFirst(":", "/") + ".std.fzn");
      if (Files.exists(t)) {
        return t;
      }
    }
    return null;
  }

  /**
   * Names of the variables and arrays a model prints, without those MiniZinc introduced: the names
   * of introduced variables depend on the library a model was flattened with.
   */
  static Set<String> outputNames(FznModel model) {
    Set<String> names = new HashSet<>();
    for (FznModel.Item item : model.items) {
      FznModel.Decl d = item.decl;
      if (item.kind == FznModel.ItemKind.VARIABLE
          && d != null
          && !d.name.startsWith("X_INTRODUCED_")
          && (d.annotations.contains("output_var") || d.annotations.contains("output_array"))) {
        names.add(d.name);
      }
    }
    return names;
  }

  /** Hash of the printed lines of the given variables, in name order. */
  static long projection(String solution, Set<String> names) {
    List<String> lines = new ArrayList<>();
    for (String line : solution.split("\n")) {
      int eq = line.indexOf('=');
      if (eq > 0 && names.contains(line.substring(0, eq).strip())) {
        lines.add(line.strip());
      }
    }
    lines.sort(null);
    return SolverRun.hash(String.join("\n", lines));
  }

  /**
   * Checks the standard-library flattening: the same solutions with a static and with free search,
   * and the same minimum of a random objective with LCG.
   */
  private void stdChecks(
      Candidate c,
      String sha,
      FznModel std,
      String objective,
      SolverRun ref,
      Set<Long> projections,
      Set<String> printed,
      List<Objective> stdObjs)
      throws IOException {
    String bound = bound(std, objective);
    for (List<String> options : List.of(List.<String>of(), List.of("-f"))) {
      String check = options.isEmpty() ? "std" : "std:f";
      if (done(c, sha, check)) {
        continue;
      }
      String text = DecompositionCheck.render(std, Set.of(), null, bound, true, false);
      Path file = write(c, check, text);
      Set<Long> seen = new HashSet<>();
      SolverRun r =
          settle(
              SolverRun.run(
                  file,
                  options,
                  true,
                  solutionLimit,
                  timeoutMillis,
                  s -> seen.add(projection(s, printed))));
      Files.deleteIfExists(file);
      Set<Long> extra = new HashSet<>(seen);
      extra.removeAll(projections);
      String verdict;
      String note = "";
      if (r.status == SolverRun.Status.ERROR) {
        verdict = "ERROR";
        note = r.error;
      } else if (!extra.isEmpty()) {
        verdict = "WRONG";
        note = extra.size() + " solutions that the reference does not have";
      } else if (r.status == SolverRun.Status.COMPLETE && seen.size() < projections.size()) {
        verdict = "MISSED";
        note = "finished with " + seen.size() + " of " + projections.size() + " solutions";
      } else if (r.status == SolverRun.Status.COMPLETE) {
        verdict = "PASS";
      } else {
        verdict = "PARTIAL";
        note = seen.size() + " of " + projections.size() + " solutions before the limit";
      }
      if (!"PASS".equals(verdict) && !"PARTIAL".equals(verdict)) {
        Files.writeString(
            out.resolve(c.name.replaceAll("[^A-Za-z0-9_.-]", "_") + "__" + check + ".fzn"),
            "% " + verdict + " " + note + " options " + options + "\n" + text);
      }
      record(c, sha, check, verdict, r, note);
    }
    if (stdObjs.isEmpty() || done(c, sha, "objstd:lcg")) {
      return;
    }
    Objective o;
    try {
      o = stdObjs.get(0).on(std);
    } catch (UnsupportedOperationException | IndexOutOfBoundsException e) {
      record(c, sha, "objstd:lcg", "UNSUPPORTED", null, e.getMessage());
      return;
    }
    FznBuilder b = new FznBuilder(std, "X_DECOMP_");
    Term obj = objectiveTerm(b, o);
    String text = DecompositionCheck.render(std, Set.of(), b, bound, true, false);
    text = text.substring(0, text.lastIndexOf("satisfy;")) + "minimize " + obj.text() + ";\n";
    Path file = write(c, "objstd", text);
    Set<Long> seen = new HashSet<>();
    SolverRun r =
        settle(
            SolverRun.run(
                file,
                List.of("--lcg"),
                false,
                0,
                timeoutMillis,
                s -> seen.add(projection(s, printed))));
    Files.deleteIfExists(file);
    seen.removeAll(projections);
    String verdict;
    String note = "";
    if (r.status == SolverRun.Status.ERROR) {
      verdict = "ERROR";
      note = r.error;
    } else if (!seen.isEmpty()) {
      verdict = "WRONG";
      note = seen.size() + " printed solutions that the reference does not have";
    } else if (projections.isEmpty()) {
      verdict = r.status == SolverRun.Status.COMPLETE ? "PASS" : "PARTIAL";
    } else if (r.status == SolverRun.Status.COMPLETE && r.solutions == 0) {
      verdict = "MISSED";
      note = "reports no solution";
    } else if (r.status == SolverRun.Status.COMPLETE) {
      long v = o.value(values(std, r.lastSolution));
      verdict = v == o.min ? "PASS" : "MISSED";
      note = v == o.min ? "" : "proved minimum " + v + ", the reference has " + o.min;
    } else {
      verdict = "PARTIAL";
    }
    if (!"PASS".equals(verdict) && !"PARTIAL".equals(verdict)) {
      Files.writeString(
          out.resolve(c.name.replaceAll("[^A-Za-z0-9_.-]", "_") + "__objstd.fzn"),
          "% " + verdict + " " + note + "\n" + text);
    }
    record(c, sha, "objstd:lcg", verdict, r, note);
  }

  /** Keeps the model of a failed check, with the command line, for investigation. */
  private void keep(
      Candidate c,
      String check,
      String verdict,
      String text,
      List<String> options,
      SolverRun ref,
      SolverRun r)
      throws IOException {
    if ("PASS".equals(verdict) || "PARTIAL".equals(verdict)) {
      return;
    }
    String base = c.name.replaceAll("[^A-Za-z0-9_.-]", "_") + "__" + check.replace(':', '_');
    StringBuilder b = new StringBuilder();
    b.append("% ").append(verdict).append(" options ").append(options).append('\n');
    b.append("% error ").append(r.error).append('\n');
    int shown = 0;
    for (String s : r.distinct.keySet()) {
      if (!ref.contains(s) && shown++ < 3) {
        b.append("% only in this run:\n%   ").append(s.replace("\n", "\n%   ")).append('\n');
      }
    }
    shown = 0;
    for (String s : ref.distinct.keySet()) {
      if (!r.contains(s) && shown++ < 3) {
        b.append("% only in the reference:\n%   ").append(s.replace("\n", "\n%   ")).append('\n');
      }
    }
    Files.writeString(out.resolve(base + ".fzn"), b + text);
  }

  // ---------------------------------------------------------------------------------------------
  // Random objectives.

  private List<Objective> objectives(FznModel model, String sha) {
    return objectives(model, sha, null, objectives, 0);
  }

  static List<Objective> objectives(
      FznModel model, String sha, Set<String> only, int count, long salt) {
    List<String> names = new ArrayList<>();
    List<Integer> positions = new ArrayList<>();
    List<Expr> vars = new ArrayList<>();
    for (FznModel.Item item : model.items) {
      FznModel.Decl d = item.decl;
      if (item.kind != FznModel.ItemKind.VARIABLE
          || d == null
          || d.type == FznModel.BaseType.FLOAT
          || d.type == FznModel.BaseType.SET
          || !(d.annotations.contains("output_var") || d.annotations.contains("output_array"))
          || only != null && !only.contains(d.name)) {
        continue;
      }
      List<Expr> elements =
          d.isArray ? model.elements(new Ident(d.name)) : List.of(new Ident(d.name));
      for (int i = 0; i < elements.size(); i++) {
        if (model.constant(elements.get(i)) == null) {
          names.add(d.name);
          positions.add(i);
          vars.add(elements.get(i));
        }
      }
    }
    List<Objective> result = new ArrayList<>();
    if (names.isEmpty()) {
      return result;
    }
    Random random = new Random(Long.parseUnsignedLong(sha, 16) + salt);
    for (int k = 0; k < count; k++) {
      Objective o = new Objective();
      int terms = Math.min(names.size(), 3 + random.nextInt(18));
      Set<Integer> picked = new LinkedHashSet<>();
      while (picked.size() < terms) {
        picked.add(random.nextInt(names.size()));
      }
      for (int i : picked) {
        o.names.add(names.get(i));
        o.positions.add(positions.get(i));
        o.vars.add(vars.get(i));
        long w = 1 + random.nextInt(4);
        o.weights.add(random.nextBoolean() ? w : -w);
      }
      result.add(o);
    }
    return result;
  }

  static Term objectiveTerm(FznBuilder b, Objective o) {
    List<Term> terms = new ArrayList<>();
    long[] coefs = new long[o.vars.size() + 1];
    long lo = 0;
    long hi = 0;
    boolean bounded = true;
    for (int i = 0; i < o.vars.size(); i++) {
      Term t = b.term(o.vars.get(i));
      if (t.bool()) {
        Term v = b.newInt(0, 1);
        b.post("bool2int", t, v);
        t = v;
      }
      terms.add(t);
      long w = o.weights.get(i);
      coefs[i] = w;
      if (b.bounded(t)) {
        lo += Math.min(w * b.lb(t), w * b.ub(t));
        hi += Math.max(w * b.lb(t), w * b.ub(t));
      } else {
        bounded = false;
      }
    }
    Term obj = bounded ? b.newInt(lo, hi) : b.newInt(-FznBuilder.UNBOUNDED, FznBuilder.UNBOUNDED);
    terms.add(obj);
    coefs[o.vars.size()] = -1;
    b.linear(coefs, terms, "eq", 0);
    return obj;
  }

  /** The integer and Boolean values of a printed solution, by output name. */
  static Map<String, List<Long>> values(FznModel model, String solution) {
    Map<String, List<Long>> result = new HashMap<>();
    for (String line : solution.split("\n")) {
      int eq = line.indexOf('=');
      FznModel.Decl d = eq < 0 ? null : model.decls.get(line.substring(0, eq).strip());
      if (d == null || d.type == FznModel.BaseType.FLOAT || d.type == FznModel.BaseType.SET) {
        continue;
      }
      String value = line.substring(eq + 1).strip();
      value = value.endsWith(";") ? value.substring(0, value.length() - 1) : value;
      Expr parsed = new FznModel.Lexer(value).expr();
      List<Expr> elements;
      if (d.isArray) {
        if (!(parsed instanceof FznModel.Call(_, List<Expr> args))
            || !(args.getLast() instanceof FznModel.ArrayLit(List<Expr> el))) {
          continue;
        }
        elements = el;
      } else {
        elements = List.of(parsed);
      }
      List<Long> values = new ArrayList<>();
      for (Expr e : elements) {
        values.add(
            switch (e) {
              case FznModel.IntLit(long v) -> v;
              case FznModel.BoolLit(boolean v) -> v ? 1L : 0L;
              default -> 0L;
            });
      }
      result.put(d.name, values);
    }
    return result;
  }

  // ---------------------------------------------------------------------------------------------
  // Coverage report.

  private static final Pattern BUILTIN =
      Pattern.compile("\\bpredicate\\s+(jacop_[a-z0-9_]+)\\s*\\(");

  /**
   * Returns the jacop_* predicates that a library file declares without a body, the ones that can
   * appear in FlatZinc; functions, tests and predicates with a body never do.
   */
  static Set<String> builtins(String library) {
    String text = library.replaceAll("%[^\\n]*", "");
    Set<String> names = new TreeSet<>();
    Matcher m = BUILTIN.matcher(text);
    while (m.find()) {
      int depth = 1;
      int i = m.end();
      while (i < text.length() && depth > 0) {
        char c = text.charAt(i++);
        if (c == '(') {
          depth++;
        } else if (c == ')') {
          depth--;
        }
      }
      while (i < text.length() && Character.isWhitespace(text.charAt(i))) {
        i++;
      }
      if (i < text.length() && text.charAt(i) == ';') {
        names.add(m.group(1));
      }
    }
    return names;
  }

  private void report() throws IOException {
    Set<String> universe = new TreeSet<>();
    if (Files.isDirectory(mznlib)) {
      try (Stream<Path> s = Files.walk(mznlib)) {
        for (Path p : s.filter(x -> x.toString().endsWith(".mzn")).toList()) {
          universe.addAll(builtins(Files.readString(p)));
        }
      }
    }
    Map<String, Integer> suite = new TreeMap<>();
    Map<String, Map<String, Integer>> verdicts = new TreeMap<>();
    for (String[] p : problems.values()) {
      if (!"COMPLETE".equals(p[5])) {
        continue;
      }
      for (String g : globals(p)) {
        suite.merge(g, 1, Integer::sum);
      }
    }
    Map<String, Integer> totals = new TreeMap<>();
    for (String[] k : checks.values()) {
      String[] p = problems.get(k[1]);
      if (p == null || !p[2].equals(k[2])) {
        continue;
      }
      totals.merge(k[4], 1, Integer::sum);
      String check = k[3];
      List<String> about = new ArrayList<>();
      int d = check.indexOf("decomp:");
      if (d >= 0) {
        about.add(check.substring(d + "decomp:".length()));
      } else {
        about.addAll(globals(p));
      }
      String kind =
          check.startsWith("decomp:")
              ? "decomp"
              : check.contains(":lcg:decomp:") ? "decomp-lcg" : check.replaceAll("^obj\\d+:", "");
      for (String g : about) {
        verdicts.computeIfAbsent(g, x -> new TreeMap<>()).merge(kind + ":" + k[4], 1, Integer::sum);
      }
    }
    universe.addAll(suite.keySet());
    StringBuilder b = new StringBuilder();
    long joined = problems.values().stream().filter(p -> "COMPLETE".equals(p[5])).count();
    b.append("# All-solutions suite coverage\n\n");
    b.append("Generated by `AllSolutionsSuite` from `")
        .append(statePath.getFileName())
        .append("`. ")
        .append(joined)
        .append(" problems in the suite, ")
        .append(problems.size())
        .append(" tried. Check verdicts: ")
        .append(totals)
        .append(".\n\n");
    b.append(
        "| Constraint | Problems | decomp | decomp --lcg | all -f | plain | -f | --lcg | --lcg -f |"
            + " Not passed |\n");
    b.append("|---|---:|---:|---:|---:|---:|---:|---:|---:|---|\n");
    for (String g : universe) {
      Map<String, Integer> v = verdicts.getOrDefault(g, Map.of());
      StringBuilder bad = new StringBuilder();
      for (Map.Entry<String, Integer> e : v.entrySet()) {
        if (!e.getKey().endsWith(":PASS") && !e.getKey().endsWith(":PARTIAL")) {
          bad.append(e.getKey()).append(' ').append(e.getValue()).append("; ");
        }
      }
      b.append("| `")
          .append(g)
          .append("` | ")
          .append(suite.getOrDefault(g, 0))
          .append(" | ")
          .append(v.getOrDefault("decomp:PASS", 0))
          .append(" | ")
          .append(v.getOrDefault("decomp-lcg:PASS", 0))
          .append(" | ")
          .append(v.getOrDefault("all:f:PASS", 0))
          .append(" | ")
          .append(v.getOrDefault("plain:PASS", 0))
          .append(" | ")
          .append(v.getOrDefault("f:PASS", 0))
          .append(" | ")
          .append(v.getOrDefault("lcg:PASS", 0))
          .append(" | ")
          .append(v.getOrDefault("lcg-f:PASS", 0))
          .append(" | ")
          .append(bad.toString().strip())
          .append(" |\n");
    }
    Files.writeString(reportPath, b.toString());
    System.out.println("AllSolutionsSuite: " + joined + " problems, checks " + totals);
  }

  // ---------------------------------------------------------------------------------------------

  private static final Pattern SCALAR_VAR = Pattern.compile("(?m)^(var [^=;\\[]*?)\\s*;\\s*$");

  /**
   * Prints every scalar variable that no constraint defines, so that two solutions that differ only
   * in variables the model does not print are told apart.
   */
  static String printAll(String text) {
    Matcher m = SCALAR_VAR.matcher(text);
    StringBuilder b = new StringBuilder();
    while (m.find()) {
      String decl = m.group(1);
      String replacement =
          decl.contains("output_var") || decl.contains("is_defined_var")
              ? m.group()
              : decl + " :: output_var;";
      m.appendReplacement(b, Matcher.quoteReplacement(replacement));
    }
    m.appendTail(b);
    return b.toString();
  }

  /** A run that failed without finishing is an error, not a run stopped at a limit. */
  private static SolverRun settle(SolverRun r) {
    if (r.status == SolverRun.Status.INCOMPLETE
        && !r.error.isEmpty()
        && !r.error.startsWith("killed")) {
      r.status = SolverRun.Status.ERROR;
    }
    return r;
  }

  private static String read(Path p) throws IOException {
    if (p.toString().endsWith(".gz")) {
      try (InputStream in = new GZIPInputStream(Files.newInputStream(p))) {
        return new String(in.readAllBytes(), StandardCharsets.UTF_8);
      }
    }
    return Files.readString(p, StandardCharsets.UTF_8);
  }

  private Path write(Candidate c, String tag, String text) throws IOException {
    Path file =
        Files.createTempFile(
            out.resolve("tmp"),
            c.name.replaceAll("[^A-Za-z0-9_-]", "_") + "__" + tag.replaceAll("[^A-Za-z0-9_-]", "_"),
            ".fzn");
    Files.writeString(file, text, StandardCharsets.UTF_8);
    return file;
  }

  private static String now() {
    return Instant.now().truncatedTo(ChronoUnit.SECONDS).toString();
  }
}
