/*
 * SetFixpointTest.java
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

package org.jacop.set;

import static org.assertj.core.api.Assertions.assertThat;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.regex.Pattern;
import java.util.stream.Stream;
import org.jacop.api.SatisfiedPresent;
import org.jacop.constraints.And;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Eq;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.IfThenElse;
import org.jacop.constraints.Implies;
import org.jacop.constraints.Not;
import org.jacop.constraints.Or;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.Xor;
import org.jacop.core.FailException;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.Var;
import org.jacop.set.SetImposeGroundingHarness.Assignment;
import org.jacop.set.SetImposeGroundingHarness.Case;
import org.jacop.set.SetImposeGroundingHarness.Spec;
import org.jacop.set.constraints.AeqB;
import org.jacop.set.constraints.AeqS;
import org.jacop.set.constraints.AinB;
import org.jacop.set.constraints.AinS;
import org.jacop.set.constraints.AleB;
import org.jacop.set.constraints.AltB;
import org.jacop.set.constraints.EinA;
import org.jacop.set.constraints.SinA;
import org.jacop.set.constraints.XeqA;
import org.jacop.set.constraints.XinA;
import org.jacop.set.core.BoundSetDomain;
import org.jacop.set.core.SetDomain;
import org.jacop.set.core.SetVar;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/**
 * Checks that set constraints reach the fixpoint a fresh store reaches, as {@code
 * WakeUpFixpointTest} does for integer constraints. Every case of {@link SetImposeGroundingTest}
 * and {@link SetConsistencyCases}, and set relations composed with Reified, Not, And, Or, IfThen,
 * IfThenElse, Implies, Xor and Eq (with variables repeated at random), is imposed on small
 * variables and explored by random dives of decisions on set variables (element in, element out,
 * cardinality bounds) and integer variables ({@code =}, {@code !=}, {@code <=}, {@code >=}). At
 * every node:
 *
 * <ul>
 *   <li>the constraint imposed in a fresh store over the current domains prunes nothing more and
 *       does not fail: a missed wake-up event or a constraint that does not propagate its own
 *       pruning;
 *   <li>propagation keeps every solution of the box (brute force) and fails only without one;
 *   <li>{@code satisfied()} holds only when every tuple of the box is a solution, right after a
 *       decision and after propagation, and {@code notSatisfied()} of a primitive constraint only
 *       when none is.
 * </ul>
 *
 * <p>With one variable at two positions (the Repeated cases, or a composed relation such as {@code
 * v0 in v0}) only soundness counts, since a repeated variable may weaken a propagator.
 *
 * <p>Instances per case: {@code setfixpoint.instances} (default 300, 100 in the {@code min}
 * profile); {@code grounding.cases} selects cases by parts of their names. At volume:
 *
 * <pre>
 * mvn -Pmin -pl jacop-sets -am test -Dtest=SetFixpointTest -Dsurefire.failIfNoSpecifiedTests=false \
 *     -Dsurefire.rerunFailingTestsCount=0 -Dsetfixpoint.instances=10000
 * </pre>
 */
class SetFixpointTest {

  private static final int INSTANCES = Integer.getInteger("setfixpoint.instances", 300);

  private static final String FILTER = System.getProperty("grounding.cases", "");

  private static final int MAX_BOX = 50_000;

  /** A case or a composed relation with one set variable on both sides. */
  private static final Pattern REPEATED = Pattern.compile("^\\w*Repeated|\\bv(\\d) \\S+ v\\1\\b");

  static Stream<Arguments> cases() {
    return Stream.of(
            SetImposeGroundingTest.cases(), SetConsistencyCases.cases(), composedCases().stream())
        .flatMap(s -> s);
  }

  @ParameterizedTest(name = "{0}")
  @MethodSource("cases")
  void setConstraintsReachTheFreshFixpoint(String name, Function<Random, Case> generator) {
    Random random = new Random(name.hashCode() * 31L + 7);
    long nodes = 0;
    List<String> errors = new ArrayList<>();
    for (int run = 0; run < INSTANCES && errors.size() < 3; run++) {
      Case c = generator.apply(random);
      Store store = new Store();
      Var[] x = new Var[c.vars().length];
      for (int i = 0; i < x.length; i++) {
        x[i] = create(store, "v" + i, c.vars()[i]);
      }
      Constraint constraint;
      try {
        constraint = c.impose().apply(store, x);
      } catch (IllegalArgumentException _) {
        continue;
      }
      List<String> path = new ArrayList<>();
      String start = Arrays.toString(x);
      List<int[]> before = box(c, x);
      boolean ok;
      try {
        ok = store.consistency();
      } catch (FailException _) {
        ok = false;
      }
      for (int depth = 0; depth < 14; depth++) {
        nodes++;
        String at = name + " run " + run + " " + c.description() + " " + start + " then " + path;
        String error = checkNode(c, x, before, ok, constraint, at);
        if (error != null) {
          errors.add(error);
          break;
        }
        if (!ok) {
          break;
        }
        String decision = decide(store, x, random);
        if (decision == null) {
          break;
        }
        path.add(decision);
        before = box(c, x);
        if (constraint instanceof SatisfiedPresent sp
            && !before.isEmpty()
            && !before.stream().allMatch(t -> holds(c, t))
            && sp.satisfied()) {
          errors.add(at + " " + decision + ": satisfied() right after the decision, " + show(x));
          break;
        }
        try {
          ok = store.consistency();
        } catch (FailException _) {
          ok = false;
        }
      }
    }
    System.out.printf("%-28s nodes %6d%n", name, nodes);
    assertThat(errors).isEmpty();
  }

  private static String checkNode(
      Case c, Var[] x, List<int[]> before, boolean ok, Constraint constraint, String at) {
    boolean measured = !before.isEmpty();
    long solutionsBefore = before.stream().filter(t -> holds(c, t)).count();
    if (!ok) {
      return solutionsBefore > 0 ? at + ": failed with " + solutionsBefore + " solutions" : null;
    }
    List<int[]> now = box(c, x);
    long solutionsNow = now.stream().filter(t -> holds(c, t)).count();
    if (measured && !now.isEmpty() && solutionsNow < solutionsBefore) {
      return at + ": removed " + (solutionsBefore - solutionsNow) + " solutions, now " + show(x);
    }
    if (!now.isEmpty() || !measured) {
      boolean all = solutionsNow == now.size();
      if (constraint instanceof SatisfiedPresent sp && !now.isEmpty() && !all && sp.satisfied()) {
        return at + ": satisfied() with a tuple that is no solution, " + show(x);
      }
      if (constraint instanceof PrimitiveConstraint pc && solutionsNow > 0 && pc.notSatisfied()) {
        return at + ": notSatisfied() with " + solutionsNow + " solutions, " + show(x);
      }
    }
    // a repeated variable may weaken a propagator: only soundness counts then
    if (REPEATED.matcher(at).find()) {
      return null;
    }
    return fresh(c, x, at);
  }

  /** Imposes the case in a fresh store over the current domains; the difference, or null. */
  private static String fresh(Case c, Var[] x, String at) {
    Store store = new Store();
    Var[] y = new Var[x.length];
    for (int i = 0; i < x.length; i++) {
      if (x[i] instanceof IntVar v) {
        y[i] = new IntVar(store, "v" + i, v.dom().cloneLight());
      } else {
        SetDomain d = ((SetVar) x[i]).dom();
        y[i] =
            new SetVar(
                store,
                "v" + i,
                new BoundSetDomain(d.glb().cloneLight(), d.lub().cloneLight(), d.card()));
      }
    }
    boolean ok;
    try {
      c.impose().apply(store, y);
      ok = store.consistency();
    } catch (FailException _) {
      ok = false;
    } catch (IllegalArgumentException _) {
      return null;
    }
    if (!ok) {
      return at + ": a fresh store fails over " + show(x);
    }
    for (int i = 0; i < x.length; i++) {
      if (!same(x[i], y[i])) {
        return at + ": a fresh store prunes " + x[i] + " to " + y[i];
      }
    }
    return null;
  }

  private static boolean same(Var a, Var b) {
    if (a instanceof IntVar x) {
      return x.dom().eq(((IntVar) b).dom());
    }
    SetDomain d = ((SetVar) a).dom();
    SetDomain e = ((SetVar) b).dom();
    return d.glb().eq(e.glb()) && d.lub().eq(e.lub()) && card(d).eq(card(e));
  }

  private static IntDomain card(SetDomain d) {
    return d.card().intersect(d.glb().getSize(), d.lub().getSize());
  }

  private static String decide(Store store, Var[] x, Random random) {
    List<Integer> open = new ArrayList<>();
    for (int i = 0; i < x.length; i++) {
      if (!x[i].singleton()) {
        open.add(i);
      }
    }
    if (open.isEmpty()) {
      return null;
    }
    store.setLevel(store.level + 1);
    int i = open.get(random.nextInt(open.size()));
    try {
      if (x[i] instanceof IntVar v) {
        int[] vals = elements(v.dom());
        int value = vals[random.nextInt(vals.length)];
        switch (random.nextInt(4)) {
          case 0 -> {
            v.domain.in(store.level, v, value, value);
            return v.id() + "=" + value;
          }
          case 1 -> {
            v.domain.inComplement(store.level, v, value);
            return v.id() + "!=" + value;
          }
          case 2 -> {
            v.domain.inMax(store.level, v, value);
            return v.id() + "<=" + value;
          }
          default -> {
            v.domain.inMin(store.level, v, value);
            return v.id() + ">=" + value;
          }
        }
      }
      SetVar s = (SetVar) x[i];
      int[] free =
          Arrays.stream(elements(s.dom().lub())).filter(e -> !s.dom().glb().contains(e)).toArray();
      IntDomain card = card(s.dom());
      int kind = random.nextInt(free.length == 0 ? 1 : 5);
      if (kind == 0 && card.min() < card.max()) {
        int k = card.min() + random.nextInt(card.max() - card.min() + 1);
        switch (random.nextInt(3)) {
          case 0 -> {
            s.domain.inCardinality(store.level, s, k, k);
            return "#" + s.id() + "=" + k;
          }
          case 1 -> {
            s.domain.inCardinality(store.level, s, Integer.MIN_VALUE, k);
            return "#" + s.id() + "<=" + k;
          }
          default -> {
            s.domain.inCardinality(store.level, s, k, Integer.MAX_VALUE);
            return "#" + s.id() + ">=" + k;
          }
        }
      }
      if (free.length == 0) {
        store.setLevel(store.level - 1);
        return null;
      }
      int e = free[random.nextInt(free.length)];
      if (random.nextBoolean()) {
        s.domain.inGlb(store.level, s, e);
        return e + " in " + s.id();
      }
      s.domain.inLubComplement(store.level, s, e);
      return e + " notin " + s.id();
    } catch (FailException _) {
      // a decision that empties a domain: not taken
      store.removeLevel(store.level);
      store.setLevel(store.level - 1);
      return null;
    }
  }

  // ---------------------------------------------------------------------------------------------
  // composed set relations

  /** A primitive set relation over the variables of a composed case and its meaning. */
  private record Relation(
      Function<Var[], PrimitiveConstraint> make, Predicate<Assignment> meaning, String text) {}

  // the variables of a composed case: sets 0..2, integers 3..4, Booleans 5..6
  private static final int SETS = 3;
  private static final int INTS = 2;
  private static final int BOOLS = 2;

  private static List<Arguments> composedCases() {
    List<Arguments> cases = new ArrayList<>();
    String[] kinds = {
      "Reified",
      "Not",
      "And",
      "Or",
      "IfThen",
      "IfThenElse",
      "Implies",
      "Xor",
      "Eq",
      "NotAnd",
      "ReifiedOr",
      "ReifiedFixed"
    };
    for (String kind : kinds) {
      cases.add(Arguments.of("Composed" + kind, (Function<Random, Case>) r -> composed(kind, r)));
    }
    return cases.stream()
        .filter(
            a ->
                FILTER.isEmpty()
                    || Arrays.stream(FILTER.split(","))
                        .anyMatch(part -> a.get()[0].toString().contains(part)))
        .toList();
  }

  private static Case composed(String kind, Random r) {
    Spec[] vars = new Spec[SETS + INTS + BOOLS];
    for (int i = 0; i < SETS; i++) {
      int[] lub = values(r, 1, 4, r.nextInt(4));
      int[] glb = Arrays.stream(lub).filter(e -> r.nextInt(5) == 0).toArray();
      vars[i] = Spec.setVar(glb, lub);
    }
    for (int i = 0; i < INTS; i++) {
      vars[SETS + i] = Spec.intVar(values(r, 0, 5, 1 + r.nextInt(3)));
    }
    for (int i = 0; i < BOOLS; i++) {
      vars[SETS + INTS + i] = Spec.intVar(0, 1);
    }
    Relation p = relation(r);
    Relation q = relation(r);
    Relation s = relation(r);
    int b = SETS + INTS + r.nextInt(BOOLS);
    int fixed = r.nextInt(2);
    Function<Var[], Constraint> make;
    Predicate<Assignment> meaning;
    String text;
    switch (kind) {
      case "Reified" -> {
        make = x -> new Reified(p.make.apply(x), (IntVar) x[b]);
        meaning = t -> p.meaning.test(t) == (t.i(b) == 1);
        text = "reif(" + p.text + ", v" + b + ")";
      }
      case "ReifiedFixed" -> {
        // the Boolean of Reified is fixed before impose
        make =
            x -> {
              IntVar bv = (IntVar) x[b];
              bv.domain.in(bv.getStore().level, bv, fixed, fixed);
              return new Reified(p.make.apply(x), bv);
            };
        meaning = t -> t.i(b) == fixed && p.meaning.test(t) == (fixed == 1);
        text = "reif(" + p.text + ", v" + b + "=" + fixed + ")";
      }
      case "Not" -> {
        make = x -> new Not(p.make.apply(x));
        meaning = p.meaning.negate();
        text = "not(" + p.text + ")";
      }
      case "And" -> {
        make = x -> new And(p.make.apply(x), q.make.apply(x));
        meaning = p.meaning.and(q.meaning);
        text = "and(" + p.text + ", " + q.text + ")";
      }
      case "NotAnd" -> {
        make = x -> new Not(new And(p.make.apply(x), q.make.apply(x)));
        meaning = p.meaning.and(q.meaning).negate();
        text = "not(and(" + p.text + ", " + q.text + "))";
      }
      case "Or" -> {
        make = x -> new Or(p.make.apply(x), q.make.apply(x));
        meaning = p.meaning.or(q.meaning);
        text = "or(" + p.text + ", " + q.text + ")";
      }
      case "ReifiedOr" -> {
        make = x -> new Reified(new Or(p.make.apply(x), q.make.apply(x)), (IntVar) x[b]);
        meaning = t -> (p.meaning.test(t) || q.meaning.test(t)) == (t.i(b) == 1);
        text = "reif(or(" + p.text + ", " + q.text + "), v" + b + ")";
      }
      case "IfThen" -> {
        make = x -> new IfThen(p.make.apply(x), q.make.apply(x));
        meaning = p.meaning.negate().or(q.meaning);
        text = "ifthen(" + p.text + ", " + q.text + ")";
      }
      case "IfThenElse" -> {
        make = x -> new IfThenElse(p.make.apply(x), q.make.apply(x), s.make.apply(x));
        meaning = t -> p.meaning.test(t) ? q.meaning.test(t) : s.meaning.test(t);
        text = "ifthenelse(" + p.text + ", " + q.text + ", " + s.text + ")";
      }
      case "Implies" -> {
        make = x -> new Implies((IntVar) x[b], p.make.apply(x));
        meaning = t -> t.i(b) == 0 || p.meaning.test(t);
        text = "implies(v" + b + ", " + p.text + ")";
      }
      case "Xor" -> {
        make = x -> new Xor(p.make.apply(x), (IntVar) x[b]);
        meaning = t -> p.meaning.test(t) != (t.i(b) == 1);
        text = "xor(" + p.text + ", v" + b + ")";
      }
      default -> {
        make = x -> new Eq(p.make.apply(x), q.make.apply(x));
        meaning = t -> p.meaning.test(t) == q.meaning.test(t);
        text = "eq(" + p.text + ", " + q.text + ")";
      }
    }
    return new Case(
        vars,
        (store, x) -> {
          Constraint c = make.apply(x);
          store.impose(c);
          return c;
        },
        meaning,
        text);
  }

  private static Relation relation(Random r) {
    int a = r.nextInt(SETS);
    int b = r.nextInt(SETS);
    int x = SETS + r.nextInt(INTS);
    boolean strict = r.nextBoolean();
    int[] constant = values(r, 1, 4, r.nextInt(4));
    IntDomain d = domain(constant);
    Set<Integer> cs = toSet(constant);
    int e = 1 + r.nextInt(4);
    String st = strict ? "<" : "";
    return switch (r.nextInt(10)) {
      case 0 ->
          new Relation(
              v -> new AinB((SetVar) v[a], (SetVar) v[b], strict),
              t -> subset(t.s(a), t.s(b), strict),
              "v" + a + " in" + st + " v" + b);
      case 1 ->
          new Relation(
              v -> new AeqB((SetVar) v[a], (SetVar) v[b]),
              t -> t.s(a).equals(t.s(b)),
              "v" + a + " = v" + b);
      case 2 ->
          new Relation(
              v -> new AleB((SetVar) v[a], (SetVar) v[b]),
              t -> lex(t.elements(a), t.elements(b)) <= 0,
              "v" + a + " lex<= v" + b);
      case 3 ->
          new Relation(
              v -> new AltB((SetVar) v[a], (SetVar) v[b]),
              t -> lex(t.elements(a), t.elements(b)) < 0,
              "v" + a + " lex< v" + b);
      case 4 ->
          new Relation(
              v -> new EinA(e, (SetVar) v[a], strict),
              t -> subset(Set.of(e), t.s(a), strict),
              e + " in" + st + " v" + a);
      case 5 ->
          new Relation(
              v -> new XinA((IntVar) v[x], (SetVar) v[a], strict),
              t -> subset(Set.of(t.i(x)), t.s(a), strict),
              "v" + x + " in" + st + " v" + a);
      case 6 ->
          new Relation(
              v -> new XeqA((IntVar) v[x], (SetVar) v[a]),
              t -> t.s(a).equals(Set.of(t.i(x))),
              "{v" + x + "} = v" + a);
      case 7 ->
          new Relation(
              v -> new AinS((SetVar) v[a], d, strict),
              t -> subset(t.s(a), cs, strict),
              "v" + a + " in" + st + " " + cs);
      case 8 ->
          new Relation(
              v -> new SinA(d, (SetVar) v[a], strict),
              t -> subset(cs, t.s(a), strict),
              cs + " in" + st + " v" + a);
      default ->
          new Relation(
              v -> new AeqS((SetVar) v[a], d), t -> t.s(a).equals(cs), "v" + a + " = " + cs);
    };
  }

  // ---------------------------------------------------------------------------------------------
  // brute force

  /** The tuples of the current domains, as indices into the values of each specification. */
  private static List<int[]> box(Case c, Var[] x) {
    List<List<Integer>> allowed = new ArrayList<>();
    long size = 1;
    for (int i = 0; i < x.length; i++) {
      List<int[]> values = c.vars()[i].values();
      List<Integer> keep = new ArrayList<>();
      for (int k = 0; k < values.size(); k++) {
        if (inDomain(x[i], values.get(k))) {
          keep.add(k);
        }
      }
      allowed.add(keep);
      size *= Math.max(1, keep.size());
    }
    List<int[]> tuples = new ArrayList<>();
    if (size > MAX_BOX || allowed.stream().anyMatch(List::isEmpty)) {
      return tuples;
    }
    enumerate(allowed, 0, new int[x.length], tuples);
    return tuples;
  }

  private static void enumerate(List<List<Integer>> allowed, int i, int[] t, List<int[]> out) {
    if (i == t.length) {
      out.add(t.clone());
      return;
    }
    for (int k : allowed.get(i)) {
      t[i] = k;
      enumerate(allowed, i + 1, t, out);
    }
  }

  private static boolean inDomain(Var v, int[] value) {
    if (v instanceof IntVar x) {
      return x.dom().contains(value[0]);
    }
    SetDomain d = ((SetVar) v).dom();
    for (int e : elements(d.glb())) {
      if (Arrays.binarySearch(value, e) < 0) {
        return false;
      }
    }
    for (int e : value) {
      if (!d.lub().contains(e)) {
        return false;
      }
    }
    return d.card().contains(value.length);
  }

  private static boolean holds(Case c, int[] t) {
    int[][] a = new int[t.length][];
    for (int i = 0; i < t.length; i++) {
      a[i] = c.vars()[i].values().get(t[i]);
    }
    return c.semantics().test(new Assignment(a));
  }

  private static Var create(Store store, String name, Spec spec) {
    if (!spec.isSet()) {
      return new IntVar(store, name, domain(spec.ints()));
    }
    return new SetVar(store, name, new BoundSetDomain(domain(spec.glb()), domain(spec.lub())));
  }

  private static IntDomain domain(int[] values) {
    IntervalDomain d = new IntervalDomain();
    for (int v : values) {
      d.unionAdapt(v, v);
    }
    return d;
  }

  private static int[] elements(IntDomain d) {
    List<Integer> l = new ArrayList<>();
    for (var e = d.valueEnumeration(); e.hasMoreElements(); ) {
      l.add(e.nextElement());
    }
    return l.stream().mapToInt(Integer::intValue).toArray();
  }

  private static int[] values(Random random, int min, int max, int count) {
    java.util.TreeSet<Integer> s = new java.util.TreeSet<>();
    for (int i = 0; i < count; i++) {
      s.add(min + random.nextInt(max - min + 1));
    }
    return s.stream().mapToInt(Integer::intValue).toArray();
  }

  private static Set<Integer> toSet(int[] values) {
    Set<Integer> s = new java.util.TreeSet<>();
    for (int v : values) {
      s.add(v);
    }
    return s;
  }

  private static boolean subset(Set<Integer> a, Set<Integer> b, boolean strict) {
    return b.containsAll(a) && (!strict || !a.equals(b));
  }

  private static int lex(int[] a, int[] b) {
    for (int i = 0; i < Math.min(a.length, b.length); i++) {
      if (a[i] != b[i]) {
        return Integer.compare(a[i], b[i]);
      }
    }
    return Integer.compare(a.length, b.length);
  }

  private static String show(Var[] x) {
    return Arrays.toString(x);
  }
}
