package org.jacop.core;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.jacop.constraints.Constraint;

/**
 * Study-only profiler (not for merging): consistency calls, time, prunings, failures and
 * explanation work per constraint class and size bucket. On with -Djacop.cprof=FILE; the table is
 * written at exit.
 */
public final class ConstraintProfile {

  public static final String FILE = System.getProperty("jacop.cprof");
  public static final boolean ON = FILE != null;

  /** One bucket. */
  public static final class Stat {
    final String key;
    long constraints;
    long calls;
    long ns;
    long pruning;
    long fails;
    long explains;
    long explainNs;
    long explainLits;
    long failExplains;
    long arity;
    long dom;

    Stat(String key) {
      this.key = key;
    }
  }

  private static final Map<String, Stat> STATS = new HashMap<>();
  private static final long START = System.nanoTime();
  public static long satNs;
  public static long satProps;
  public static long conflicts;

  static {
    if (ON) {
      Runtime.getRuntime().addShutdownHook(new Thread(ConstraintProfile::write));
    }
  }

  private ConstraintProfile() {}

  private static int bucket(long n) {
    if (n <= 2) return (int) n;
    if (n <= 3) return 3;
    if (n <= 4) return 4;
    if (n <= 8) return 8;
    if (n <= 16) return 16;
    if (n <= 32) return 32;
    if (n <= 64) return 64;
    if (n <= 256) return 256;
    if (n <= 1024) return 1024;
    return 99999;
  }

  /** The bucket of a constraint, made at its first call. */
  public static synchronized Stat of(Constraint c) {
    if (c.profileSlot instanceof Stat s) {
      return s;
    }
    int arity = 0;
    long dom = 0;
    long domSum = 0;
    for (Var v : c.arguments()) {
      if (v instanceof IntVar x && !x.singleton()) {
        arity++;
        dom = Math.max(dom, x.getSize());
        domSum += x.getSize();
      }
    }
    String key = c.getClass().getSimpleName() + "\t" + bucket(arity) + "\t" + bucket(dom);
    Stat s = STATS.computeIfAbsent(key, Stat::new);
    s.constraints++;
    s.arity += arity;
    s.dom += domSum;
    c.profileSlot = s;
    return s;
  }

  public static void call(Constraint c, long ns, boolean pruned, boolean failed) {
    Stat s = of(c);
    s.calls++;
    s.ns += ns;
    if (pruned) s.pruning++;
    if (failed) s.fails++;
  }

  public static void explain(Constraint c, long ns, int lits, boolean failure) {
    if (c == null) return;
    Stat s = of(c);
    s.explains++;
    s.explainNs += ns;
    s.explainLits += lits;
    if (failure) s.failExplains++;
  }

  static synchronized void write() {
    List<Stat> all = new ArrayList<>(STATS.values());
    all.sort((a, b) -> Long.compare(b.ns + b.explainNs, a.ns + a.explainNs));
    try (PrintWriter w = new PrintWriter(new FileWriter(FILE))) {
      w.println(
          "#total_ns\t"
              + (System.nanoTime() - START)
              + "\tsat_ns\t"
              + satNs
              + "\tsat_props\t"
              + satProps
              + "\tconflicts\t"
              + conflicts);
      w.println(
          "class\tarity\tdom\tconstraints\tcalls\tns\tpruning\tfails\texplains\texplainNs\texplainLits\tfailExplains\taritySum\tdomSum");
      for (Stat s : all) {
        w.println(
            s.key
                + "\t"
                + s.constraints
                + "\t"
                + s.calls
                + "\t"
                + s.ns
                + "\t"
                + s.pruning
                + "\t"
                + s.fails
                + "\t"
                + s.explains
                + "\t"
                + s.explainNs
                + "\t"
                + s.explainLits
                + "\t"
                + s.failExplains
                + "\t"
                + s.arity
                + "\t"
                + s.dom);
      }
    } catch (IOException e) {
      // study tool
    }
  }
}
