/*
 * Xcsp2jacop.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
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
 * preservation of specified reasonable legal notices and author attributions
 * in material modified versions of this work.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.fz.xcsp;

import java.io.BufferedInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import org.jacop.fz.Fz2jacop;

/**
 * Solves an XCSP3 instance with JaCoP and prints the answer in the format of the XCSP3 competition.
 * The instance is read by {@link XcspReader}, written as FlatZinc and solved by JaCoP's FlatZinc
 * front end with the given options.
 *
 * <p>Usage: {@code java -cp jacop.jar org.jacop.fz.xcsp.Xcsp2jacop [FlatZinc options]
 * instance.xml}. {@code --fzn FILE} keeps the FlatZinc model in FILE; {@code --fzn-only} stops
 * after writing it. An optimisation problem runs with {@code -a}, so that each better solution
 * prints an {@code o} line.
 */
public final class Xcsp2jacop {

  private Xcsp2jacop() {}

  /**
   * Runs the solver.
   *
   * @param args the FlatZinc options, then the XCSP3 file
   */
  public static void main(String[] args) {
    watchdog = true;
    System.exit(run(args));
  }

  // a run from the command line answers by its time limit, whatever the solver is doing then
  private static boolean watchdog;

  // the output filter, once solving starts; the watchdog prints its last solution
  private static volatile XcspOutput current;

  /** Margin after the time limit (-t, from the start of the run) before the watchdog answers. */
  private static final long WATCHDOG_MARGIN_MS =
      Long.getLong("org.jacop.fz.xcsp.watchdogMargin", 1000);

  private static Thread startWatchdog(PrintStream stdout, long deadlineNanos) {
    Thread w =
        new Thread(
            () -> {
              try {
                long wait;
                while ((wait = (deadlineNanos - System.nanoTime()) / 1_000_000) > 0) {
                  Thread.sleep(wait);
                }
              } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
                return;
              }
              XcspOutput f = current;
              if (f != null) {
                f.finish();
              } else {
                stdout.println("c time limit reached before solving started");
                stdout.println("s UNKNOWN");
              }
              stdout.flush();
              Runtime.getRuntime().halt(0);
            },
            "xcsp-watchdog");
    w.setDaemon(true);
    w.start();
    return w;
  }

  // the value of -t in milliseconds, 0 without one
  private static long timeLimit(List<String> fzArgs) {
    int i = fzArgs.indexOf("-t");
    if (i < 0 || i + 1 >= fzArgs.size()) {
      return 0;
    }
    try {
      return Long.parseLong(fzArgs.get(i + 1));
    } catch (NumberFormatException e) {
      return 0;
    }
  }

  /**
   * Runs the solver without exiting the JVM.
   *
   * @param args the FlatZinc options, then the XCSP3 file
   * @return the exit status
   */
  @SuppressWarnings("java:S106") // stdout is the interface of a competition solver
  public static int run(String[] args) {
    PrintStream stdout = System.out;
    if (args.length == 0) {
      stdout.println("c usage: Xcsp2jacop [FlatZinc options] instance.xml");
      return 1;
    }
    long t0 = System.nanoTime();
    String file = args[args.length - 1];
    List<String> fzArgs = new ArrayList<>();
    Path keep = null;
    boolean only = false;
    for (int i = 0; i < args.length - 1; i++) {
      switch (args[i]) {
        case "--fzn" -> keep = Path.of(args[++i]);
        case "--fzn-only" -> only = true;
        default -> fzArgs.add(args[i]);
      }
    }
    long limit = timeLimit(fzArgs);
    Thread dog =
        watchdog && limit > 0
            ? startWatchdog(stdout, t0 + (limit + WATCHDOG_MARGIN_MS) * 1_000_000)
            : null;
    try {
      return run(stdout, t0, file, fzArgs, keep, only, limit);
    } finally {
      if (dog != null) {
        dog.interrupt();
      }
    }
  }

  private static int run(
      PrintStream stdout,
      long t0,
      String file,
      List<String> fzArgs,
      Path keep,
      boolean only,
      long limit) {
    Path fzn;
    XcspReader reader;
    try {
      Path dir =
          keep != null && keep.toAbsolutePath().getParent() != null
              ? keep.toAbsolutePath().getParent()
              : Path.of(System.getProperty("java.io.tmpdir"));
      reader = new XcspReader(dir);
      try (InputStream in = open(file)) {
        reader.read(in);
      }
      fzn = keep != null ? keep : Files.createTempFile(dir, "xcsp", ".fzn");
      Outputs outputs = outputs(reader);
      String solve = "solve satisfy;";
      if (reader.objective != null) {
        reader.m.outputVars.add(reader.objective);
        solve =
            "solve " + (reader.minimize ? "minimize " : "maximize ") + reader.objective.name + ";";
      }
      reader.m.write(fzn, outputs.decls, solve);
      stdout.println(
          "c XCSP3 read in "
              + (System.nanoTime() - t0) / 1_000_000
              + " ms: "
              + reader.m.vars.size()
              + " FlatZinc variables, "
              + reader.m.constraintCount()
              + " constraints");
      stdout.flush();
      if (only) {
        return 0;
      }
      XcspOutput filter =
          new XcspOutput(
              stdout,
              reader.objective != null,
              outputs.ids,
              outputs.slots,
              outputs.symbols,
              reader.objective != null ? reader.objective.name : null);
      filter.clipped = reader.m.clipped;
      if (reader.m.clipped) {
        stdout.println(
            "c domains cut to JaCoP's integer range: no UNSATISFIABLE or OPTIMUM claims");
      }
      PrintStream filtered = new PrintStream(filter, true, java.nio.charset.StandardCharsets.UTF_8);
      Thread hook = new Thread(filter::finish);
      Runtime.getRuntime().addShutdownHook(hook);
      System.setOut(filtered);
      current = filter;
      if (reader.objective != null && !fzArgs.contains("-a")) {
        fzArgs.add(0, "-a");
      }
      if (limit > 0) {
        // the time limit runs from the start, reading included
        int i = fzArgs.indexOf("-t");
        long left = limit - (System.nanoTime() - t0) / 1_000_000;
        fzArgs.set(i + 1, Long.toString(Math.max(1, left)));
      }
      fzArgs.add(fzn.toAbsolutePath().toString());
      int status;
      try {
        status = new Fz2jacop().callMain(fzArgs.toArray(new String[0]));
      } finally {
        filtered.flush();
        System.setOut(stdout);
        filter.finish();
        current = null;
        Runtime.getRuntime().removeShutdownHook(hook);
        if (keep == null) {
          Files.deleteIfExists(fzn);
        }
      }
      return status;
    } catch (XcspException e) {
      stdout.println("c " + e.getMessage());
      stdout.println("s UNSUPPORTED");
      return 1;
    } catch (IOException e) {
      stdout.println("c " + e);
      stdout.println("s UNKNOWN");
      return 1;
    } catch (OutOfMemoryError e) {
      stdout.println("c out of memory while reading the instance");
      stdout.println("s UNKNOWN");
      return 1;
    }
  }

  // the xz program: the property org.jacop.fz.xcsp.xz, else the first of the fixed system paths
  private static String xz() throws IOException {
    String given = System.getProperty("org.jacop.fz.xcsp.xz");
    if (given != null) {
      return given;
    }
    for (String p :
        new String[] {"/usr/bin/xz", "/bin/xz", "/usr/local/bin/xz", "/opt/homebrew/bin/xz"}) {
      if (Files.isExecutable(Path.of(p))) {
        return p;
      }
    }
    throw new IOException(
        "xz not found in /usr/bin, /bin, /usr/local/bin or /opt/homebrew/bin; set -Dorg.jacop.fz.xcsp.xz");
  }

  // the instance, uncompressed by xz when its name ends with .lzma or .xz
  private static InputStream open(String file) throws IOException {
    if (file.endsWith(".lzma") || file.endsWith(".xz")) {
      Process p =
          new ProcessBuilder(xz(), "-dc", file)
              .redirectError(ProcessBuilder.Redirect.INHERIT)
              .start();
      return new BufferedInputStream(p.getInputStream(), 1 << 16);
    }
    return new BufferedInputStream(Files.newInputStream(Path.of(file)), 1 << 16);
  }

  private record Outputs(
      List<String> decls,
      List<String> ids,
      List<XcspOutput.Slot> slots,
      Map<Integer, String[]> symbols) {}

  // output annotations: an array per XCSP3 array of one kind, a variable otherwise
  private static Outputs outputs(XcspReader r) {
    List<String> decls = new ArrayList<>();
    List<String> ids = new ArrayList<>();
    List<XcspOutput.Slot> slots = new ArrayList<>();
    Map<Integer, String[]> symbols = new HashMap<>();
    String[] symbolTable = r.symbolTable();
    int arrays = 0;
    for (XcspReader.Declared d : r.declared) {
      if (d.array() == null) {
        if (r.symbolic.containsKey(d.var())) {
          symbols.put(ids.size(), symbolTable);
        }
        ids.add(d.id());
        slots.add(new XcspOutput.Slot(d.var().name, 0));
        r.m.outputVars.add(d.var());
        continue;
      }
      XcspReader.ArrayOfVars a = d.array();
      List<FznVar> cells = new ArrayList<>();
      List<String> cellIds = new ArrayList<>();
      for (int i = 0; i < a.cells.length; i++) {
        if (a.cells[i] != null) {
          cells.add(a.cells[i]);
          cellIds.add(a.cellId(i));
        }
      }
      if (cells.isEmpty()) {
        continue;
      }
      boolean allBool = cells.stream().allMatch(x -> x.bool);
      boolean noBool = cells.stream().noneMatch(x -> x.bool);
      if (allBool || noBool) {
        String name = "XCSP_ARRAY_" + arrays++ + "_";
        StringBuilder s = new StringBuilder("array [1..");
        s.append(cells.size())
            .append("] of var ")
            .append(allBool ? "bool" : "int")
            .append(": ")
            .append(name);
        s.append(":: output_array([1..").append(cells.size()).append("]) = [");
        for (int i = 0; i < cells.size(); i++) {
          if (i > 0) {
            s.append(',');
          }
          s.append(cells.get(i).name);
        }
        decls.add(s.append("];").toString());
        for (int i = 0; i < cells.size(); i++) {
          if (r.symbolic.containsKey(cells.get(i))) {
            symbols.put(ids.size(), symbolTable);
          }
          ids.add(cellIds.get(i));
          slots.add(new XcspOutput.Slot(name, i));
        }
      } else {
        for (int i = 0; i < cells.size(); i++) {
          ids.add(cellIds.get(i));
          slots.add(new XcspOutput.Slot(cells.get(i).name, 0));
          r.m.outputVars.add(cells.get(i));
        }
      }
    }
    return new Outputs(decls, ids, slots, symbols);
  }

  static String[] copy(String[] a) {
    return Arrays.copyOf(a, a.length);
  }
}
