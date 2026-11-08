/*
 * FlowTrace.java
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
 * in material form as in https://www.gnu.org/licenses/agpl-3.0.en.html#section7.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.cdcl;

import java.io.BufferedWriter;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.zip.GZIPOutputStream;

/**
 * Experimental, statistics only: a trace of the search under lazy clause generation for offline
 * study of how propagation flows between integer variables. Enabled by the system property {@code
 * jacop.flowtrace} (a file name, gzipped). Lines:
 *
 * <ul>
 *   <li>{@code V n}: number of integer variables;
 *   <li>{@code C class v1 v2 ...}: a constraint and the integer variables of its scope;
 *   <li>{@code K level}: a conflict at a decision level; then {@code E a b a b ...}: reason edges,
 *       a variable in the reason of a literal of variable b (b = -1 for the conflicting clause);
 *       then {@code L v1 v2 ...}: integer variables of the learnt clause;
 *   <li>{@code D v level}: an activity decision;
 *   <li>{@code R}: a restart.
 * </ul>
 *
 * <p>Variables are integer variable indices of the LCG solver. Atoms without an integer variable
 * are left out. Only the first {@code jacop.flowtrace.conflicts} conflicts (default 200,000) are
 * written.
 */
public final class FlowTrace {

  private static final String FILE = System.getProperty("jacop.flowtrace");
  private static final long MAX_CONFLICTS = Long.getLong("jacop.flowtrace.conflicts", 200_000L);
  private static FlowTrace instance;

  private final BufferedWriter out;
  private long conflicts;
  private boolean open = true;
  private int[] edges = new int[64];
  private int numEdges;
  // de-duplication of edges within a conflict
  private long[] seen = new long[256];
  private int numSeen;
  private final StringBuilder line = new StringBuilder(256);

  private FlowTrace(String file) throws IOException {
    out =
        new BufferedWriter(
            new OutputStreamWriter(
                new GZIPOutputStream(new FileOutputStream(file), 1 << 16),
                StandardCharsets.US_ASCII),
            1 << 16);
    Runtime.getRuntime().addShutdownHook(new Thread(this::close));
  }

  /** The trace, or null when tracing is off; created by the first call. */
  public static synchronized FlowTrace get() {
    if (FILE == null) {
      return null;
    }
    if (instance == null) {
      try {
        instance = new FlowTrace(FILE);
      } catch (IOException e) {
        throw new UncheckedIOException(e);
      }
    }
    return instance;
  }

  /** Whether lines are still written. */
  public boolean active() {
    return open && conflicts < MAX_CONFLICTS;
  }

  /** Writes a free-form line. */
  public synchronized void write(String s) {
    if (!open) {
      return;
    }
    try {
      out.write(s);
      out.write('\n');
    } catch (IOException e) {
      open = false;
    }
  }

  /** Starts a conflict. */
  public void conflict(int level) {
    numEdges = 0;
    numSeen = 0;
    if (active()) {
      write("K " + level);
    }
  }

  /** A reason edge from variable a to variable b (b = -1: the conflicting clause). */
  public void edge(int a, int b) {
    if (a < 0 || a == b || !active()) {
      return;
    }
    long key = ((long) a << 32) | (b & 0xffffffffL);
    for (int i = 0; i < numSeen; i++) {
      if (seen[i] == key) {
        return;
      }
    }
    if (numSeen == seen.length) {
      if (seen.length >= 4096) {
        return; // keep a conflict's line bounded
      }
      seen = Arrays.copyOf(seen, 2 * seen.length);
    }
    seen[numSeen++] = key;
    if (numEdges + 2 > edges.length) {
      edges = Arrays.copyOf(edges, 2 * edges.length);
    }
    edges[numEdges++] = a;
    edges[numEdges++] = b;
  }

  /** Ends a conflict with the integer variables of its learnt clause. */
  public void learnt(int[] vars, int n) {
    if (!active()) {
      return;
    }
    line.setLength(0);
    line.append('E');
    for (int i = 0; i < numEdges; i++) {
      line.append(' ').append(edges[i]);
    }
    write(line.toString());
    line.setLength(0);
    line.append('L');
    for (int i = 0; i < n; i++) {
      line.append(' ').append(vars[i]);
    }
    write(line.toString());
    conflicts++;
  }

  /** An activity decision on variable v. */
  public void decision(int v, int level) {
    if (active()) {
      write("D " + v + " " + level);
    }
  }

  /** A restart. */
  public void restart() {
    if (active()) {
      write("R");
    }
  }

  private final java.util.List<Runnable> closers = new java.util.ArrayList<>();

  /** Registers an action that writes its last lines when the trace closes. */
  public synchronized void onClose(Runnable r) {
    closers.add(r);
  }

  /** Flushes and closes the file. */
  public synchronized void close() {
    if (!open) {
      return;
    }
    for (Runnable r : closers) {
      try {
        r.run();
      } catch (RuntimeException e) {
        // statistics only
      }
    }
    open = false;
    try {
      out.close();
    } catch (IOException e) {
      // nothing to do at exit
    }
  }
}
