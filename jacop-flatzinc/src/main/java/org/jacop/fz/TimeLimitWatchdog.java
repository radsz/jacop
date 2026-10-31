/*
 * TimeLimitWatchdog.java
 * <p>
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

package org.jacop.fz;

import java.io.ByteArrayOutputStream;
import java.io.FilterOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import lombok.extern.slf4j.Slf4j;

/**
 * Ends a command-line run that is still going a grace period after its time-out ({@code -t}). The
 * searches stop at the time-out, but reading a large model, posting its constraints (a propagation
 * that creeps along a chain of bounds), presolve and the setup of lazy clause generation do not all
 * check it. When the watchdog fires and no final status was printed, it prints the best solution
 * kept back (without {@code -a}), or {@code =====UNKNOWN=====} when there is none, then the
 * statistics with {@code -s}, and halts the JVM.
 *
 * <p>It replaces {@code System.out} by a stream that records whether a solution or a status line
 * was printed, and it prints under that stream's lock, so its lines never interleave with the
 * solver's.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
final class TimeLimitWatchdog {

  /** Milliseconds after the time-out before the watchdog fires (property jacop.fz.timeOutGrace). */
  static final long GRACE = Long.getLong("jacop.fz.timeOutGrace", 1000L);

  private final TrackingStream out;
  private final PrintStream original;
  private final Thread thread;
  private final Runnable halt;
  private volatile boolean cancelled;

  /**
   * Writes what the watchdog prints when it fires: the kept solution or the unknown status, and the
   * statistics.
   */
  interface Report {
    /**
     * Prints the solution kept back without {@code -a}, if any.
     *
     * @return true when a solution was printed, now or before
     */
    boolean printKeptSolution();

    /** Prints the statistics, when they were asked for. */
    void printStatistics();
  }

  private TimeLimitWatchdog(long delayMillis, Report report, Runnable halt) {
    this.original = System.out;
    this.out = new TrackingStream(original);
    this.halt = halt;
    System.setOut(out);
    thread =
        Thread.ofPlatform()
            .daemon()
            .name("jacop-time-limit")
            .unstarted(() -> run(delayMillis, report));
  }

  /**
   * Starts a watchdog that fires {@link #GRACE} after the remaining time-out.
   *
   * @param remainingMillis the time left before the time-out
   * @param report what to print when it fires
   * @param halt how to end the run (halts the JVM on the command line)
   * @return the watchdog, to cancel when the run ends
   */
  static TimeLimitWatchdog start(long remainingMillis, Report report, Runnable halt) {
    TimeLimitWatchdog w = new TimeLimitWatchdog(remainingMillis + GRACE, report, halt);
    w.thread.start();
    return w;
  }

  /** Stops the watchdog and gives {@code System.out} back. */
  void cancel() {
    synchronized (out) {
      cancelled = true;
      out.flush();
      if (System.out == out) {
        System.setOut(original);
      }
    }
    thread.interrupt();
  }

  /**
   * Whether a solution line ({@code ----------}) was printed.
   *
   * @return true after a solution
   */
  boolean solutionPrinted() {
    return out.solution;
  }

  /**
   * Whether a final status line ({@code =====...}) was printed.
   *
   * @return true after a status
   */
  boolean statusPrinted() {
    return out.status;
  }

  private void run(long delayMillis, Report report) {
    try {
      Thread.sleep(delayMillis);
    } catch (InterruptedException _) {
      // cancelled: the run ended on its own
      Thread.currentThread().interrupt();
      return;
    }
    synchronized (out) {
      if (cancelled || out.status) {
        // the run ends on its own: its status is out, only its statistics may follow
        return;
      }
      boolean solved;
      try {
        // a solution out already is the kept one, printed as the run ended
        solved = out.solution || report.printKeptSolution();
      } catch (RuntimeException e) {
        log.debug("kept solution not printed", e);
        solved = out.solution;
      }
      if (!solved) {
        out.println("=====UNKNOWN=====");
      }
      out.println("%% =====TIME-OUT=====");
      out.flush();
      // the statistics of a search print its status too, which is already out
      LineWatch watch = (LineWatch) out.target();
      watch.dropStatus = true;
      try {
        report.printStatistics();
      } catch (RuntimeException e) {
        // the model was not read yet: no statistics to print
        log.debug("statistics not printed", e);
      }
      out.flush();
      watch.dropStatus = false;
      try {
        watch.flushLine();
      } catch (IOException e) {
        log.debug("statistics not printed", e);
      }
      halt.run();
    }
  }

  /** A stream that records whether a solution or a status line went through it. */
  private static final class TrackingStream extends PrintStream {

    volatile boolean solution;
    volatile boolean status;

    TrackingStream(PrintStream target) {
      super(new LineWatch(target), true);
      ((LineWatch) this.out).owner = this;
    }

    OutputStream target() {
      return out;
    }
  }

  /**
   * Looks at the run of {@code -} or {@code =} that starts each line written. While {@link
   * #dropStatus} is set, it holds each line back and drops the solution and status lines.
   */
  private static final class LineWatch extends FilterOutputStream {

    TrackingStream owner;
    boolean dropStatus;
    private final ByteArrayOutputStream line = new ByteArrayOutputStream();
    private boolean lineStart = true;
    private boolean inRun;
    private int lead;
    private int run;

    LineWatch(OutputStream target) {
      super(target);
    }

    @Override
    public void write(int b) throws IOException {
      if (dropStatus) {
        line.write(b);
        if (b == '\n') {
          flushLine();
        }
        return;
      }
      out.write(b);
      see(b);
    }

    @Override
    public void write(byte[] b, int off, int len) throws IOException {
      if (dropStatus) {
        for (int i = off; i < off + len; i++) {
          write(b[i]);
        }
        return;
      }
      out.write(b, off, len);
      for (int i = off; i < off + len; i++) {
        see(b[i]);
      }
    }

    // writes the line held back, unless it is a solution or status line
    void flushLine() throws IOException {
      String held = line.toString(StandardCharsets.UTF_8);
      line.reset();
      String text = held.strip();
      if (!text.startsWith("=====")
          && !text.startsWith("----------")
          && !text.startsWith("%% =====")) {
        out.write(held.getBytes(StandardCharsets.UTF_8));
      }
    }

    private void see(int b) {
      if (b == '\n') {
        endRun();
        lineStart = true;
        return;
      }
      if (lineStart) {
        lineStart = false;
        inRun = b == '-' || b == '=';
        lead = b;
        run = 1;
      } else if (inRun && b == lead) {
        run++;
      } else {
        endRun();
      }
    }

    // a solution ends with a line of ten '-', a final status starts with five '='
    private void endRun() {
      if (inRun) {
        if (lead == '-' && run >= 10) {
          owner.solution = true;
        } else if (lead == '=' && run >= 5) {
          owner.status = true;
        }
      }
      inRun = false;
    }
  }
}
