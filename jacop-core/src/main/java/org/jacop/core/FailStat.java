package org.jacop.core;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;
import java.util.TreeMap;
import org.jacop.constraints.Constraint;

/**
 * Measurement prototype (not for merging): work spent in propagation windows that end in a failure,
 * before the failing constraint got its turn. A window is one outer store.consistency() call in
 * plain CP search, or one CdclSolver.propagateAll() call under LCG (opened by {@link
 * #lcgWindowStart}).
 *
 * <p>System properties: jacop.failstat=FILE (append one JSON line at exit), jacop.failstat.tag,
 * jacop.failstat.record=FILE (window index and serial of the failing constraint, binary),
 * jacop.failstat.oracle=FILE (replay: the recorded failing constraint runs first in its window),
 * jacop.prop.front=K (the K most recently failed distinct constraints go to a front queue).
 */
public final class FailStat {

  private FailStat() {}

  public static final String FILE = System.getProperty("jacop.failstat");
  public static final String RECORD = System.getProperty("jacop.failstat.record");
  public static final String ORACLE = System.getProperty("jacop.failstat.oracle");
  public static final int FRONT = Integer.getInteger("jacop.prop.front", 0);

  /** front policy variant: 0 = hot constraint goes to front queue; 1 = front of its own class. */
  public static final int FRONT_MODE = Integer.getInteger("jacop.prop.frontMode", 0);

  /** Measurement on (timers per propagator call). */
  public static final boolean ON = FILE != null || RECORD != null;

  /** Stop (exit) when this many windows have started; time and fingerprint go to TIME_FILE. */
  public static final long MAXW = Long.getLong("jacop.failstat.maxWindows", -1);

  public static final String TIME_FILE = System.getProperty("jacop.failstat.time");

  /** Any part of this prototype is on. */
  public static final boolean ANY =
      ON || ORACLE != null || FRONT > 0 || MAXW > 0 || TIME_FILE != null;

  static long t0;
  static long fails;
  static long fingerprint = 17;

  // ------------------------------------------------------------------ window state
  static boolean lcgOpen;
  static long windowIndex = -1;
  static long winStartWall;
  static long winStartCalls;
  static long winStartProp;
  static boolean winFailed;

  /** cumulative over the run */
  static long cumCalls;

  static long cumProp;

  // ------------------------------------------------------------------ aggregates
  static long windows;
  static long failWindows;
  static long failByConstraint;
  static long failByClause; // LCG window failed with no constraint failure
  static long wallAll;
  static long wallFail;
  static long propAll;
  static long propFail;
  static long callsAll;
  static long callsFail;
  // per constraint failure
  static long callsBefore;
  static long propBefore;
  static long failCallNanos;
  static long queuedAtStart; // failing constraint queued before the window's first call
  static long ranBefore; // ran earlier in the window without failing
  static long waitProp; // propagation time between its enqueue (in window) and its call
  static long waitPropAtStart; // same, only those queued at start
  static long sameAsLast;
  static long inLast8;
  static long inLast32;
  static long firstCall; // the failing call was the first call of the window
  static long[] queueFails = new long[8];
  static long[] queueBefore = new long[8];

  static final Map<String, long[]> byClass = new HashMap<>();

  // LRU of recently failed constraints
  static final Constraint[] lru = new Constraint[64];
  static int lruSize;

  // oracle/record
  static int[] rec = new int[1 << 16];
  static int recSize;
  static int[] oracle;
  static int oraclePos;
  static long oracleHits;
  static long oracleFailFirst;
  static long oracleRuns;
  static long frontRuns;
  static long frontFails;

  /** hot constraints, front policy */
  static final Constraint[] hot = new Constraint[256];

  static int hotSize;

  static {
    if (ON || TIME_FILE != null) {
      Runtime.getRuntime()
          .addShutdownHook(
              new Thread(
                  () -> {
                    if (TIME_FILE != null) {
                      writeTime(false);
                    } else {
                      dump();
                    }
                  }));
    }
    if (ORACLE != null) {
      try (DataInputStream in =
          new DataInputStream(new BufferedInputStream(new FileInputStream(ORACLE)))) {
        int n = in.readInt();
        oracle = new int[n];
        for (int i = 0; i < n; i++) {
          oracle[i] = in.readInt();
        }
      } catch (IOException e) {
        throw new IllegalStateException(e);
      }
    }
  }

  static final java.util.ArrayList<Constraint> registry = new java.util.ArrayList<>();
  static int serialCounter;

  /** Gives a constraint its creation serial (kept only for the oracle replay). */
  public static int register(Constraint c) {
    if (ORACLE != null) {
      registry.add(c);
    }
    return serialCounter++;
  }

  static Constraint bySerial(int s) {
    return s >= 0 && s < registry.size() ? registry.get(s) : null;
  }

  // ------------------------------------------------------------------ hooks

  /** LCG: a propagateAll window starts. */
  public static void lcgWindowStart() {
    lcgOpen = true;
    open();
  }

  /** LCG: the window ends, with or without a conflict. */
  public static void lcgWindowEnd(boolean conflict) {
    close(conflict);
    lcgOpen = false;
  }

  static void open() {
    windowIndex++;
    if (windowIndex == 0) {
      t0 = System.nanoTime();
    } else if (windowIndex == MAXW) {
      writeTime(true);
      Runtime.getRuntime().halt(0);
    }
    winStartCalls = cumCalls;
    winStartProp = cumProp;
    winFailed = false;
    if (ON) {
      winStartWall = System.nanoTime();
    }
  }

  static void close(boolean failed) {
    if (!ON) {
      return;
    }
    long wall = System.nanoTime() - winStartWall;
    long prop = cumProp - winStartProp;
    long calls = cumCalls - winStartCalls;
    windows++;
    wallAll += wall;
    propAll += prop;
    callsAll += calls;
    if (failed) {
      failWindows++;
      wallFail += wall;
      propFail += prop;
      callsFail += calls;
      if (!winFailed) {
        failByClause++;
      }
    }
  }

  /** Store.consistency() starts; opens a window unless an LCG window is open. */
  static boolean consistencyStart() {
    if (lcgOpen) {
      return false;
    }
    open();
    return true;
  }

  static void consistencyEnd(boolean outer, boolean failed) {
    if (outer) {
      close(failed);
    }
  }

  /** A constraint is put into a queue. */
  static void enqueued(Constraint c) {
    c.fsQueuedCalls = cumCalls;
    c.fsQueuedProp = cumProp;
  }

  /** A propagator call finished (normally or by failure). */
  static void called(Constraint c, long nanos, int q) {
    if (q == 8) {
      frontRuns++;
    }
    called(c, nanos);
  }

  static void called(Constraint c, long nanos) {
    cumCalls++;
    cumProp += nanos;
    if (c.fsWindow == windowIndex) {
      c.fsRuns++;
    } else {
      c.fsWindow = windowIndex;
      c.fsRuns = 1;
    }
  }

  /** The constraint failed; called after {@link #called}. */
  static void failed(Constraint c, long nanos, int queue) {
    winFailed = true;
    fails++;
    if (queue == 8) {
      frontFails++;
    }
    fingerprint = fingerprint * 31 + windowIndex;
    if (RECORD != null) {
      if (recSize + 2 > rec.length) {
        rec = Arrays.copyOf(rec, rec.length * 2);
      }
      rec[recSize++] = (int) windowIndex;
      rec[recSize++] = c.fsSerial;
    }
    if (ON) {
      failByConstraint++;
      long cb = cumCalls - 1 - winStartCalls;
      long pb = cumProp - nanos - winStartProp;
      callsBefore += cb;
      propBefore += pb;
      failCallNanos += nanos;
      if (cb == 0) {
        firstCall++;
      }
      boolean atStart = c.fsQueuedCalls <= winStartCalls;
      long qp = Math.max(c.fsQueuedProp, winStartProp);
      long w = cumProp - nanos - qp;
      waitProp += w;
      if (atStart) {
        queuedAtStart++;
        waitPropAtStart += w;
      }
      if (c.fsRuns > 1) {
        ranBefore++;
      }
      int q = Math.min(queue, 7);
      queueFails[q]++;
      queueBefore[q] += pb;
      String k = c.getClass().getSimpleName();
      long[] a = byClass.computeIfAbsent(k, x -> new long[6]);
      a[0]++;
      a[1] += pb;
      a[2] += nanos;
      a[3] += w;
      a[4] += atStart ? 1 : 0;
      if (lruSize > 0 && lru[0] == c) {
        sameAsLast++;
        a[5]++;
      }
      for (int i = 0; i < lruSize; i++) {
        if (lru[i] == c) {
          if (i < 8) {
            inLast8++;
          }
          if (i < 32) {
            inLast32++;
          }
          break;
        }
      }
    }
    // LRU update
    int pos = -1;
    for (int i = 0; i < lruSize; i++) {
      if (lru[i] == c) {
        pos = i;
        break;
      }
    }
    Constraint evicted = null;
    if (pos < 0) {
      if (lruSize < lru.length) {
        lruSize++;
      }
      pos = lruSize - 1;
      evicted = lru[pos];
    }
    System.arraycopy(lru, 0, lru, 1, pos);
    lru[0] = c;
    if (FRONT > 0) {
      c.fsHot = true;
      if (FRONT < lruSize) {
        lru[FRONT].fsHot = false;
      }
      if (evicted != null) {
        evicted.fsHot = false;
      }
    }
  }

  /**
   * Oracle replay: the constraint recorded as failing in this window, or null. Called at the start
   * of an outer window.
   */
  static int oracleTarget() {
    if (oracle == null) {
      return -1;
    }
    while (oraclePos + 1 < oracle.length && oracle[oraclePos] < windowIndex) {
      oraclePos += 2;
    }
    if (oraclePos + 1 < oracle.length && oracle[oraclePos] == windowIndex) {
      return oracle[oraclePos + 1];
    }
    return -1;
  }

  static synchronized void writeTime(boolean limit) {
    if (TIME_FILE == null) {
      return;
    }
    try (PrintWriter w = new PrintWriter(new FileWriter(TIME_FILE, true))) {
      w.println(
          "{\"tag\":\""
              + System.getProperty("jacop.failstat.tag", "")
              + "\",\"limit\":"
              + limit
              + ",\"windows\":"
              + windowIndex
              + ",\"fails\":"
              + fails
              + ",\"fp\":"
              + fingerprint
              + ",\"ns\":"
              + (System.nanoTime() - t0)
              + ",\"oracleRuns\":"
              + oracleRuns
              + ",\"oracleFailFirst\":"
              + oracleFailFirst
              + ",\"frontRuns\":"
              + frontRuns
              + ",\"frontFails\":"
              + frontFails
              + "}");
    } catch (IOException e) {
      e.printStackTrace();
    }
    if (ON) {
      dump();
    }
  }

  static void dump() {
    try {
      if (RECORD != null) {
        try (DataOutputStream out =
            new DataOutputStream(new BufferedOutputStream(new FileOutputStream(RECORD)))) {
          out.writeInt(recSize);
          for (int i = 0; i < recSize; i++) {
            out.writeInt(rec[i]);
          }
        }
      }
      if (FILE == null) {
        return;
      }
      StringBuilder sb = new StringBuilder();
      sb.append("{\"tag\":\"").append(System.getProperty("jacop.failstat.tag", "")).append('"');
      kv(sb, "windows", windows);
      kv(sb, "failWindows", failWindows);
      kv(sb, "failByConstraint", failByConstraint);
      kv(sb, "failByClause", failByClause);
      kv(sb, "wallAll", wallAll);
      kv(sb, "wallFail", wallFail);
      kv(sb, "propAll", propAll);
      kv(sb, "propFail", propFail);
      kv(sb, "callsAll", callsAll);
      kv(sb, "callsFail", callsFail);
      kv(sb, "callsBefore", callsBefore);
      kv(sb, "propBefore", propBefore);
      kv(sb, "failCallNanos", failCallNanos);
      kv(sb, "firstCall", firstCall);
      kv(sb, "queuedAtStart", queuedAtStart);
      kv(sb, "ranBefore", ranBefore);
      kv(sb, "waitProp", waitProp);
      kv(sb, "waitPropAtStart", waitPropAtStart);
      kv(sb, "sameAsLast", sameAsLast);
      kv(sb, "inLast8", inLast8);
      kv(sb, "inLast32", inLast32);
      kv(sb, "oracleRuns", oracleRuns);
      kv(sb, "oracleFailFirst", oracleFailFirst);
      sb.append(",\"queueFails\":").append(Arrays.toString(queueFails));
      sb.append(",\"queueBefore\":").append(Arrays.toString(queueBefore));
      sb.append(",\"byClass\":{");
      boolean first = true;
      for (Map.Entry<String, long[]> e : new TreeMap<>(byClass).entrySet()) {
        if (!first) {
          sb.append(',');
        }
        first = false;
        sb.append('"').append(e.getKey()).append("\":").append(Arrays.toString(e.getValue()));
      }
      sb.append("}}\n");
      try (PrintWriter w = new PrintWriter(new FileWriter(FILE, true))) {
        w.print(sb);
      }
    } catch (IOException e) {
      e.printStackTrace();
    }
  }

  private static void kv(StringBuilder sb, String k, long v) {
    sb.append(",\"").append(k).append("\":").append(v);
  }
}
