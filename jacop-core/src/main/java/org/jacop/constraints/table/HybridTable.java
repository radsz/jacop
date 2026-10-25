/*
 * HybridTable.java
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

package org.jacop.constraints.table;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.atomic.AtomicInteger;
import org.jacop.api.Copyable;
import org.jacop.api.SatisfiedPresent;
import org.jacop.api.Stateful;
import org.jacop.api.UsesQueueVariable;
import org.jacop.api.VarMap;
import org.jacop.constraints.Constraint;
import org.jacop.core.InitOnce;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.IntervalEnumeration;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.core.Var;

/**
 * HybridTable is a table constraint whose tuples may contain restrictions instead of values: the
 * wildcard {@code *} of short tables, {@code != v}, {@code < v}, {@code <= v}, {@code > v}, {@code
 * >= v}, {@code in S}, {@code not in S}, and comparisons with another column of the same tuple such
 * as {@code x[i] <= x[j] + c}. A tuple of values is allowed if some hybrid tuple accepts it in
 * every column. Such tables are called hybrid tables (Lecoutre et al., IJCAI 2026) or smart tables
 * (Mairy, Deville and Lecoutre, CPAIOR 2015). Ordinary tables, short tables and compressed tables
 * are special cases.
 *
 * <p>Filtering follows CT^bs, "Extending Compact-Table to Basic Smart Tables", Hélène Verhaeghe,
 * Christophe Lecoutre, Yves Deville and Pierre Schaus, CP 2017, which builds on Compact-Table
 * (Demeulenaere et al., CP 2016) and CT* (Verhaeghe, Lecoutre and Schaus, AAAI 2017). The valid
 * hybrid tuples are kept in a reversible sparse bit-set. The values of each column are split into
 * classes, the constants of the column and the intervals between them, so that every unary
 * restriction accepts whole classes; this keeps the bit-sets small even for huge domains. When a
 * variable loses values the bit-set is updated either from the classes that remain (reset) or
 * incrementally from the classes that were removed, with dedicated bit-sets for tuples whose column
 * is {@code = v}, {@code != v}, a lower or an upper bound. Tuples with restrictions between columns
 * are also kept in the bit-set, and in addition are checked one by one, as in tabular reduction, by
 * arc consistency on their restrictions.
 *
 * <p>The constraint achieves generalized arc consistency when the restrictions between columns of
 * each tuple form a forest, which includes all tables without such restrictions. Otherwise it
 * enforces arc consistency on each tuple and is weaker, but still correct.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
public class HybridTable extends Constraint
    implements UsesQueueVariable, Stateful, SatisfiedPresent, Copyable<HybridTable> {

  static final AtomicInteger idNumber = new AtomicInteger(0);

  /** Variables within the scope of the constraint. */
  final IntVar[] x;

  /**
   * The restrictions of the hybrid tuples, tuple t in cells[t * arity .. t * arity + arity - 1].
   */
  Restriction[] cells;

  /** The number of hybrid tuples. */
  int tupleCount;

  /** True to expand the tuples with restrictions between columns when the constraint is imposed. */
  private final boolean expandBetweenColumns;

  private final Map<IntVar, Integer> varMap;

  private final int arity;

  private Store store;

  /** Number of 64-bit words of the bit-sets. */
  private int words;

  // Value classes of each column: constants[i] are the sorted constants mentioned by the unary
  // restrictions of column i. Class 2p + 1 is the constant constants[i][p] and class 2p the
  // interval between constants[i][p - 1] and constants[i][p] (both excluded, unbounded at the
  // ends). Every unary restriction accepts whole classes.
  private int[][] constants;
  private int[][] classMin;
  private int[][] classMax;

  /** The tuples whose restriction on column i accepts class c, null when there are none. */
  private long[][][] supports;

  /** The tuples whose restriction on column i is {@code = v} for the constant of class c. */
  private long[][][] equalSupports;

  /** The tuples whose restriction on column i is {@code != v} for the constant of class c. */
  private long[][][] notEqualSupports;

  // Tuples whose restriction on column i is an upper bound (lower bound, set membership): all of
  // them, and those that accept class c. An upper bound holds iff it accepts the class of the
  // minimum, a lower bound iff it accepts the class of the maximum.
  private long[][] upperAll;
  private long[][][] upperAccept;
  private long[][] lowerAll;
  private long[][][] lowerAccept;
  private long[][] setAll;
  private long[][][] setAccept;

  /** Tuples with a restriction between columns, null when there are none. */
  private long[] binaryAll;

  /** Tuples with a restriction between columns that involves column i. */
  private long[][] binaryColumn;

  /** For each tuple with restrictions between columns, the columns these involve. */
  private int[][] binaryColumns;

  /** For each tuple with restrictions between columns, the columns holding such restrictions. */
  private int[][] binarySources;

  /** The domains of the IN and NOT_IN restrictions, by tuple and column. */
  private IntDomain[][] setDomains;

  private int[][] residues;

  /** The classes of each column that may still intersect its domain, first liveSize of them. */
  private int[][] live;

  // Reversible sparse bit-set of the valid tuples, as in Compact-Table: the non-zero words are
  // index[0..limit]. Record liveRecord + i of state holds the number of live classes of column i.
  private TrailedTupleSet valid;
  private long[] state;
  private int[] index;
  private long[] mask;

  /** Work space of the tuples whose in or not in restriction accepts a live class. */
  private long[] temp;

  private int liveRecord;

  /** Position of each variable indexed by its store index minus indexOffset, or -1. */
  private int[] positionByIndex;

  private int indexOffset;

  private int[] queue;
  private int queueSize;
  private boolean[] queued;
  private boolean pruning;
  private final InitOnce init = new InitOnce();

  // Work space of the tuples with restrictions between columns.
  private IntDomain[] work;
  private IntDomain[] binarySupport;

  // When the columns involved in restrictions between columns have small spans, the values the
  // tuples with such restrictions support are marked in bit-sets instead of collected in domains:
  // value v of column i is bit v - markBase[i] of marks[i]. markCount[i] counts the marked values
  // and markNeed[i] is the domain size, so a column whose values are all marked is skipped.
  private boolean useMarks;
  private int[] markBase;
  private long[][] marks;
  private int[] markCount;
  private int[] markNeed;
  private static final int MAX_MARK_SPAN = 1 << 16;

  // When moreover these spans are at most 64, a tuple is checked on one word per column: the
  // domain of column k as a bit-set relative to markBase[k] is domainMask[k], and the values the
  // unary restriction of tuple t on column k accepts are unaryMask[t][k].
  private boolean wordMasks;
  private long[] domainMask;
  private long[][] unaryMask;
  private long[] maskWork;

  /**
   * It constructs a hybrid table constraint.
   *
   * @param list the variables in the scope of the constraint.
   * @param tuples the hybrid tuples, each with one restriction per variable.
   */
  public HybridTable(IntVar[] list, Restriction[][] tuples) {
    this(list, tuples, true);
  }

  /**
   * It constructs a hybrid table constraint.
   *
   * @param list the variables in the scope of the constraint.
   * @param tuples the hybrid tuples, each with one restriction per variable.
   * @param expandBetweenColumns true to replace, where it is cheap, a tuple with restrictions
   *     between columns by one tuple per value of the columns they refer to, so that only unary
   *     restrictions remain and the bit-sets handle it.
   */
  public HybridTable(IntVar[] list, Restriction[][] tuples, boolean expandBetweenColumns) {

    if (list == null || tuples == null) {
      throw new IllegalArgumentException("HybridTable: list and tuples must not be null");
    }
    checkInputForNullness(new String[] {"list", "tuples"}, list, tuples);
    checkInputForDuplication("list", list);
    this.arity = list.length;
    for (Restriction[] tuple : tuples) {
      if (tuple == null || tuple.length != arity) {
        throw new IllegalArgumentException(
            "HybridTable: each tuple needs one restriction per variable");
      }
      for (int i = 0; i < arity; i++) {
        Restriction r = tuple[i];
        if (r == null) {
          throw new IllegalArgumentException("HybridTable: a restriction is null");
        }
        if (r.isBinary() && (r.column >= arity || r.column == i)) {
          throw new IllegalArgumentException(
              "HybridTable: restriction " + r + " of column " + i + " refers to a wrong column");
        }
      }
    }
    this.x = Arrays.copyOf(list, list.length);
    this.expandBetweenColumns = expandBetweenColumns;
    setTuples(tuples);
    this.varMap = Var.positionMapping(list, false, this.getClass());
    this.queueIndex = 1;
    numberId = idNumber.incrementAndGet();
    setScope(list);
  }

  /** A copy over the counterparts of the variables; the restrictions are shared. */
  private HybridTable(HybridTable original, VarMap map) {
    this.arity = original.arity;
    this.x = map.get(original.x);
    this.expandBetweenColumns = original.expandBetweenColumns;
    this.cells = original.cells;
    this.tupleCount = original.tupleCount;
    this.varMap = Var.positionMapping(x, false, this.getClass());
    this.queueIndex = 1;
    numberId = idNumber.incrementAndGet();
    setScope(x);
  }

  private void setTuples(Restriction[][] rows) {
    tupleCount = rows.length;
    cells = new Restriction[tupleCount * arity];
    for (int t = 0; t < tupleCount; t++) {
      System.arraycopy(rows[t], 0, cells, t * arity, arity);
    }
  }

  /** A tuple is expanded only if the columns it refers to have at most this many combinations. */
  private static final int EXPANSION_LIMIT = 64;

  /**
   * It replaces each tuple with restrictions between columns, whose referred columns have unary
   * restrictions and few values, by one tuple per combination of values of the referred columns. In
   * each of them the referred columns are fixed and the restrictions between columns become
   * comparisons with constants, so the tuples allow the same assignments of the current domains.
   */
  private static Restriction[][] expandBetweenColumns(IntVar[] x, Restriction[][] tuples) {
    List<Restriction[]> result = null;
    for (int t = 0; t < tuples.length; t++) {
      Restriction[][] expanded = expandTuple(x, tuples[t]);
      if (expanded != null && result == null) {
        result = new ArrayList<>(Arrays.asList(tuples).subList(0, t));
      }
      if (result != null) {
        result.addAll(
            expanded == null ? List.<Restriction[]>of(tuples[t]) : Arrays.asList(expanded));
      }
    }
    return result == null ? tuples : result.toArray(new Restriction[0][]);
  }

  /** The expansion of a tuple, or null if it has no restriction between columns or is too large. */
  private static Restriction[][] expandTuple(IntVar[] x, Restriction[] tuple) {
    int arity = tuple.length;
    boolean[] referred = new boolean[arity];
    boolean binary = false;
    for (Restriction r : tuple) {
      if (r.isBinary()) {
        binary = true;
        referred[r.column] = true;
      }
    }
    if (!binary) {
      return null;
    }
    // The values of each referred column that its own restriction accepts.
    int[][] values = new int[arity][];
    long combinations = 1;
    for (int j = 0; j < arity; j++) {
      if (referred[j]) {
        if (tuple[j].isBinary() || x[j].getSize() > EXPANSION_LIMIT) {
          return null;
        }
        List<Integer> accepted = new ArrayList<>();
        for (ValueEnumeration e = x[j].dom().valueEnumeration(); e.hasMoreElements(); ) {
          int v = e.nextElement();
          if (tuple[j].accepts(v)) {
            accepted.add(v);
          }
        }
        values[j] = accepted.stream().mapToInt(Integer::intValue).toArray();
        combinations *= values[j].length;
        if (combinations > EXPANSION_LIMIT) {
          return null;
        }
      }
    }
    List<Restriction[]> rows = new ArrayList<>();
    int[] choice = new int[arity];
    for (long c = 0; c < combinations; c++) {
      long rest = c;
      for (int j = 0; j < arity; j++) {
        if (referred[j]) {
          choice[j] = values[j][(int) (rest % values[j].length)];
          rest /= values[j].length;
        }
      }
      Restriction[] row = new Restriction[arity];
      boolean representable = true;
      for (int i = 0; i < arity && representable; i++) {
        Restriction r = tuple[i];
        if (referred[i]) {
          row[i] = Restriction.eq(choice[i]);
        } else if (r.isBinary()) {
          long bound = (long) choice[r.column] + r.offset;
          representable = bound >= Integer.MIN_VALUE && bound <= Integer.MAX_VALUE;
          row[i] = representable ? Restriction.compare(r.relation, (int) bound) : null;
        } else {
          row[i] = r;
        }
      }
      if (!representable) {
        return null;
      }
      rows.add(row);
    }
    return rows.toArray(new Restriction[0][]);
  }

  /**
   * It constructs a short table constraint, a table in which a special value stands for any value.
   *
   * @param list the variables in the scope of the constraint.
   * @param tuples the tuples.
   * @param star the value which stands for any value.
   */
  public HybridTable(IntVar[] list, int[][] tuples, int star) {
    this(list, toRestrictions(tuples, star));
  }

  /**
   * It constructs a table constraint over tuples of values.
   *
   * @param list the variables in the scope of the constraint.
   * @param tuples the allowed tuples.
   */
  public HybridTable(IntVar[] list, int[][] tuples) {
    this(list, toRestrictions(tuples, null));
  }

  private static Restriction[][] toRestrictions(int[][] tuples, Integer star) {
    if (tuples == null) {
      throw new IllegalArgumentException("HybridTable: tuples is null");
    }
    // One restriction object per distinct value, so a large table costs one reference per entry.
    Map<Integer, Restriction> equal = new HashMap<>();
    Restriction[][] result = new Restriction[tuples.length][];
    for (int t = 0; t < tuples.length; t++) {
      result[t] = new Restriction[tuples[t].length];
      for (int i = 0; i < tuples[t].length; i++) {
        int v = tuples[t][i];
        result[t][i] =
            star != null && v == star
                ? Restriction.any()
                : equal.computeIfAbsent(v, Restriction::eq);
      }
    }
    return result;
  }

  @Override
  public void impose(Store store) {

    this.store = store;
    if (expandBetweenColumns && Arrays.stream(cells).anyMatch(Restriction::isBinary)) {
      // The expansion depends on the domains, so it is done for the domains at imposition.
      Restriction[][] rows = new Restriction[tupleCount][];
      for (int t = 0; t < tupleCount; t++) {
        rows[t] = Arrays.copyOfRange(cells, t * arity, t * arity + arity);
      }
      Restriction[][] expanded = expandBetweenColumns(x, rows);
      if (expanded != rows) {
        setTuples(expanded);
      }
    }
    int n = tupleCount;
    valid = new TrailedTupleSet(n, arity);
    words = valid.words;
    queue = new int[arity];
    queued = new boolean[arity];
    buildClasses();
    buildSupports();

    state = valid.state;
    index = valid.index;
    mask = valid.mask;
    liveRecord = valid.limitRecord + 1;
    temp = new long[words];

    // Initial live classes and removal of the tuples that are not valid.
    live = new int[arity][];
    for (int i = 0; i < arity; i++) {
      int classes = classMin[i].length;
      int[] l = new int[classes];
      int size = 0;
      IntDomain d = x[i].dom();
      for (int c = 0; c < classes; c++) {
        if (classMin[i][c] <= classMax[i][c] && d.isIntersecting(classMin[i][c], classMax[i][c])) {
          l[size++] = c;
        }
      }
      int removed = size;
      for (int c = 0; c < classes; c++) {
        if (classMin[i][c] > classMax[i][c] || !d.isIntersecting(classMin[i][c], classMax[i][c])) {
          l[removed++] = c;
        }
      }
      live[i] = l;
      state[liveRecord + i] = size;
      valid.clearMask();
      for (int p = 0; p < size; p++) {
        addToMask(supports[i][l[p]]);
      }
      for (int w = 0; w < words; w++) {
        state[w] &= mask[w];
      }
    }
    valid.rebuildIndex();

    work = new IntDomain[arity];
    binarySupport = new IntDomain[arity];
    if (binaryAll != null) {
      useMarks = true;
      markBase = new int[arity];
      marks = new long[arity][];
      markCount = new int[arity];
      markNeed = new int[arity];
      for (int i = 0; i < arity; i++) {
        if (binaryColumn[i] != null) {
          long span = (long) x[i].max() - x[i].min() + 1;
          if (span > MAX_MARK_SPAN) {
            useMarks = false;
          } else {
            markBase[i] = x[i].min();
            marks[i] = new long[(int) ((span + 63) >> 6)];
          }
        }
      }
      wordMasks = useMarks;
      for (int i = 0; i < arity && wordMasks; i++) {
        wordMasks = marks[i] == null || marks[i].length == 1;
      }
      if (wordMasks) {
        domainMask = new long[arity];
        maskWork = new long[arity];
        unaryMask = new long[n][];
        for (int t = 0; t < n; t++) {
          if (binaryColumns[t] == null) {
            continue;
          }
          unaryMask[t] = new long[arity];
          for (int k : binaryColumns[t]) {
            long m = 0L;
            long span = (long) x[k].max() - markBase[k] + 1;
            for (int q = 0; q < span; q++) {
              if (cells[t * arity + k].accepts(markBase[k] + q)) {
                m |= 1L << q;
              }
            }
            unaryMask[t][k] = m;
          }
        }
      }
    }

    positionByIndex = TrailedTupleSet.positionByIndex(x);
    indexOffset = TrailedTupleSet.minIndex(x);

    super.impose(store);
  }

  private void buildClasses() {
    constants = new int[arity][];
    classMin = new int[arity][];
    classMax = new int[arity][];
    for (int i = 0; i < arity; i++) {
      List<Integer> values = new ArrayList<>();
      for (int t = 0; t < tupleCount; t++) {
        Restriction r = cells[t * arity + i];
        switch (r.kind) {
          case EQ, NE, LE, GE -> values.add(r.value);
          case IN, NOT_IN -> {
            for (int v : r.values) {
              values.add(v);
            }
          }
          default -> {
            // ANY and COLUMN accept every class.
          }
        }
      }
      int[] cs = values.stream().mapToInt(Integer::intValue).sorted().distinct().toArray();
      constants[i] = cs;
      int classes = 2 * cs.length + 1;
      classMin[i] = new int[classes];
      classMax[i] = new int[classes];
      for (int c = 0; c < classes; c++) {
        int p = c >> 1;
        if ((c & 1) == 1) {
          classMin[i][c] = cs[p];
          classMax[i][c] = cs[p];
        } else {
          long lo = p == 0 ? IntDomain.MIN_INT : (long) cs[p - 1] + 1;
          long hi = p == cs.length ? IntDomain.MAX_INT : (long) cs[p] - 1;
          lo = Math.max(lo, IntDomain.MIN_INT);
          hi = Math.min(hi, IntDomain.MAX_INT);
          if (lo > hi) {
            classMin[i][c] = 1;
            classMax[i][c] = 0;
          } else {
            classMin[i][c] = (int) lo;
            classMax[i][c] = (int) hi;
          }
        }
      }
    }
  }

  private int classOf(int i, int v) {
    int p = Arrays.binarySearch(constants[i], v);
    return p >= 0 ? 2 * p + 1 : -2 * (p + 1);
  }

  private static void setBit(long[][] sets, int c, int t, int words) {
    if (sets[c] == null) {
      sets[c] = new long[words];
    }
    sets[c][t >> 6] |= 1L << t;
  }

  private static long[] setBit(long[] set, int t, int words) {
    long[] s = set == null ? new long[words] : set;
    s[t >> 6] |= 1L << t;
    return s;
  }

  private void buildSupports() {
    int n = tupleCount;
    supports = new long[arity][][];
    equalSupports = new long[arity][][];
    notEqualSupports = new long[arity][][];
    upperAll = new long[arity][];
    upperAccept = new long[arity][][];
    lowerAll = new long[arity][];
    lowerAccept = new long[arity][][];
    setAll = new long[arity][];
    setAccept = new long[arity][][];
    binaryColumn = new long[arity][];
    residues = new int[arity][];
    binaryColumns = new int[n][];
    binarySources = new int[n][];
    setDomains = new IntDomain[n][];

    for (int i = 0; i < arity; i++) {
      int classes = classMin[i].length;
      long[][] sup = new long[classes][];
      long[][] eq = new long[classes][];
      long[][] ne = new long[classes][];
      long[][] upper = new long[classes][];
      long[][] lower = new long[classes][];
      long[][] set = new long[classes][];
      boolean onlyEquality = true;
      for (int t = 0; t < n; t++) {
        Restriction r = cells[t * arity + i];
        if (r.kind != Restriction.Kind.EQ) {
          onlyEquality = false;
        }
        switch (r.kind) {
          case EQ -> {
            int c = classOf(i, r.value);
            setBit(sup, c, t, words);
          }
          case NE -> {
            setBit(ne, classOf(i, r.value), t, words);
            for (int c = 0; c < classes; c++) {
              if (c != classOf(i, r.value)) {
                setBit(sup, c, t, words);
              }
            }
          }
          case LE, GE -> {
            for (int c = 0; c < classes; c++) {
              if (classMin[i][c] <= classMax[i][c] && r.accepts(classMin[i][c])) {
                setBit(sup, c, t, words);
                setBit(r.kind == Restriction.Kind.LE ? upper : lower, c, t, words);
              }
            }
            if (r.kind == Restriction.Kind.LE) {
              upperAll[i] = setBit(upperAll[i], t, words);
            } else {
              lowerAll[i] = setBit(lowerAll[i], t, words);
            }
          }
          case IN, NOT_IN -> {
            for (int c = 0; c < classes; c++) {
              if (classMin[i][c] <= classMax[i][c] && r.accepts(classMin[i][c])) {
                setBit(sup, c, t, words);
                setBit(set, c, t, words);
              }
            }
            setAll[i] = setBit(setAll[i], t, words);
            if (setDomains[t] == null) {
              setDomains[t] = new IntDomain[arity];
            }
            IntDomain d = new IntervalDomain();
            for (int v : r.values) {
              d.unionAdapt(v, v);
            }
            setDomains[t][i] = d;
          }
          default -> {
            // ANY and COLUMN accept every class.
            for (int c = 0; c < classes; c++) {
              setBit(sup, c, t, words);
            }
          }
        }
      }
      // The equality tuples of a class are its supports when every restriction is an equality.
      for (int c = 0; c < classes; c++) {
        if (onlyEquality) {
          eq[c] = sup[c];
        }
      }
      if (!onlyEquality) {
        for (int t = 0; t < n; t++) {
          Restriction r = cells[t * arity + i];
          if (r.kind == Restriction.Kind.EQ) {
            setBit(eq, classOf(i, r.value), t, words);
          }
        }
      }
      supports[i] = sup;
      equalSupports[i] = eq;
      notEqualSupports[i] = Arrays.stream(ne).allMatch(a -> a == null) ? null : ne;
      upperAccept[i] = upper;
      lowerAccept[i] = lower;
      setAccept[i] = set;
      residues[i] = new int[classes];
    }

    for (int t = 0; t < n; t++) {
      boolean[] involved = new boolean[arity];
      int sources = 0;
      for (int i = 0; i < arity; i++) {
        Restriction r = cells[t * arity + i];
        if (r.isBinary()) {
          involved[i] = true;
          involved[r.column] = true;
          sources++;
        }
      }
      if (sources == 0) {
        continue;
      }
      binaryAll = setBit(binaryAll, t, words);
      int[] cols = new int[arity];
      int count = 0;
      for (int i = 0; i < arity; i++) {
        if (involved[i]) {
          cols[count++] = i;
          binaryColumn[i] = setBit(binaryColumn[i], t, words);
        }
      }
      binaryColumns[t] = Arrays.copyOf(cols, count);
      int[] src = new int[sources];
      int s = 0;
      for (int i = 0; i < arity; i++) {
        if (cells[t * arity + i].isBinary()) {
          src[s++] = i;
        }
      }
      binarySources[t] = src;
    }
  }

  // ---------------------------------------------------------------------------------------------
  // Trailing.

  @Override
  public void removeLevel(int level) {
    valid.removeLevel(level);
    for (int p = 0; p < queueSize; p++) {
      queued[queue[p]] = false;
    }
    queueSize = 0;
    pruning = false;
  }

  @Override
  public void queueVariable(int level, Var v) {
    if (pruning) {
      return;
    }
    int p = TrailedTupleSet.column(v, positionByIndex, indexOffset, varMap);
    if (p >= 0 && !queued[p]) {
      queued[p] = true;
      queue[queueSize++] = p;
    }
  }

  // ---------------------------------------------------------------------------------------------
  // Reversible sparse bit-set.

  private int limit() {
    return valid.limit();
  }

  private void addToMask(long[] set) {
    if (set != null) {
      valid.addToMask(set);
    }
  }

  /** It adds to the mask the tuples of all that are not in accepted. */
  private void addToMaskDifference(long[] all, long[] accepted) {
    int limit = limit();
    if (accepted == null) {
      addToMask(all);
      return;
    }
    for (int p = 0; p <= limit; p++) {
      int w = index[p];
      mask[w] |= all[w] & ~accepted[w];
    }
  }

  /** It checks whether the valid tuples, without the excluded ones, meet the set. */
  private boolean intersects(int i, int c, long[] set, long[] excluded) {
    int[] res = residues[i];
    int r = res[c];
    if (excluded == null) {
      if ((state[r] & set[r]) != 0L) {
        return true;
      }
    } else if ((state[r] & set[r] & ~excluded[r]) != 0L) {
      return true;
    }
    int limit = limit();
    for (int p = 0; p <= limit; p++) {
      int w = index[p];
      long word = state[w] & set[w];
      if (excluded != null) {
        word &= ~excluded[w];
      }
      if (word != 0L) {
        res[c] = w;
        return true;
      }
    }
    return false;
  }

  private boolean intersects(long[] set) {
    int limit = limit();
    for (int p = 0; p <= limit; p++) {
      int w = index[p];
      if ((state[w] & set[w]) != 0L) {
        return true;
      }
    }
    return false;
  }

  // ---------------------------------------------------------------------------------------------
  // Propagation.

  @Override
  public void consistency(Store store) {

    valid.newEpochIfNeeded(store.level);
    pruning = false;
    valid.changed = false;

    if (limit() < 0) {
      throw Store.failException;
    }

    int changed = queueSize;
    int onlyChanged = queueSize == 1 ? queue[0] : -1;
    for (int p = 0; p < queueSize; p++) {
      int i = queue[p];
      queued[i] = false;
      updateTable(i);
    }
    queueSize = 0;

    if (binaryAll != null) {
      reviseBinaryTuples();
    }

    if (init.begin(store)) {
      onlyChanged = -1;
      changed = arity;
    } else if (onlyChanged >= 0
        && binaryColumn[onlyChanged] != null
        && intersects(binaryColumn[onlyChanged])) {
      // Restrictions between columns can remove further values of the changed column itself,
      // for example x[1] > x[2] and x[2] >= x[1] - 1 in one tuple.
      onlyChanged = -1;
    } else if (!valid.changed && (binaryAll == null || !intersects(binaryAll))) {
      // The valid tuples are those of the previous call, which supported every remaining value.
      return;
    }

    pruning = true;
    int notGround = 0;
    for (int i = 0; i < arity; i++) {
      IntVar xi = x[i];
      boolean wasSingleton = xi.singleton();
      if (i != onlyChanged && (!wasSingleton || changed > 0)) {
        filterDomain(i);
      }
      if (!xi.singleton()) {
        notGround++;
      }
    }
    pruning = false;

    if (notGround <= 1) {
      removeConstraint();
    }
  }

  private int liveSize(int i) {
    return (int) state[liveRecord + i];
  }

  private void setLiveSize(int i, int size) {
    valid.set(liveRecord + i, size);
  }

  /** It updates the valid tuples after the domain of variable i changed. */
  private void updateTable(int i) {

    IntDomain d = x[i].dom();
    int[] l = live[i];
    int size = liveSize(i);
    int[] cMin = classMin[i];
    int[] cMax = classMax[i];
    int s = size;
    int p = 0;
    while (p < s) {
      int c = l[p];
      int lo = cMin[c];
      int hi = cMax[c];
      if (lo == hi ? d.contains(lo) : d.isIntersecting(lo, hi)) {
        p++;
      } else {
        s--;
        l[p] = l[s];
        l[s] = c;
      }
    }
    if (s == size) {
      return;
    }
    setLiveSize(i, s);

    valid.clearMask();
    long[][] sup = supports[i];
    if (s <= size - s) {
      for (int k = 0; k < s; k++) {
        addToMask(sup[l[k]]);
      }
    } else {
      long[][] eq = equalSupports[i];
      for (int k = s; k < size; k++) {
        addToMask(eq[l[k]]);
      }
      if (notEqualSupports[i] != null && d.singleton()) {
        addToMask(notEqualSupports[i][classOf(i, d.value())]);
      }
      if (upperAll[i] != null) {
        addToMaskDifference(upperAll[i], upperAccept[i][classOf(i, d.min())]);
      }
      if (lowerAll[i] != null) {
        addToMaskDifference(lowerAll[i], lowerAccept[i][classOf(i, d.max())]);
      }
      if (setAll[i] != null) {
        addToMaskDifference(setAll[i], acceptedBySet(i, l, s));
      }
      valid.reverseMask();
    }
    valid.intersectWithMask();

    if (limit() < 0) {
      throw Store.failException;
    }
  }

  /** The tuples whose in or not in restriction on column i accepts one of the live classes. */
  private long[] acceptedBySet(int i, int[] l, int s) {
    int limit = limit();
    for (int p = 0; p <= limit; p++) {
      temp[index[p]] = 0L;
    }
    for (int k = 0; k < s; k++) {
      long[] accepted = setAccept[i][l[k]];
      if (accepted != null) {
        for (int p = 0; p <= limit; p++) {
          int w = index[p];
          temp[w] |= accepted[w];
        }
      }
    }
    return temp;
  }

  /**
   * It checks every valid tuple with restrictions between columns by arc consistency on its
   * restrictions, removes the tuples that fail and collects the values the others support.
   */
  private void reviseBinaryTuples() {

    if (useMarks) {
      for (int i = 0; i < arity; i++) {
        if (marks[i] != null) {
          Arrays.fill(marks[i], 0L);
          markCount[i] = 0;
          markNeed[i] = x[i].getSize();
          if (wordMasks) {
            domainMask[i] = wordOf(i, x[i].dom());
          }
        }
      }
    } else {
      Arrays.fill(binarySupport, null);
    }
    int limit = limit();
    for (int p = limit; p >= 0; p--) {
      int w = index[p];
      long bits = state[w] & binaryAll[w];
      while (bits != 0L) {
        int b = Long.numberOfTrailingZeros(bits);
        bits &= bits - 1;
        int t = (w << 6) + b;
        boolean consistent;
        if (wordMasks) {
          consistent = reviseTupleOnWords(t);
        } else if (useMarks && binarySources[t].length == 1) {
          consistent = reviseSingleRestriction(t);
        } else {
          consistent = reviseTuple(t);
        }
        if (!consistent) {
          valid.removeTuple(t, p);
        }
      }
    }
    if (limit() < 0) {
      throw Store.failException;
    }
  }

  /** The values of d as a bit-set relative to markBase[i]. */
  private long wordOf(int i, IntDomain d) {
    long m = 0L;
    int base = markBase[i];
    int v = d.min();
    while (true) {
      m |= 1L << (v - base);
      int next = d.nextValue(v);
      if (next == v) {
        return m;
      }
      v = next;
    }
  }

  /** The bit-set of the positions p with p at most bound, for 64 positions. */
  private static long atMostWord(long bound) {
    if (bound < 0) {
      return 0L;
    }
    return bound >= 63 ? -1L : (1L << (bound + 1)) - 1;
  }

  /** The bit-set of the positions p with p at least bound, for 64 positions. */
  private static long atLeastWord(long bound) {
    if (bound > 63) {
      return 0L;
    }
    return bound <= 0 ? -1L : -1L << bound;
  }

  private static long shiftWord(long m, long by) {
    if (by >= 64 || by <= -64) {
      return 0L;
    }
    return by >= 0 ? m << by : m >>> -by;
  }

  /**
   * It removes from mi the positions p without a position q in mj such that p relation q + offset.
   */
  private static long reviseWord(long mi, Restriction.Relation relation, long mj, long offset) {
    return switch (relation) {
      case LT -> mi & atMostWord(63 - Long.numberOfLeadingZeros(mj) + offset - 1);
      case LE -> mi & atMostWord(63 - Long.numberOfLeadingZeros(mj) + offset);
      case GT -> mi & atLeastWord(Long.numberOfTrailingZeros(mj) + offset + 1);
      case GE -> mi & atLeastWord(Long.numberOfTrailingZeros(mj) + offset);
      case EQ -> mi & shiftWord(mj, offset);
      case NE -> Long.bitCount(mj) == 1 ? mi & ~shiftWord(mj, offset) : mi;
    };
  }

  /** It checks a tuple by arc consistency on one word per column and marks what it supports. */
  private boolean reviseTupleOnWords(int t) {
    int base = t * arity;
    int[] cols = binaryColumns[t];
    long[] unary = unaryMask[t];
    long[] m = maskWork;
    for (int k : cols) {
      long d = domainMask[k] & unary[k];
      if (d == 0L) {
        return false;
      }
      m[k] = d;
    }
    int[] sources = binarySources[t];
    boolean changed = true;
    while (changed) {
      changed = false;
      for (int i : sources) {
        Restriction r = cells[base + i];
        int j = r.column;
        // x[i] relation x[j] + offset in positions: p relation q + markBase[j] + offset -
        // markBase[i]
        long shift = (long) markBase[j] + r.offset - markBase[i];
        long mi = reviseWord(m[i], r.relation, m[j], shift);
        if (mi == 0L) {
          return false;
        }
        long mj = reviseWord(m[j], converse(r.relation), mi, -shift);
        if (mj == 0L) {
          return false;
        }
        if (mi != m[i] || mj != m[j]) {
          m[i] = mi;
          m[j] = mj;
          changed = true;
        }
      }
    }
    for (int k : cols) {
      long[] mk = marks[k];
      long before = mk[0];
      long after = before | m[k];
      if (after != before) {
        mk[0] = after;
        markCount[k] = Long.bitCount(after);
      }
    }
    return true;
  }

  private boolean marked(int i, int v) {
    int k = v - markBase[i];
    return (marks[i][k >> 6] & 1L << k) != 0L;
  }

  private void mark(int i, int v) {
    int k = v - markBase[i];
    long bit = 1L << k;
    long[] m = marks[i];
    if ((m[k >> 6] & bit) == 0L) {
      m[k >> 6] |= bit;
      markCount[i]++;
    }
  }

  private boolean fullyMarked(int i) {
    return markCount[i] >= markNeed[i];
  }

  /**
   * It marks the values of d between min and max that r accepts; it tells whether there are any.
   */
  private boolean markRange(int i, IntDomain d, Restriction r, long min, long max) {
    long from = Math.max(min, d.min());
    long to = Math.min(max, d.max());
    if (from > to) {
      return false;
    }
    boolean found = false;
    int v = d.contains((int) from) ? (int) from : d.nextValue((int) from);
    while (v <= to) {
      if (r.accepts(v)) {
        found = true;
        mark(i, v);
        if (fullyMarked(i)) {
          return true;
        }
      }
      int next = d.nextValue(v);
      if (next == v) {
        break;
      }
      v = next;
    }
    return found;
  }

  /** The smallest value of d that r accepts, or Long.MAX_VALUE if there is none. */
  private static long firstAccepted(IntDomain d, Restriction r) {
    int v = d.min();
    while (true) {
      if (r.accepts(v)) {
        return v;
      }
      int next = d.nextValue(v);
      if (next == v) {
        return Long.MAX_VALUE;
      }
      v = next;
    }
  }

  /** The largest value of d that r accepts, or Long.MIN_VALUE if there is none. */
  private static long lastAccepted(IntDomain d, Restriction r) {
    int v = d.max();
    while (true) {
      if (r.accepts(v)) {
        return v;
      }
      int previous = d.previousValue(v);
      if (previous == v) {
        return Long.MIN_VALUE;
      }
      v = previous;
    }
  }

  /**
   * It checks a tuple with a single restriction between columns, x[i] relation x[j] + offset, and
   * marks the values it supports in both columns, without building domains.
   */
  private boolean reviseSingleRestriction(int t) {
    int base = t * arity;
    int i = binarySources[t][0];
    Restriction r = cells[base + i];
    int j = r.column;
    Restriction rj = cells[base + j];
    Restriction any = Restriction.any();
    IntDomain di = x[i].dom();
    IntDomain dj = x[j].dom();
    long c = r.offset;
    long minJ = firstAccepted(dj, rj);
    if (minJ == Long.MAX_VALUE) {
      return false;
    }
    long maxJ = lastAccepted(dj, rj);
    long minI = di.min();
    long maxI = di.max();
    switch (r.relation) {
      case LT, LE -> {
        long strict = r.relation == Restriction.Relation.LT ? 1 : 0;
        // x[i] <= x[j] + c - strict
        if (minI > maxJ + c - strict) {
          return false;
        }
        if (!fullyMarked(i)) {
          markRange(i, di, any, Long.MIN_VALUE, maxJ + c - strict);
        }
        if (!fullyMarked(j)) {
          markRange(j, dj, rj, minI - c + strict, Long.MAX_VALUE);
        }
      }
      case GT, GE -> {
        long strict = r.relation == Restriction.Relation.GT ? 1 : 0;
        // x[i] >= x[j] + c + strict
        if (maxI < minJ + c + strict) {
          return false;
        }
        if (!fullyMarked(i)) {
          markRange(i, di, any, minJ + c + strict, Long.MAX_VALUE);
        }
        if (!fullyMarked(j)) {
          markRange(j, dj, rj, Long.MIN_VALUE, maxI - c - strict);
        }
      }
      case EQ -> {
        boolean found = false;
        long from = Math.max(minI, minJ + c);
        long to = Math.min(maxI, maxJ + c);
        if (from > to) {
          return false;
        }
        int v = di.contains((int) from) ? (int) from : di.nextValue((int) from);
        while (v <= to) {
          long w = v - c;
          if (dj.contains((int) w) && rj.accepts((int) w)) {
            if (!found) {
              found = true;
            }
            mark(i, v);
            mark(j, (int) w);
            if (fullyMarked(i) && fullyMarked(j)) {
              break;
            }
          }
          int next = di.nextValue(v);
          if (next == v) {
            break;
          }
          v = next;
        }
        return found;
      }
      case NE -> {
        boolean singleI = minI == maxI;
        boolean singleJ = minJ == maxJ;
        if (singleI && singleJ && minI == minJ + c) {
          return false;
        }
        if (!fullyMarked(i)) {
          if (singleJ) {
            markRange(
                i,
                di,
                Restriction.ne(Math.clamp(minJ + c, Integer.MIN_VALUE, Integer.MAX_VALUE)),
                Long.MIN_VALUE,
                Long.MAX_VALUE);
          } else {
            markRange(i, di, any, Long.MIN_VALUE, Long.MAX_VALUE);
          }
        }
        if (!fullyMarked(j)) {
          if (singleI) {
            long forbidden = minI - c;
            int v = dj.min();
            while (true) {
              if (v != forbidden && rj.accepts(v)) {
                mark(j, v);
              }
              int next = dj.nextValue(v);
              if (next == v) {
                break;
              }
              v = next;
            }
          } else {
            markRange(j, dj, rj, Long.MIN_VALUE, Long.MAX_VALUE);
          }
        }
      }
    }
    return true;
  }

  private boolean reviseTuple(int t) {
    int base = t * arity;
    int[] cols = binaryColumns[t];
    for (int i : cols) {
      IntDomain d = unary(t, i, cells[base + i], x[i].dom());
      if (d.isEmpty()) {
        return false;
      }
      work[i] = d;
    }
    int[] sources = binarySources[t];
    boolean changed = true;
    while (changed) {
      changed = false;
      for (int i : sources) {
        Restriction r = cells[base + i];
        int j = r.column;
        IntDomain di = work[i];
        IntDomain dj = work[j];
        IntDomain ni = revise(di, r.relation, dj, r.offset);
        if (ni.isEmpty()) {
          return false;
        }
        IntDomain nj = revise(dj, converse(r.relation), ni, -(long) r.offset);
        if (nj.isEmpty()) {
          return false;
        }
        if (ni != di) {
          work[i] = ni;
          changed = true;
        }
        if (nj != dj) {
          work[j] = nj;
          changed = true;
        }
      }
    }
    for (int i : cols) {
      if (useMarks) {
        if (!fullyMarked(i)) {
          markRange(i, work[i], Restriction.any(), Long.MIN_VALUE, Long.MAX_VALUE);
        }
      } else {
        binarySupport[i] = binarySupport[i] == null ? work[i] : binarySupport[i].union(work[i]);
      }
    }
    return true;
  }

  private IntDomain unary(int t, int i, Restriction r, IntDomain d) {
    return switch (r.kind) {
      case ANY, COLUMN -> d;
      case EQ -> d.contains(r.value) ? new IntervalDomain(r.value, r.value) : new IntervalDomain();
      case NE -> d.contains(r.value) ? d.subtract(r.value) : d;
      case LE -> atMost(d, r.value);
      case GE -> atLeast(d, r.value);
      case IN -> d.intersect(setDomains[t][i]);
      case NOT_IN -> d.subtract(setDomains[t][i]);
    };
  }

  private static Restriction.Relation converse(Restriction.Relation relation) {
    return switch (relation) {
      case LT -> Restriction.Relation.GT;
      case LE -> Restriction.Relation.GE;
      case EQ -> Restriction.Relation.EQ;
      case NE -> Restriction.Relation.NE;
      case GE -> Restriction.Relation.LE;
      case GT -> Restriction.Relation.LT;
    };
  }

  /** It removes from d the values v without a value w of e such that v relation w + offset. */
  private static IntDomain revise(
      IntDomain d, Restriction.Relation relation, IntDomain e, long offset) {
    return switch (relation) {
      case LT -> atMost(d, e.max() + offset - 1);
      case LE -> atMost(d, e.max() + offset);
      case GT -> atLeast(d, e.min() + offset + 1);
      case GE -> atLeast(d, e.min() + offset);
      case EQ -> {
        IntDomain shifted = shift(e, offset);
        yield shifted.contains(d) ? d : d.intersect(shifted);
      }
      case NE -> {
        if (e.singleton()) {
          long v = e.value() + offset;
          yield v >= d.min() && v <= d.max() && d.contains((int) v) ? d.subtract((int) v) : d;
        }
        yield d;
      }
    };
  }

  private static IntDomain atMost(IntDomain d, long max) {
    if (max >= d.max()) {
      return d;
    }
    if (max < d.min()) {
      return new IntervalDomain();
    }
    return d.intersect(d.min(), (int) max);
  }

  private static IntDomain atLeast(IntDomain d, long min) {
    if (min <= d.min()) {
      return d;
    }
    if (min > d.max()) {
      return new IntervalDomain();
    }
    return d.intersect((int) min, d.max());
  }

  private static IntDomain shift(IntDomain d, long offset) {
    if (offset == 0) {
      return d;
    }
    IntervalDomain result = new IntervalDomain(d.noIntervals() + 1);
    for (IntervalEnumeration e = d.intervalEnumeration(); e.hasMoreElements(); ) {
      Interval in = e.nextElement();
      long lo = Math.max(in.min() + offset, IntDomain.MIN_INT);
      long hi = Math.min(in.max() + offset, IntDomain.MAX_INT);
      if (lo <= hi) {
        result.unionAdapt((int) lo, (int) hi);
      }
    }
    return result;
  }

  /** It removes the values of variable i that no valid tuple supports. */
  private void filterDomain(int i) {

    IntVar xi = x[i];
    int[] l = live[i];
    int size = liveSize(i);
    int[] cMin = classMin[i];
    int[] cMax = classMax[i];
    long[][] sup = supports[i];
    long[] excluded = binaryColumn[i];
    IntDomain extra = null;
    if (excluded != null) {
      if (!intersects(excluded)) {
        excluded = null;
      } else if (!useMarks) {
        extra = binarySupport[i] == null ? new IntervalDomain() : binarySupport[i];
      }
    }
    int s = size;
    int p = 0;
    while (p < s) {
      int c = l[p];
      IntDomain d = xi.dom();
      int lo = cMin[c];
      int hi = cMax[c];
      boolean alive = lo == hi ? d.contains(lo) : d.isIntersecting(lo, hi);
      if (alive && (sup[c] == null || !intersects(i, c, sup[c], excluded))) {
        if (excluded != null && useMarks) {
          removeUnmarked(i, xi, lo, hi);
          alive = xi.dom().isIntersecting(lo, hi);
        } else if (extra == null) {
          removeClass(xi, cMin[c], cMax[c]);
          alive = false;
        } else {
          IntDomain unsupported = d.intersect(cMin[c], cMax[c]).subtract(extra);
          for (int k = 0; k < unsupported.noIntervals(); k++) {
            removeClass(xi, unsupported.leftElement(k), unsupported.rightElement(k));
          }
          alive = xi.dom().isIntersecting(cMin[c], cMax[c]);
        }
      }
      if (alive) {
        p++;
      } else {
        s--;
        l[p] = l[s];
        l[s] = c;
      }
    }
    if (s != size) {
      setLiveSize(i, s);
    }
  }

  /** It removes the values of x[i] between min and max that no tuple marked as supported. */
  private void removeUnmarked(int i, IntVar xi, int min, int max) {
    if (fullyMarked(i)) {
      return;
    }
    IntDomain d = xi.dom();
    int v = Math.max(min, d.min());
    if (!d.contains(v)) {
      v = d.nextValue(v);
    }
    while (v <= max && d.contains(v)) {
      int next = d.nextValue(v);
      if (!marked(i, v)) {
        xi.domain.inComplement(store.level, xi, v);
        d = xi.dom();
      }
      if (next == v) {
        break;
      }
      v = next;
    }
  }

  private void removeClass(IntVar xi, int min, int max) {
    if (min == max) {
      xi.domain.inComplement(store.level, xi, min);
    } else {
      xi.domain.inComplement(store.level, xi, min, max);
    }
  }

  @Override
  public int getDefaultConsistencyPruningEvent() {
    return IntDomain.ANY;
  }

  @Override
  public boolean satisfied() {
    if (!grounded()) {
      return false;
    }
    int[] values = new int[arity];
    for (int i = 0; i < arity; i++) {
      values[i] = x[i].value();
    }
    for (int t = 0; t < tupleCount; t++) {
      if (accepts(cells, t * arity, arity, values)) {
        return true;
      }
    }
    return false;
  }

  /**
   * It checks whether a hybrid tuple accepts a tuple of values.
   *
   * @param tuple the hybrid tuple.
   * @param values the values, one per column.
   * @return true if every restriction of the hybrid tuple holds.
   */
  public static boolean accepts(Restriction[] tuple, int[] values) {
    return accepts(tuple, 0, tuple.length, values);
  }

  private static boolean accepts(Restriction[] cells, int base, int arity, int[] values) {
    for (int i = 0; i < arity; i++) {
      Restriction r = cells[base + i];
      if (r.isBinary() ? !r.accepts(values[i], values[r.column]) : !r.accepts(values[i])) {
        return false;
      }
    }
    return true;
  }

  @Override
  public String toString() {
    StringBuilder s = new StringBuilder(id());
    s.append(" : hybridTable(").append(Arrays.asList(x)).append(", [");
    for (int t = 0; t < tupleCount; t++) {
      s.append(Arrays.toString(Arrays.copyOfRange(cells, t * arity, t * arity + arity)));
      if (t < tupleCount - 1) {
        s.append(", ");
      }
    }
    s.append("])");
    return s.toString();
  }

  @Override
  public HybridTable copy(VarMap map) {
    return new HybridTable(this, map);
  }
}
