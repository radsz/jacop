/*
 * DomainTrail.java
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

package org.jacop.core;

import java.util.Arrays;

/**
 * One trail shared by the domains of a store that are changed in place ({@link LazyBitSetDomain}).
 * A domain pushes an entry before its first change at a level, and the store pops the entries of a
 * level when it removes the level, giving each entry back to its domain.
 *
 * <p>Keeping the entries of all domains in one array, in the order they were made, makes saving and
 * restoring a sequential walk over memory, where a trail per domain would touch a separate array
 * per changed variable.
 *
 * <p>Entries take only the space their kind needs. They are kept in two streams: an int stream and
 * an object stream. A word entry, the most frequent kind, saves one long word of a domain and is
 * five ints (the old stamp of the word, the word as two ints, the level and the word index) and one
 * object (the domain): 24 bytes. Any other entry is a kind chosen by the domain with a number of
 * ints and objects: its ints are the position of its objects, its own ints, the level and a tag
 * holding the kind and the two counts; its objects are the domain and its own objects. Each entry
 * ends with its level and its tag, so the trail is popped from its end without an index of the
 * entries.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 5.0
 */
public final class DomainTrail {

  /** A domain whose state is saved on a {@link DomainTrail}. */
  interface Entry {

    /**
     * Restores a word saved by {@link DomainTrail#pushWord}, whose entry is being popped.
     *
     * @param word the index of the word.
     * @param stamp the int saved with the word.
     * @param value the saved word.
     */
    void undoWord(int word, int stamp, long value);

    /**
     * Restores the state saved in an entry pushed by {@link DomainTrail#push}, which is being
     * popped.
     *
     * @param trail the trail.
     * @param entry the entry.
     * @param kind the kind of the entry.
     */
    void undo(DomainTrail trail, int entry, int kind);
  }

  /** The number of ints of a word entry. */
  static final int WORD_INTS = 5;

  /** The ints an entry other than a word entry adds to its own: objects position, level, tag. */
  static final int EXTRA_INTS = 3;

  /** The largest number of ints or objects of an entry, other than the domain. */
  static final int MAX_FIELDS = 0xFF;

  /** The log of the length of the first segment of each stream. */
  private static final int FIRST_SHIFT = 10;

  /** The length of the first segment of each stream; segment s has length FIRST << s. */
  private static final int FIRST = 1 << FIRST_SHIFT;

  /**
   * The number of segments of each stream: the last one has 2^30 elements, and the position of
   * every element of a stream still fits an int.
   */
  private static final int SEGMENTS = 21;

  private static final int[] NO_INTS = {};

  private static final Object[] NO_OBJECTS = {};

  /**
   * The int stream, in segments of doubling length, so the trail grows without copying: on a deep
   * search the trail can hold millions of entries, and copying them into ever larger arrays touches
   * twice the memory they need. An entry never spans two segments; the end of a segment that an
   * entry does not fit is left unused.
   */
  private final int[][] ints = new int[SEGMENTS][];

  /** The length used in each int segment below the current one. */
  private final int[] intsUsed = new int[SEGMENTS];

  /** The object stream, kept as the int stream. */
  private final Object[][] objects = new Object[SEGMENTS][];

  /** The length used in each object segment below the current one. */
  private final int[] objectsUsed = new int[SEGMENTS];

  /** The current int segment, -1 before the first push. */
  private int intSegment = -1;

  /** The current int segment, ints[intSegment]. */
  private int[] intCurrent = NO_INTS;

  /** The length used in the current int segment. */
  private int intTop;

  /** The position in the int stream of the first element of the current int segment. */
  private int intBase;

  private int objectSegment = -1;

  private Object[] objectCurrent = NO_OBJECTS;

  private int objectTop;

  private int objectBase;

  /**
   * Pushes a word entry, which saves one long of a domain with an int.
   *
   * @param domain the domain the entry belongs to.
   * @param word the index of the word, at least 0.
   * @param level the level the entry belongs to.
   * @param stamp the int saved with the word.
   * @param value the saved word.
   */
  void pushWord(Entry domain, int word, int level, int stamp, long value) {
    int[] in = intCurrent;
    int p = intTop;
    if (p + WORD_INTS > in.length) {
      in = nextIntSegment();
      p = 0;
    }
    in[p] = stamp;
    in[p + 1] = (int) value;
    in[p + 2] = (int) (value >>> 32);
    in[p + 3] = level;
    in[p + 4] = word;
    intTop = p + WORD_INTS;
    Object[] ob = objectCurrent;
    int q = objectTop;
    if (q == ob.length) {
      ob = nextObjectSegment();
      q = 0;
    }
    ob[q] = domain;
    objectTop = q + 1;
  }

  /**
   * Pushes an entry of a kind chosen by the domain; the caller fills in its ints and objects.
   *
   * @param domain the domain the entry belongs to.
   * @param kind the kind of the entry, from -32768 to -1, given back to the domain.
   * @param level the level the entry belongs to.
   * @param intCount the number of ints of the entry, at most {@link #MAX_FIELDS}.
   * @param objectCount the number of objects of the entry besides the domain, at most {@link
   *     #MAX_FIELDS}.
   * @return the entry, its position in the int stream.
   */
  int push(Entry domain, int kind, int level, int intCount, int objectCount) {
    int length = intCount + EXTRA_INTS;
    int[] in = intCurrent;
    int p = intTop;
    if (p + length > in.length) {
      in = nextIntSegment();
      p = 0;
    }
    Object[] ob = objectCurrent;
    int q = objectTop;
    if (q + objectCount + 1 > ob.length) {
      ob = nextObjectSegment();
      q = 0;
    }
    in[p] = objectBase + q;
    in[p + length - 2] = level;
    in[p + length - 1] = kind << 16 | intCount << 8 | objectCount;
    ob[q] = domain;
    intTop = p + length;
    objectTop = q + objectCount + 1;
    return intBase + p;
  }

  private int[] nextIntSegment() {
    if (intSegment >= 0) {
      intsUsed[intSegment] = intTop;
    }
    int s = ++intSegment;
    if (s >= SEGMENTS) {
      intSegment--;
      throw new IllegalStateException("Trail too large");
    }
    if (ints[s] == null) {
      ints[s] = new int[FIRST << s];
    }
    intCurrent = ints[s];
    intTop = 0;
    intBase = start(s);
    return intCurrent;
  }

  private Object[] nextObjectSegment() {
    if (objectSegment >= 0) {
      objectsUsed[objectSegment] = objectTop;
    }
    int s = ++objectSegment;
    if (s >= SEGMENTS) {
      objectSegment--;
      throw new IllegalStateException("Trail too large");
    }
    if (objects[s] == null) {
      objects[s] = new Object[FIRST << s];
    }
    objectCurrent = objects[s];
    objectTop = 0;
    objectBase = start(s);
    return objectCurrent;
  }

  /** The position in a stream of the first element of segment s. */
  private static int start(int s) {
    return (FIRST << s) - FIRST;
  }

  /**
   * The segment of a position in a stream: segment s holds positions FIRST * (2^s - 1) to FIRST *
   * (2^(s+1) - 1) - 1.
   */
  private static int segment(int position) {
    return 31 - FIRST_SHIFT - Integer.numberOfLeadingZeros(position + FIRST);
  }

  /**
   * Returns an int of an entry pushed by {@link #push}.
   *
   * @param entry the entry.
   * @param k the index of the int, below the int count of the entry.
   * @return the int.
   */
  int getInt(int entry, int k) {
    int i = entry - intBase;
    if (i >= 0) {
      // the entries just pushed and those being popped are in the current segment
      return intCurrent[i + 1 + k];
    }
    int s = segment(entry);
    return ints[s][entry - start(s) + 1 + k];
  }

  /**
   * Sets an int of an entry pushed by {@link #push}.
   *
   * @param entry the entry.
   * @param k the index of the int, below the int count of the entry.
   * @param value the int.
   */
  void setInt(int entry, int k, int value) {
    int i = entry - intBase;
    if (i >= 0) {
      intCurrent[i + 1 + k] = value;
      return;
    }
    int s = segment(entry);
    ints[s][entry - start(s) + 1 + k] = value;
  }

  /**
   * Returns an object of an entry pushed by {@link #push}.
   *
   * @param entry the entry.
   * @param k the index of the object, 0 for the domain and 1 to the object count for the others.
   * @return the object.
   */
  Object getObject(int entry, int k) {
    int position = getInt(entry, -1) + k;
    int i = position - objectBase;
    if (i >= 0) {
      return objectCurrent[i];
    }
    int t = segment(position);
    return objects[t][position - start(t)];
  }

  /**
   * Sets an object of an entry pushed by {@link #push}.
   *
   * @param entry the entry.
   * @param k the index of the object, from 1 to the object count.
   * @param value the object.
   */
  void setObject(int entry, int k, Object value) {
    int position = getInt(entry, -1) + k;
    int i = position - objectBase;
    if (i >= 0) {
      objectCurrent[i] = value;
      return;
    }
    int t = segment(position);
    objects[t][position - start(t)] = value;
  }

  /**
   * Pops the entries of the given level and of the levels above it, newest first.
   *
   * @param level the lowest level removed.
   */
  void removeLevel(int level) {
    // kept small so that it inlines into the store's backtracking, which most stores do without
    // ever pushing an entry
    if (intTop != 0 || intSegment > 0) {
      pop(level);
    }
  }

  private void pop(int level) {
    while (true) {
      if (intTop == 0) {
        if (intSegment <= 0) {
          return;
        }
        previousIntSegment();
      }
      int[] in = intCurrent;
      int p = intTop;
      if (in[p - 2] < level) {
        return;
      }
      if (objectTop == 0) {
        previousObjectSegment();
      }
      Object[] ob = objectCurrent;
      int q = objectTop;
      int tag = in[p - 1];
      if (tag >= 0) {
        intTop = p - WORD_INTS;
        objectTop = q - 1;
        Entry domain = (Entry) ob[q - 1];
        ob[q - 1] = null;
        domain.undoWord(tag, in[p - 5], word(in, p));
      } else {
        int start = p - ((tag >>> 8) & 0xFF) - EXTRA_INTS;
        int first = q - (tag & 0xFF) - 1;
        intTop = start;
        objectTop = first;
        ((Entry) ob[first]).undo(this, intBase + start, tag >> 16);
        Arrays.fill(ob, first, q, null);
      }
    }
  }

  /** The word of the word entry ending at position p of the int segment in. */
  private static long word(int[] in, int p) {
    return (long) in[p - 3] << 32 | (in[p - 4] & 0xFFFFFFFFL);
  }

  private void previousIntSegment() {
    int s = --intSegment;
    intCurrent = ints[s];
    intTop = intsUsed[s];
    intBase = start(s);
  }

  private void previousObjectSegment() {
    int s = --objectSegment;
    objectCurrent = objects[s];
    objectTop = objectsUsed[s];
    objectBase = start(s);
  }

  /**
   * Writes into words the words saved by the word entries of a domain pushed after a given entry,
   * the oldest last, so each word ends as it was when that entry was pushed.
   *
   * @param domain the domain.
   * @param after the entry, pushed by {@link #push}.
   * @param words the words of the domain, indexed by word.
   */
  void savedWords(Entry domain, int after, long[] words) {
    int s = intSegment;
    int p = intTop;
    int t = objectSegment;
    int q = objectTop;
    while (true) {
      if (p == 0) {
        if (s <= 0) {
          return;
        }
        s--;
        p = intsUsed[s];
      }
      if (q == 0) {
        t--;
        q = objectsUsed[t];
      }
      int[] in = s == intSegment ? intCurrent : ints[s];
      int tag = in[p - 1];
      int start;
      if (tag >= 0) {
        start = p - WORD_INTS;
        if (objects[t][q - 1] == domain) {
          words[tag] = word(in, p);
        }
        q--;
      } else {
        start = p - ((tag >>> 8) & 0xFF) - EXTRA_INTS;
        q -= (tag & 0xFF) + 1;
      }
      if (start(s) + start <= after) {
        return;
      }
      p = start;
    }
  }

  /**
   * Returns whether the trail has no entries.
   *
   * @return true if no entry is on the trail.
   */
  boolean isEmpty() {
    return intTop == 0 && intSegment <= 0;
  }
}
