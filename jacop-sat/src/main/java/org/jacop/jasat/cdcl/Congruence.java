/*
 * Congruence.java
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

package org.jacop.jasat.cdcl;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

/**
 * Equivalent-literal substitution on the irredundant clauses at level 0. Equivalences come from two
 * sources:
 *
 * <ul>
 *   <li>the strongly connected components of the binary implication graph (Aspvall, Plass and
 *       Tarjan, "A linear-time algorithm for testing the truth of certain quantified boolean
 *       formulas", IPL 1979; Van Gelder, "Toward leaner binary-clause reasoning in a satisfiability
 *       solver", AMAI 2005);
 *   <li>clausal congruence closure (Biere, Fazekas, Fleury and Froleyks, "Clausal Congruence
 *       Closure", SAT 2024): the AND, XOR and ITE gates the {@link GateExtractor} finds are hashed
 *       on their inputs, rewritten to the representatives of the equivalences found so far, and two
 *       gates with the same kind and inputs have equivalent outputs, until a fixpoint.
 * </ul>
 *
 * <p>Each equivalence class keeps one representative literal (a frozen variable if the class has
 * one); every other variable of the class is replaced by it in all clauses and goes on the
 * extension stack (the two binary clauses of its equivalence, as {@link Eliminator#extend} reads
 * them). A frozen variable that is not the representative keeps its occurrences, and its two binary
 * clauses stay in the formula.
 *
 * <p>Every equivalence is written to the proof before it is used: those of the binary graph and of
 * AND gates are RUP; those of XOR and ITE gates are derived by case splits on their inputs, each
 * leaf RUP. Rewritten clauses are RUP from the old clause and the equivalences.
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
final class Congruence {

  // literals visited by the gate extraction in one run
  private static final long EFFORT_LIMIT = 200_000_000L;

  private final int numVars;
  private final boolean[] frozen;
  private final ProofOutput proof;

  private final int[][] clauses;
  private final int numClauses;
  private final int[][] occ;
  private final int[] occSize;

  // union-find over literals: parent[v] is a literal equal to the positive literal of v, 2v at a
  // representative
  private final int[] parent;
  private boolean unsat;
  private int[] units = new int[16];
  private int numUnits;

  // the gates, and per representative variable the gates with an input in its class
  private Node[] gates = new Node[64];
  private int numGates;
  private int[][] users;
  private int[] usersSize;
  private final Map<Key, Node> table = new HashMap<>();
  private int[] queue = new int[64];
  private int queueSize;

  private int[] out;
  private int[][] result;
  private boolean[] substituted;
  private int numSubstituted;
  private int[] stack = new int[0];

  /** Statistics: equivalences found from the binary implication graph. */
  int sccEquivalences;

  /** Statistics: equivalences found by congruence closure on gates. */
  int gateEquivalences;

  /** Statistics: gates extracted, by kind (AND, XOR, ITE). */
  int andGates;

  /** Statistics: XOR gates extracted. */
  int xorGates;

  /** Statistics: ITE gates extracted. */
  int iteGates;

  /** Whether congruence closure on gates runs; the binary implication graph always does. */
  boolean gatesOn = true;

  /**
   * Creates the pass over the given clauses, which must have at least two literals, no duplicate
   * literal, no tautology, and no assigned literal.
   *
   * @param numVars the number of variables
   * @param input the clauses
   * @param numInput how many of them are used
   * @param frozen the variables that must not be replaced
   * @param proof the DRAT output, or null
   */
  Congruence(int numVars, int[][] input, int numInput, boolean[] frozen, ProofOutput proof) {
    this.numVars = numVars;
    this.frozen = frozen;
    this.proof = proof;
    clauses = Arrays.copyOf(input, numInput);
    numClauses = numInput;
    occ = new int[2 * numVars][];
    occSize = new int[2 * numVars];
    for (int i = 0; i < numInput; i++) {
      for (int l : input[i]) {
        occSize[l]++;
      }
    }
    for (int l = 0; l < 2 * numVars; l++) {
      occ[l] = new int[occSize[l]];
      occSize[l] = 0;
    }
    for (int i = 0; i < numInput; i++) {
      for (int l : input[i]) {
        occ[l][occSize[l]++] = i;
      }
    }
    parent = new int[numVars];
    for (int v = 0; v < numVars; v++) {
      parent[v] = 2 * v;
    }
  }

  /**
   * Finds the equivalences and substitutes them.
   *
   * @return false when the formula is unsatisfiable
   */
  boolean run() {
    boolean free = false;
    for (int v = 0; v < numVars && !free; v++) {
      free = !frozen[v] && occSize[2 * v] + occSize[2 * v + 1] > 0;
    }
    if (!free) {
      result = clauses;
      substituted = new boolean[numVars];
      return true; // nothing could be replaced
    }
    binaryComponents();
    if (!unsat && gatesOn) {
      extractGates();
      closure();
    }
    if (!unsat) {
      substitute();
    }
    if (!unsat) {
      propagateUnits();
    }
    return !unsat;
  }

  /** The clauses after substitution, units excluded. */
  int[][] clauses() {
    return result;
  }

  /** The units found. */
  int[] units() {
    return Arrays.copyOf(units, numUnits);
  }

  /** The variables replaced by their representatives. */
  boolean[] substituted() {
    return substituted;
  }

  /** The number of variables replaced. */
  int numSubstituted() {
    return numSubstituted;
  }

  /** The extension stack: each clause with its replaced literal first, then its size. */
  int[] stack() {
    return stack;
  }

  // ------------------------------------------------------------------------------ union-find

  /** The representative of a literal. */
  int find(int lit) {
    int x = lit & ~1;
    int r = x;
    while (parent[r >> 1] != (r & ~1)) {
      r = parent[r >> 1] ^ (r & 1);
    }
    int y = x;
    while (parent[y >> 1] != (y & ~1)) {
      int next = parent[y >> 1] ^ (y & 1);
      parent[y >> 1] = r ^ (y & 1);
      y = next;
    }
    return r ^ (lit & 1);
  }

  /**
   * Records that a and b are equivalent, which the proof already implies by RUP; writes the two
   * binary clauses of the equivalence to the proof.
   */
  private void merge(int a, int b) {
    int ra = find(a);
    int rb = find(b);
    if (ra == rb || unsat) {
      return;
    }
    if (proof != null) {
      proof.add(new int[] {a ^ 1, b}, 0, 2);
      proof.add(new int[] {a, b ^ 1}, 0, 2);
    }
    if (ra == (rb ^ 1)) {
      // a = -a: both a and -a are RUP now
      if (proof != null) {
        proof.add(new int[] {a}, 0, 1);
        proof.add(new int[0], 0, 0);
      }
      unsat = true;
      return;
    }
    // the root: a frozen variable if either is, otherwise the smaller variable
    int va = ra >> 1;
    int vb = rb >> 1;
    boolean keepA = frozen[va] || !frozen[vb] && va < vb;
    if (keepA) {
      parent[vb] = ra ^ (rb & 1);
      requeueUsers(vb, va);
    } else {
      parent[va] = rb ^ (ra & 1);
      requeueUsers(va, vb);
    }
  }

  /** Records a unit the proof already implies by RUP. */
  private void unit(int l) {
    if (proof != null) {
      proof.add(new int[] {l}, 0, 1);
    }
    if (numUnits == units.length) {
      units = Arrays.copyOf(units, 2 * numUnits);
    }
    units[numUnits++] = l;
  }

  // -------------------------------------------------------------- binary implication graph

  /** Tarjan's algorithm, iterative, over the literals with the edges -a -> b of each (a | b). */
  private void binaryComponents() {
    int n = 2 * numVars;
    int[] start = new int[n + 1];
    for (int i = 0; i < numClauses; i++) {
      int[] c = clauses[i];
      if (c.length == 2) {
        start[c[0] ^ 1]++;
        start[c[1] ^ 1]++;
      }
    }
    int sum = 0;
    for (int l = 0; l < n; l++) {
      int k = start[l];
      start[l] = sum;
      sum += k;
    }
    start[n] = sum;
    if (sum == 0) {
      return;
    }
    int[] edges = new int[sum];
    int[] fill = Arrays.copyOf(start, n);
    for (int i = 0; i < numClauses; i++) {
      int[] c = clauses[i];
      if (c.length == 2) {
        edges[fill[c[0] ^ 1]++] = c[1];
        edges[fill[c[1] ^ 1]++] = c[0];
      }
    }
    int[] index = new int[n];
    int[] low = new int[n];
    boolean[] onStack = new boolean[n];
    int[] sccStack = new int[n];
    int sccTop = 0;
    int[] callStack = new int[n];
    int[] edgePos = new int[n];
    int counter = 0;
    for (int root = 0; root < n && !unsat; root++) {
      if (index[root] != 0 || start[root] == start[root + 1]) {
        continue;
      }
      int top = 0;
      callStack[top++] = root;
      index[root] = low[root] = ++counter;
      edgePos[root] = start[root];
      sccStack[sccTop++] = root;
      onStack[root] = true;
      while (top > 0) {
        int u = callStack[top - 1];
        if (edgePos[u] < start[u + 1]) {
          int w = edges[edgePos[u]++];
          if (index[w] == 0) {
            index[w] = low[w] = ++counter;
            edgePos[w] = start[w];
            sccStack[sccTop++] = w;
            onStack[w] = true;
            callStack[top++] = w;
          } else if (onStack[w]) {
            low[u] = Math.min(low[u], index[w]);
          }
          continue;
        }
        top--;
        if (top > 0) {
          int p = callStack[top - 1];
          low[p] = Math.min(low[p], low[u]);
        }
        if (low[u] == index[u]) {
          // the component is the stack down to u; the first literal popped is the last found
          int first = u;
          int w;
          do {
            w = sccStack[--sccTop];
            onStack[w] = false;
            if (w != first && find(first) != find(w)) {
              merge(first, w);
              sccEquivalences++;
            }
          } while (w != u);
        }
      }
    }
  }

  // ----------------------------------------------------------------------------------- gates

  /** A gate: kind, output, its inputs as extracted, and its current key in the table. */
  private static final class Node {
    final int kind;
    final int output;
    final int[] inputs;
    Key key;
    boolean dead;
    boolean queued;

    Node(int kind, int output, int[] inputs) {
      this.kind = kind;
      this.output = output;
      this.inputs = inputs;
    }
  }

  /** The kind and the rewritten inputs of a gate. */
  private static final class Key {
    final int kind;
    final int[] inputs;
    final int hash;

    Key(int kind, int[] inputs) {
      this.kind = kind;
      this.inputs = inputs;
      this.hash = 31 * kind + Arrays.hashCode(inputs);
    }

    @Override
    public boolean equals(Object o) {
      return o instanceof Key k && k.kind == kind && Arrays.equals(k.inputs, inputs);
    }

    @Override
    public int hashCode() {
      return hash;
    }
  }

  private void extractGates() {
    GateExtractor x = new GateExtractor(clauses, occ, occSize, numVars);
    users = new int[numVars][];
    usersSize = new int[numVars];
    for (int v = 0; v < numVars && x.effort < EFFORT_LIMIT; v++) {
      int pos = 2 * v;
      if (occSize[pos] + occSize[pos + 1] < 3) {
        continue;
      }
      for (int s = 0; s < 2; s++) {
        GateExtractor.Gate g = x.findAnd(pos + s);
        if (g != null) {
          addGate(g);
          andGates++;
        }
      }
      GateExtractor.Gate g = x.findXor(pos);
      if (g != null) {
        addGate(g);
        xorGates++;
      }
      g = x.findIte(pos);
      if (g != null) {
        addGate(g);
        iteGates++;
      }
    }
  }

  private void addGate(GateExtractor.Gate g) {
    Node node = new Node(g.kind, g.output, g.inputs);
    if (numGates == gates.length) {
      gates = Arrays.copyOf(gates, 2 * numGates);
    }
    int id = numGates++;
    gates[id] = node;
    for (int l : g.inputs) {
      int v = find(l) >> 1;
      if (users[v] == null) {
        users[v] = new int[2];
      } else if (usersSize[v] == users[v].length) {
        users[v] = Arrays.copyOf(users[v], 2 * usersSize[v]);
      }
      users[v][usersSize[v]++] = id;
    }
    enqueue(id);
  }

  private void enqueue(int id) {
    Node g = gates[id];
    if (g.queued || g.dead) {
      return;
    }
    g.queued = true;
    if (queueSize == queue.length) {
      queue = Arrays.copyOf(queue, 2 * queueSize);
    }
    queue[queueSize++] = id;
  }

  /** After the class of variable child joined the class of root: its users get a new key. */
  private void requeueUsers(int child, int root) {
    if (users == null || users[child] == null) {
      return;
    }
    int[] list = users[child];
    int n = usersSize[child];
    for (int k = 0; k < n; k++) {
      Node g = gates[list[k]];
      if (g.key != null && table.get(g.key) == g) {
        table.remove(g.key);
      }
      g.key = null;
      enqueue(list[k]);
    }
    if (users[root] == null) {
      users[root] = new int[Math.max(2, n)];
    }
    if (usersSize[root] + n > users[root].length) {
      users[root] =
          Arrays.copyOf(users[root], Math.max(usersSize[root] + n, 2 * users[root].length));
    }
    System.arraycopy(list, 0, users[root], usersSize[root], n);
    usersSize[root] += n;
    users[child] = null;
    usersSize[child] = 0;
  }

  /** Hashes the queued gates until no two have the same key. */
  private void closure() {
    while (queueSize > 0 && !unsat) {
      int id = queue[--queueSize];
      Node g = gates[id];
      g.queued = false;
      if (g.dead) {
        continue;
      }
      switch (g.kind) {
        case GateExtractor.AND -> hashAnd(g);
        case GateExtractor.XOR -> hashXor(g);
        default -> hashIte(g);
      }
    }
  }

  private void hashAnd(Node g) {
    int o = find(g.output);
    int[] in = new int[g.inputs.length];
    for (int i = 0; i < in.length; i++) {
      in[i] = find(g.inputs[i]);
    }
    Arrays.sort(in);
    int n = 0;
    for (int i = 0; i < in.length; i++) {
      if (n > 0 && in[n - 1] == in[i]) {
        continue;
      }
      if (n > 0 && in[n - 1] == (in[i] ^ 1)) {
        // o = a & -a: o is false, RUP through the gate's binary clauses
        g.dead = true;
        unit(g.output ^ 1);
        return;
      }
      in[n++] = in[i];
    }
    for (int i = 0; i < n; i++) {
      if (in[i] >> 1 == o >> 1) {
        g.dead = true; // the output is its own input: no equivalence to read
        return;
      }
    }
    if (n == 1) {
      g.dead = true; // o = a, both binary clauses RUP through the gate
      merge(g.output, in[0]);
      gateEquivalences++;
      return;
    }
    lookup(g, new Key(GateExtractor.AND, Arrays.copyOf(in, n)), o);
  }

  private void hashXor(Node g) {
    int o = find(g.output);
    int[] in = new int[g.inputs.length];
    for (int i = 0; i < in.length; i++) {
      int r = find(g.inputs[i]);
      o ^= r & 1; // a negated input flips the output
      in[i] = r & ~1;
    }
    Arrays.sort(in);
    int n = 0;
    for (int i = 0; i < in.length; i++) {
      if (n > 0 && in[n - 1] == in[i]) {
        n--; // x ^ x = 0
        continue;
      }
      in[n++] = in[i];
    }
    for (int i = 0; i < n; i++) {
      if (in[i] == (o & ~1)) {
        g.dead = true;
        return;
      }
    }
    if (n == 0) {
      g.dead = true; // o = 0
      byCases(new int[] {o ^ 1}, g, null);
      unit(o ^ 1);
      return;
    }
    if (n == 1) {
      g.dead = true; // o = a
      byCases(new int[] {o ^ 1, in[0]}, g, null);
      byCases(new int[] {o, in[0] ^ 1}, g, null);
      merge(o, in[0]);
      gateEquivalences++;
      return;
    }
    lookup(g, new Key(GateExtractor.XOR, Arrays.copyOf(in, n)), o);
  }

  private void hashIte(Node g) {
    int o = find(g.output);
    int c = find(g.inputs[0]);
    int t = find(g.inputs[1]);
    int e = find(g.inputs[2]);
    if ((c & 1) != 0) {
      c ^= 1;
      int s = t;
      t = e;
      e = s;
    }
    if (t == e) {
      g.dead = true; // o = c ? t : t = t
      byCases(new int[] {o ^ 1, t}, g, null);
      byCases(new int[] {o, t ^ 1}, g, null);
      merge(o, t);
      gateEquivalences++;
      return;
    }
    int cv = c >> 1;
    if (t >> 1 == e >> 1
        || t >> 1 == cv
        || e >> 1 == cv
        || o >> 1 == cv
        || o >> 1 == t >> 1
        || o >> 1 == e >> 1) {
      g.dead = true; // degenerate: an XOR or a smaller gate, not handled here
      return;
    }
    if ((t & 1) != 0) {
      // o = c ? -t' : e  is  -o = c ? t' : -e
      o ^= 1;
      t ^= 1;
      e ^= 1;
    }
    lookup(g, new Key(GateExtractor.ITE, new int[] {c, t, e}), o);
  }

  /** Puts g with output o in the table, or merges o with the output of the gate with its key. */
  private void lookup(Node g, Key key, int o) {
    Node h = table.get(key);
    if (h == null || h.dead) {
      g.key = key;
      table.put(key, g);
      return;
    }
    // h has the same key: its normalised output is o2
    int o2 = normalisedOutput(h);
    g.dead = true;
    if (find(o) == find(o2)) {
      return;
    }
    if (g.kind != GateExtractor.AND) {
      byCases(new int[] {o ^ 1, o2}, g, h);
      byCases(new int[] {o, o2 ^ 1}, g, h);
    }
    merge(o, o2);
    gateEquivalences++;
  }

  // the output of a gate in the table, normalised as its key was
  private int normalisedOutput(Node h) {
    int o = find(h.output);
    if (h.kind == GateExtractor.XOR) {
      for (int l : h.inputs) {
        o ^= find(l) & 1;
      }
    } else if (h.kind == GateExtractor.ITE) {
      int c = find(h.inputs[0]);
      int t = find((c & 1) != 0 ? h.inputs[2] : h.inputs[1]);
      if ((t & 1) != 0) {
        o ^= 1;
      }
    }
    return o;
  }

  /**
   * Writes the clause target to the proof by case splits on the input variables of g and h (one per
   * equivalence class): every full split is RUP, since with all inputs assigned the gates' clauses
   * fix both outputs.
   */
  private void byCases(int[] target, Node g, Node h) {
    if (proof == null) {
      return;
    }
    int[] split = new int[g.inputs.length + (h == null ? 0 : h.inputs.length)];
    int n = 0;
    for (Node x : new Node[] {g, h}) {
      if (x == null) {
        continue;
      }
      int[] in = x.kind == GateExtractor.ITE ? new int[] {x.inputs[0]} : x.inputs;
      for (int l : in) {
        int r = find(l) >> 1;
        boolean seen = false;
        for (int k = 0; k < n && !seen; k++) {
          seen = find(split[k]) >> 1 == r;
        }
        if (!seen) {
          split[n++] = l & ~1;
        }
      }
    }
    int[] clause = Arrays.copyOf(target, target.length + n);
    derive(clause, target.length, split, 0, n);
  }

  // derives clause[0..len) with the split literals from position depth on still to be resolved
  private void derive(int[] clause, int len, int[] split, int depth, int n) {
    if (depth < n) {
      clause[len] = split[depth];
      derive(clause, len + 1, split, depth + 1, n);
      clause[len] = split[depth] ^ 1;
      derive(clause, len + 1, split, depth + 1, n);
    }
    proof.add(clause, 0, len);
    if (depth < n) {
      // the two clauses with the next split literal are resolved; they are not needed again
      clause[len] = split[depth];
      proof.delete(clause, 0, len + 1);
      clause[len] = split[depth] ^ 1;
      proof.delete(clause, 0, len + 1);
    }
  }

  // ----------------------------------------------------------------------------- substitution

  /** Replaces every literal by its representative; deletes tautologies and old clauses. */
  private void substitute() {
    substituted = new boolean[numVars];
    out = new int[2 * numVars];
    for (int l = 0; l < 2 * numVars; l++) {
      int r = find(l);
      out[l] = frozen[l >> 1] ? l : r;
    }
    int[] ext = new int[64];
    int extSize = 0;
    for (int v = 0; v < numVars; v++) {
      int r = find(2 * v);
      if (r == 2 * v) {
        continue;
      }
      if (frozen[v]) {
        continue;
      }
      substituted[v] = true;
      numSubstituted++;
      if (extSize + 6 > ext.length) {
        ext = Arrays.copyOf(ext, 2 * ext.length);
      }
      // v | -r with v first, then -v | r with -v first: extend sets v to the value of r
      ext[extSize++] = 2 * v;
      ext[extSize++] = r ^ 1;
      ext[extSize++] = 2;
      ext[extSize++] = 2 * v + 1;
      ext[extSize++] = r;
      ext[extSize++] = 2;
    }
    stack = Arrays.copyOf(ext, extSize);
    int[][] res = new int[numClauses][];
    int n = 0;
    int[] mark = new int[2 * numVars];
    int stamp = 0;
    for (int i = 0; i < numClauses; i++) {
      int[] c = clauses[i];
      boolean changed = false;
      for (int l : c) {
        changed |= out[l] != l;
      }
      if (!changed) {
        res[n++] = c;
        continue;
      }
      stamp++;
      int[] d = new int[c.length];
      int k = 0;
      boolean tautology = false;
      for (int l : c) {
        int m = out[l];
        if (mark[m ^ 1] == stamp) {
          tautology = true;
          break;
        }
        if (mark[m] != stamp) {
          mark[m] = stamp;
          d[k++] = m;
        }
      }
      if (!tautology) {
        if (proof != null) {
          proof.add(d, 0, k);
        }
        if (k == 1) {
          if (numUnits == units.length) {
            units = Arrays.copyOf(units, 2 * numUnits);
          }
          units[numUnits++] = d[0];
        } else {
          res[n++] = Arrays.copyOf(d, k);
        }
      }
      if (proof != null) {
        proof.delete(c, 0, c.length);
      }
    }
    result = Arrays.copyOf(res, n);
  }

  /** Propagates the units over the result: removes satisfied clauses and false literals. */
  private void propagateUnits() {
    if (numUnits == 0) {
      return;
    }
    byte[] value = new byte[2 * numVars];
    for (int i = 0; i < numUnits; i++) {
      int l = out[units[i]];
      if (l != units[i] && proof != null) {
        proof.add(new int[] {l}, 0, 1);
      }
      units[i] = l;
    }
    int head = 0;
    int[][] res = result;
    boolean changed = true;
    while (changed && !unsat) {
      changed = false;
      for (; head < numUnits && !unsat; head++) {
        int l = units[head];
        if (value[l] < 0) {
          if (proof != null) {
            proof.add(new int[0], 0, 0);
          }
          unsat = true;
        } else if (value[l] == 0) {
          value[l] = 1;
          value[l ^ 1] = -1;
        }
      }
      for (int i = 0; i < res.length && !unsat; i++) {
        int[] c = res[i];
        if (c == null) {
          continue;
        }
        int k = 0;
        boolean sat = false;
        for (int l : c) {
          sat |= value[l] > 0;
          if (value[l] == 0) {
            k++;
          }
        }
        if (!sat && k == c.length) {
          continue;
        }
        changed = true;
        res[i] = null;
        if (proof != null) {
          if (!sat) {
            int[] d = new int[k];
            int j = 0;
            for (int l : c) {
              if (value[l] == 0) {
                d[j++] = l;
              }
            }
            proof.add(d, 0, k);
            proof.delete(c, 0, c.length);
            if (k >= 2) {
              res[i] = d;
            }
          } else {
            proof.delete(c, 0, c.length);
          }
        } else if (!sat) {
          int[] d = new int[k];
          int j = 0;
          for (int l : c) {
            if (value[l] == 0) {
              d[j++] = l;
            }
          }
          if (k >= 2) {
            res[i] = d;
          }
        }
        if (!sat && k == 0) {
          if (proof != null) {
            proof.add(new int[0], 0, 0);
          }
          unsat = true;
        } else if (!sat && k == 1) {
          int u = c[0];
          for (int l : c) {
            if (value[l] == 0) {
              u = l;
            }
          }
          if (numUnits == units.length) {
            units = Arrays.copyOf(units, 2 * numUnits);
          }
          units[numUnits++] = u;
        }
      }
    }
    int n = 0;
    for (int[] c : res) {
      if (c != null) {
        res[n++] = c;
      }
    }
    result = Arrays.copyOf(res, n);
    // the units' variables leave the formula: keep only units that are not already in it
    int[] kept = new int[numUnits];
    int k = 0;
    for (int i = 0; i < numUnits; i++) {
      int l = units[i];
      if (value[l] > 0) {
        value[l] = 2; // listed once
        kept[k++] = l;
      }
    }
    units = kept;
    numUnits = k;
  }
}
