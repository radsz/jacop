/*
 * SatTranslation.java
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

package org.jacop.satwrapper;

import java.util.ArrayList;
import java.util.List;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * SatTranslation defines SAT clauses for typical logical constraints.
 *
 * @author Krzysztof Kuchcinski
 * @version 5.0
 */
public class SatTranslation {

  final SatWrapper clauses;
  final Store store;
  public boolean debug;
  long numberClauses;

  private int[] toBoolVarArray(List<IntVar> vars) {
    int[] result = new int[vars.size()];
    for (int i = 0; i < vars.size(); i++) {
      result[i] = clauses.cpVarToBoolVar(vars.get(i), 1, true);
    }
    return result;
  }

  /**
   * Constructs a SAT translation instance for the given store.
   *
   * @param store the constraint store
   */
  public SatTranslation(Store store) {
    this.store = store;
    clauses = new SatWrapper();

    numberClauses = 0;
    clauses.empty = true;
  }

  /**
   * Generates a SAT clause from positive and negative literals.
   *
   * @param a1 array of variables for positive literals
   * @param a2 array of variables for negative literals
   */
  public void generateClause(IntVar[] a1, IntVar[] a2) {

    List<IntVar> a1reduced = new ArrayList<>();
    for (IntVar v : a1) {
      if (v.min() == 1) {
        return;
      } else if (v.max() != 0) {
        a1reduced.add(v);
      }
    }
    List<IntVar> a2reduced = new ArrayList<>();
    for (IntVar intVar : a2) {
      if (intVar.max() == 0) {
        return;
      } else if (intVar.min() != 1) {
        a2reduced.add(intVar);
      }
    }
    if (a1reduced.isEmpty() && a2reduced.isEmpty()) {
      throw Store.failException;
    }
    if (debug) {
      IO.println("% generate clause, positive: " + a1reduced + ", negative: " + a2reduced);
    }

    for (IntVar v : a1reduced) {
      clauses.register(v);
    }
    for (IntVar v : a2reduced) {
      clauses.register(v);
    }

    int[] a1IsOne = toBoolVarArray(a1reduced);
    int[] a2IsOne = toBoolVarArray(a2reduced);

    int[] clause = new int[a1reduced.size() + a2reduced.size()];
    System.arraycopy(a1IsOne, 0, clause, 0, a1reduced.size());
    for (int i = 0; i < a2reduced.size(); i++) {
      clause[a1reduced.size() + i] = -a2IsOne[i];
    }
    clauses.addModelClause(clause);

    numberClauses++;
  }

  /**
   * Generates a reified clause expressing {@code ((a1 \/ ... \/ an) \/ (-b1 \/ ... \/ -bn)) <=> r}.
   *
   * @param a array of variables for positive literals
   * @param b array of variables for negative literals
   * @param r reification variable
   */
  public void generateClauseReif(IntVar[] a, IntVar[] b, IntVar r) {
    // ((a1 \/ ...\/ an) \/ (-b1 \/ ... \/ -bn)) <=> r
    // a1 \/ ...\/ an \/ -b1 \/ ... \/ -bn \/ -r
    // for all i: -ai \/ r
    // for all i:  bi \/ r
    IntVar[] bs = new IntVar[b.length + 1];
    System.arraycopy(b, 0, bs, 0, b.length);
    bs[b.length] = r;
    generateClause(a, bs);
    for (IntVar v : a) {
      generateClause(new IntVar[] {r}, new IntVar[] {v});
    }
    for (IntVar intVar : b) {
      generateClause(new IntVar[] {intVar, r}, new IntVar[] {});
    }
  }

  /**
   * Generates clauses for OR constraint: {@code c <=> (a1 \/ a2 \/ ... \/ an)}.
   *
   * @param a array of input variables
   * @param c output variable
   */
  public void generateOr(IntVar[] a, IntVar c) {

    // (a1 \/ a2 \/ ... \/ an \/ -c)
    // /\
    // for all i: (-ai \/ c)
    for (IntVar v : a) {
      if (v.min() == 1) {
        c.domain.in(store.level, c, 1, 1);
        return;
      }
    }

    generateClause(a, new IntVar[] {c});
    for (IntVar intVar : a) {
      generateClause(new IntVar[] {c}, new IntVar[] {intVar});
    }
  }

  /**
   * Generates clauses for AND constraint: {@code c <=> (a1 /\ a2 /\ ... /\ an)}.
   *
   * @param a array of input variables
   * @param c output variable
   */
  public void generateAnd(IntVar[] a, IntVar c) {

    // -a1 \/ -a2 \/ ... \/ c
    // /\
    // for all i: ai \/ -c
    for (IntVar v : a) {
      if (v.max() == 0) {
        c.domain.in(store.level, c, 0, 0);
        return;
      }
    }

    generateClause(new IntVar[] {c}, a);
    for (IntVar intVar : a) {
      generateClause(new IntVar[] {intVar}, new IntVar[] {c});
    }
  }

  /**
   * To represent XOR function in CNF one needs to have 2^{n-1} clauses, where n is the size of your
   * XOR function :( Our method cuts list to 3 or 2 element parts, generates XOR for them and
   * composesd them back to the original XOR. Further improvements possible, if using 4-7
   * decompositions.
   *
   * @param a parameters to be xor'ed
   * @param c result
   */
  public void generateXor(IntVar[] a, IntVar c) {

    if (a.length == 3) {
      generateXor(a[0], a[1], a[2], c);
    } else if (a.length == 2) {
      generateXor(a[0], a[1], c);
    } else if (a.length == 1) {
      // this case should not normally happen;
      // the only case if the user specified this case
      generateEq(a[0], c);
    } else { // must be a.length > 3
      IntVar[] as = new IntVar[a.length - 2];
      BooleanVar t = new BooleanVar(store);
      System.arraycopy(a, 3, as, 0, a.length - 3);
      as[as.length - 1] = t;
      generateXor(a[0], a[1], a[2], t);
      generateXor(as, c);
    }
  }

  /**
   * Generates clauses for XOR constraint with two inputs: {@code c <=> (a xor b)}.
   *
   * @param a first input variable
   * @param b second input variable
   * @param c output variable
   */
  public void generateXor(IntVar a, IntVar b, IntVar c) {
    // (a xor b) <=> c
    generateNeqReif(a, b, c);
  }

  /**
   * Generates clauses for XOR constraint with three inputs: {@code d <=> (a xor b xor c)}.
   *
   * @param a first input variable
   * @param b second input variable
   * @param c third input variable
   * @param d output variable
   */
  public void generateXor(IntVar a, IntVar b, IntVar c, IntVar d) {
    // (a xor b xor c) <=> d
    generateClause(new IntVar[] {a}, new IntVar[] {b, c, d});
    generateClause(new IntVar[] {b}, new IntVar[] {a, c, d});
    generateClause(new IntVar[] {c}, new IntVar[] {a, b, d});
    generateClause(new IntVar[] {d}, new IntVar[] {a, b, c});

    generateClause(new IntVar[] {b, c, d}, new IntVar[] {a});
    generateClause(new IntVar[] {a, c, d}, new IntVar[] {b});
    generateClause(new IntVar[] {a, b, d}, new IntVar[] {c});
    generateClause(new IntVar[] {a, b, c}, new IntVar[] {d});
  }

  /**
   * Generates clauses for equality constraint: a = b.
   *
   * @param a first variable
   * @param b second variable
   */
  public void generateEq(IntVar a, IntVar b) {
    // a = b
    // ===========
    // (-a \/ b) /\ ( a \/ -b)
    generateClause(new IntVar[] {b}, new IntVar[] {a});
    generateClause(new IntVar[] {a}, new IntVar[] {b});
  }

  /**
   * Generates clauses for less-than-or-equal constraint: {@code a <= b}.
   *
   * @param a first variable
   * @param b second variable
   */
  public void generateLe(IntVar a, IntVar b) {
    // a =< b
    // ===========
    // -a \/ b
    generateClause(new IntVar[] {b}, new IntVar[] {a});
  }

  /**
   * Generates clauses for less-than constraint: {@code a < b}.
   *
   * @param a first variable
   * @param b second variable
   */
  public void generateLt(IntVar a, IntVar b) {
    // a < b
    // ===========
    // -a /\ b
    generateClause(new IntVar[] {}, new IntVar[] {a});
    generateClause(new IntVar[] {b}, new IntVar[] {});
  }

  /**
   * Generates clauses for reified equality constraint: {@code c <=> (a = b)}.
   *
   * @param a first variable
   * @param b second variable
   * @param c reification variable
   */
  public void generateEqReif(IntVar a, IntVar b, IntVar c) {
    // a = b <=> c
    // ===========
    // (-a \/ b \/ -c) /\
    // (a \/ -b \/ -c) /\
    // (a \/ b \/ c) /\
    // (-a \/ -b \/ c)

    generateClause(new IntVar[] {b}, new IntVar[] {a, c});
    generateClause(new IntVar[] {a}, new IntVar[] {b, c});
    generateClause(new IntVar[] {a, b, c}, new IntVar[] {});
    generateClause(new IntVar[] {c}, new IntVar[] {a, b});
  }

  /**
   * Generates clauses for reified inequality constraint: {@code c <=> (a != b)}.
   *
   * @param a first variable
   * @param b second variable
   * @param c reification variable
   */
  public void generateNeqReif(IntVar a, IntVar b, IntVar c) {
    // a != b <=> c
    // ===========
    // (-a \/ b \/ c) /\
    // (a \/ -b \/ c) /\
    // (a \/ b \/ -c) /\
    // (-a \/ -b \/ -c)

    generateClause(new IntVar[] {b, c}, new IntVar[] {a});
    generateClause(new IntVar[] {a, c}, new IntVar[] {b});
    generateClause(new IntVar[] {a, b}, new IntVar[] {c});
    generateClause(new IntVar[] {}, new IntVar[] {a, b, c});
  }

  /**
   * Generates clauses for reified less-than-or-equal constraint: {@code c <=> (a <= b)}.
   *
   * @param a first variable
   * @param b second variable
   * @param c reification variable
   */
  public void generateLeReif(IntVar a, IntVar b, IntVar c) {
    // a =< b <=> c
    // ===========
    // (-a \/ b \/ -c) /\ (a \/ c) /\ (-b \/ c)
    generateClause(new IntVar[] {b}, new IntVar[] {a, c});
    generateClause(new IntVar[] {a, c}, new IntVar[] {});
    generateClause(new IntVar[] {c}, new IntVar[] {b});
  }

  /**
   * Generates clauses for reified less-than constraint: {@code c <=> (a < b)}.
   *
   * @param a first variable
   * @param b second variable
   * @param c reification variable
   */
  public void generateLtReif(IntVar a, IntVar b, IntVar c) {
    // a < b <=> c
    // ===========
    // (a \/ -b \/ c) /\ (-a \/ -c) /\ (b \/ -c)
    generateClause(new IntVar[] {a, c}, new IntVar[] {b});
    generateClause(new IntVar[] {}, new IntVar[] {a, c});
    generateClause(new IntVar[] {b}, new IntVar[] {c});
  }

  /**
   * Generates clauses for NOT constraint: {@code b <=> -a}.
   *
   * @param a input variable
   * @param b output variable
   */
  public void generateNot(IntVar a, IntVar b) {
    // -a = b
    // ===========
    // (a \/ b) /\
    // (-a \/ -b)

    generateClause(new IntVar[] {a, b}, new IntVar[] {});
    generateClause(new IntVar[] {}, new IntVar[] {a, b});
  }

  /**
   * Generates clauses for implication constraint: a => b.
   *
   * @param a antecedent variable
   * @param b consequent variable
   */
  public void generateImplication(IntVar a, IntVar b) {
    // a => b
    // ===========
    // -a \/ b

    generateClause(new IntVar[] {b}, new IntVar[] {a});
  }

  /**
   * Generates clauses for reified implication constraint: {@code c <=> (a => b)}.
   *
   * @param a antecedent variable
   * @param b consequent variable
   * @param c reification variable
   */
  public void generateImplicationReif(IntVar a, IntVar b, IntVar c) {
    // (a => b) <=> c
    // ===========
    // (-a \/ b \/ -c) /\
    // (a \/ c) /\
    // (-b \/ c)

    generateClause(new IntVar[] {b}, new IntVar[] {a, c});
    generateClause(new IntVar[] {a, c}, new IntVar[] {});
    generateClause(new IntVar[] {c}, new IntVar[] {b});
  }

  /**
   * Generates clauses for reified all-zero constraint: {@code c <=> (a[0] = 0 /\ ... /\ a[n] = 0)}.
   *
   * @param as array of variables to check for zero
   * @param c reification variable
   */
  public void generateAllZeroReif(IntVar[] as, IntVar c) {
    // allZero(a) <=> c
    // - (a[0] \/ .. \/ a[n]) <=> c
    // ===========
    // /\_i (-a[i] \/ -c) /\ (a[0] \/ .. a[n] \/ c)

    // if any as[i] == 1 => c == 0
    for (IntVar a : as) {
      if (a.min() == 1) {
        c.domain.in(store.level, c, 0, 0);
        return;
      }
    }

    IntVar[] v = new IntVar[as.length + 1];
    for (int i = 0; i < as.length; i++) {
      v[i] = as[i];
      generateClause(new IntVar[] {}, new IntVar[] {as[i], c});
    }
    v[as.length] = c;
    generateClause(v, new IntVar[] {});
  }

  /**
   * Generates clauses for if-then-else boolean constraint: if c then a else b.
   *
   * @param c condition variable
   * @param a variable set to true when c is true
   * @param b variable set to true when c is false
   */
  public void generateIfThenElseBool(IntVar c, IntVar a, IntVar b) {
    // case for if c then a = true else b = true
    // (-c \/ a) /\ (c \/ b)
    generateClause(new IntVar[] {a}, new IntVar[] {c});
    generateClause(new IntVar[] {c, b}, new IntVar[] {});
  }

  /** Imposes the generated clauses on the store. */
  public void impose() {

    store.countConstraint();

    store.impose(clauses);
  }

  /**
   * Returns the number of clauses generated.
   *
   * @return the number of generated clauses
   */
  public long numberClauses() {
    return numberClauses;
  }

  /**
   * Converts a clause to its string representation.
   *
   * @param clause the clause as an array of literals
   * @return string representation of the clause
   */
  String clauseToString(int[] clause) {

    StringBuilder buffer = new StringBuilder();

    for (int j : clause) {
      buffer.append(j).append(" ");
    }

    buffer.append("\n");
    return buffer.toString();
  }
}
