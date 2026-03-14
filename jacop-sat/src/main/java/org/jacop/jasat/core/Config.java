/*
 * Config.java
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

package org.jacop.jasat.core;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;
import org.jacop.jasat.core.clauses.AbstractClausesDatabase;
import org.jacop.jasat.core.clauses.BinaryClausesDatabase;
import org.jacop.jasat.core.clauses.DefaultClausesDatabase;
import org.jacop.jasat.core.clauses.TernaryClausesDatabase;
import org.jacop.jasat.core.clauses.UnaryClausesDatabase;

/**
 * The configuration for a solver. It contains all numeric values or enumerations needed to set the
 * solver behavior; those parameters can be changed before the Config object is given to the solver.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
@SuppressWarnings("serial")
public class Config extends Properties {

  /** How many clausesDatabases can we have ? must be a power of 2. */
  public final int maxNumberOfDatabases = 8;

  /** Number of int[] of each size in the memory pool. */
  public final int memoryPoolStockSize = 500;

  /** The maximum size of int[] to store in the memory pool. */
  public final int memoryPoolMaxSize = 60;

  /** Threshold above which a rebase is performed for activity counters. */
  public final int rebase_threshold = Integer.MAX_VALUE / 10;

  /** The default bump rate. It is added to activity at each bump() */
  public final int bump_rate = 4;

  /** Initial number of variables in the trail. */
  public final int trail_size = 100;

  /** Factor by which restart threshold is increased. */
  public final double restartThresholdIncreaseRate = 1.5;

  /** Initial threshold (number of conflicts needed) for restarts. */
  public final long restartConflictThreshold = 100;

  /** The list of components the solver must add. */
  public final List<SolverComponent> mainComponents = new ArrayList<>();

  /** The list of databases the solver must add. */
  public final List<AbstractClausesDatabase> clausesDatabases = new ArrayList<>();

  /** Controls default solver verbosity. */
  public int verbosity;

  /** The default timeout, in seconds, for searches. */
  public long timeout;

  /** Switch for debug mode. */
  public boolean debug;

  /** Random seed, to be changed if we want to redo the same run. */
  public long seed = System.currentTimeMillis();

  /**
   * Constructor for config, that adds some default components. If you want to choose all
   * components, just components.clear() (if you know what you do)
   */
  public Config() {

    // create default databases and add them to store
    DefaultClausesDatabase stdDb = new DefaultClausesDatabase();
    UnaryClausesDatabase unaryDb = new UnaryClausesDatabase();
    BinaryClausesDatabase binDb = new BinaryClausesDatabase();
    TernaryClausesDatabase triDb = new TernaryClausesDatabase();

    // first, the most efficient databases (binary and ternary clauses)
    clausesDatabases.add(binDb);
    clausesDatabases.add(triDb);
    clausesDatabases.add(stdDb);
    clausesDatabases.add(unaryDb);
  }

  /**
   * Static access to the default config.
   *
   * @return default config
   */
  public static Config defaultConfig() {
    return new Config();
  }

  @Override
  public synchronized String toString() {
    StringBuilder sb = new StringBuilder();

    for (Field field : this.getClass().getFields()) {
      try {
        sb.append("%-30s: %s\n".formatted(field.getName(), field.get(this)));
      } catch (IllegalArgumentException | IllegalAccessException e) {
        // Ignore reflection errors for inaccessible fields; e.getMessage() would show the cause
        assert e != null;
      }
    }

    return sb.toString();
  }

  /**
   * Check some properties of the config.
   *
   * @return true if the config passes check, false if there is a problem
   */
  public boolean check() {

    // check it is a power of 2
    return Integer.bitCount(maxNumberOfDatabases) == 1;
  }
}
