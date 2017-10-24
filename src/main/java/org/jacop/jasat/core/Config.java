/*
 * Config.java
 * <p>
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
 * The configuration for a solver. It contains all numeric values or
 * enumerations needed to set the solver behavior; those parameters can be
 * changed before the Config object is given to the solver.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 *
 */

@SuppressWarnings("serial") public class Config extends Properties {

    /**
     * how many clausesDatabases can we have ? must be a power of 2
     */
    public int MAX_NUMBER_OF_DATABASES = 8;


    /**
     * number of int[] of each size in the memory pool
     */
    public int MEMORY_POOL_STOCK_SIZE = 500;


    /**
     * the maximum size of int[] to store in the memory pool
     */
    public int MEMORY_POOL_MAX_SIZE = 60;


    /**
     * threshold above which a rebase is performed for activity counters
     */
    public int rebase_threshold = Integer.MAX_VALUE / 10;


    /**
     * the default bump rate. It is added to activity at each bump()
     */
    public int bump_rate = 4;


    /**
     * initial number of variables in the trail
     */
    public int trail_size = 100;


    /**
     * controls default solver verbosity
     */
    public int verbosity = 0;


    /**
     * the default timeout, in seconds, for searches.
     */
    public long timeout = 0;


    /**
     * switch for debug mode
     */
    public boolean debug = false;

    /**
     * random seed, to be changed if we want to redo the same run
     */
    public long seed = System.currentTimeMillis();

    /**
     * factor by which restart threshold is increased
     */
    public double RESTART_THRESHOLD_INCREASE_RATE = 1.5;

    /**
     * initial threshold (number of conflicts needed) for restarts
     */
    public long RESTART_CONFLICT_THRESHOLD = 100;

    /**
     * the list of components the solver must add
     */
    public List<SolverComponent> mainComponents = new ArrayList<SolverComponent>();

    /**
     * the list of databases the solver must add
     */
    public List<AbstractClausesDatabase> clausesDatabases = new ArrayList<AbstractClausesDatabase>();


    @Override public String toString() {
        StringBuilder sb = new StringBuilder();

        // TODO : enhance
        for (Field field : this.getClass().getFields()) {
            try {
                sb.append(String.format("%-30s: %s\n", field.getName(), field.get(this)));
            } catch (IllegalArgumentException e) {
            } catch (IllegalAccessException e) {
            }
        }

        return sb.toString();

    }

    /**
     * check some properties of the config
     * @return true if the config passes check, false if there is a problem
     */
    public boolean check() {

        // check it is a power of 2
        if (Integer.bitCount(MAX_NUMBER_OF_DATABASES) != 1)
            return false;

        return true;
    }

    /**
     * constructor for config, that adds some default components. If you want
     * to choose all components, just components.clear() (if you know what
     * you do)
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
     * static access to the default config
     *
     * @return default config
     */
    public static Config defaultConfig() {
        return new Config();
    }


}
