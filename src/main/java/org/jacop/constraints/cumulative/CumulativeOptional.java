/*
 * CumulativeOptional.java
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

package org.jacop.constraints.cumulative;

import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;
import org.jacop.core.BooleanVar;
import org.jacop.core.Store;
import java.util.*;
import java.util.stream.Stream;

/*
 * CumulativeOptional implements the scheduling constraint for optional tasks.
 * 
 * @author Krzysztof Kuchcinski
 * @version 4.9
 * @see <a href="http://urn.kb.se/resolve?urn=urn:nbn:se:uu:diva-132172">http://urn.kb.se/resolve?urn=urn:nbn:se:uu:diva-132172</a>
 */

public class CumulativeOptional extends Cumulative {

    IntVar[] opt;

    ProfileOptional up;

    /**
     * It creates a cumulative constraint.
     *
     * @param starts    variables denoting starts of the tasks.
     * @param durations variables denoting durations of the tasks.
     * @param resources variables denoting resource usage of the tasks.
     * @param limit     the overall limit of resources which has to be used.
     * @param opt       variables informing whether the tasks is present or not.
     */
    public CumulativeOptional(IntVar[] starts, IntVar[] durations, IntVar[] resources, IntVar limit, IntVar[] opt) {

        super(starts, durations, resources, limit);

        this.opt = opt;

        up = new ProfileOptional(limit);

        setScope(Stream.concat(
                               Stream.concat(
                                             Stream.concat(Arrays.stream(starts), Arrays.stream(durations)),
                                             Stream.concat(Arrays.stream(resources), Stream.of(limit))),
                               Arrays.stream(opt)));
    }

    /**
     * It creates a cumulative constraint.
     *
     * @param starts    variables denoting starts of the tasks.
     * @param durations variables denoting durations of the tasks.
     * @param resources variables denoting resource usage of the tasks.
     * @param limit     the overall limit of resources which has to be used.
     * @param opt       variables informing whether the tasks is present or not.
     */
    public CumulativeOptional(List<? extends IntVar> starts, List<? extends IntVar> durations, List<? extends IntVar> resources, IntVar limit,
                              List<? extends IntVar> opt) {

        this(starts.toArray(new IntVar[starts.size()]), durations.toArray(new IntVar[durations.size()]),
             resources.toArray(new IntVar[resources.size()]), limit, opt.toArray(new IntVar[opt.size()]));

    }

    
    @Override public void consistency(Store store) {

        do {

            store.propagationHasOccurred = false;

            up.sweepPruning(store, taskNormal, opt);
            // up.updateTasksRes(store, ts);

            if (!store.propagationHasOccurred && doEdgeFind) {
                // overloadCheck();  // not needed if profile propagator is used
                if (doQuadraticEdgeFind)
                    edgeFindQuad(store);
                else
                    edgeFind(store);
            }

        } while (store.propagationHasOccurred);
    }

    
    TaskView[] filterZeroTasks(TaskView[] ts) {

        TaskView[] nonZeroTasks = new TaskView[ts.length];
        int k = 0;

        for (int i = 0; i < ts.length; i++)
            if (ts[i].res.min() != 0 && ts[i].dur.min() != 0 && opt[i].min() != 0) {
                nonZeroTasks[k] = ts[i];
                ts[i].index = k++;
            }

        if (k == 0)
            return null;
        TaskView[] t = new TaskView[k];
        System.arraycopy(nonZeroTasks, 0, t, 0, k);
        return t;
    }

    @Override public int getDefaultConsistencyPruningEvent() {
        return IntDomain.BOUND;
    }

    @Override public String toString() {

        StringBuilder result = new StringBuilder(id());
        if (doEdgeFind)
            result.append(" : cumulativeOptional([ ");
        else if (super.cumulativeForConstants != null)
            result.append(" : cumulativePrimary([ ");
        else
            result.append(" : cumulativeBasic([ ");

        for (int i = 0; i < taskNormal.length - 1; i++)
            result.append(taskNormal[i]).append(", ");

        result.append(taskNormal[taskNormal.length - 1]);

        result.append(" ]").append(", limit = ").append(limit)
            .append(", " + java.util.Arrays.asList(opt)).append(", quad=" + doQuadraticEdgeFind + " )");

        return result.toString();

    }

}