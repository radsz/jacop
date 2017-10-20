/*
 * CPvizGardner.java
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

package org.jacop.examples.cpviz;

import org.jacop.constraints.Not;
import org.jacop.core.BooleanVar;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SimpleSolutionListener;
import org.jacop.search.TraceGenerator;
import org.jacop.set.constraints.AeqB;
import org.jacop.set.constraints.AintersectBeqC;
import org.jacop.set.constraints.CardA;
import org.jacop.set.constraints.CardAeqX;
import org.jacop.set.core.SetVar;
import org.jacop.set.search.IndomainSetMin;

/**
 * It shows how to visualize solving process for Gardner problem.
 *
 * @author Krzysztof Kuchcinski
 * @version 4.5
 */
public class CPvizGardner {
    Store store;

    public static void main(String args[]) {

        CPvizGardner run = new CPvizGardner();
        run.examples();
    }

    CPvizGardner() {
    }

    void examples() {

        ex1();

    }


    void ex1() {
        //       long T1, T2, T;
        //       T1 = System.currentTimeMillis();


        Thread tread = java.lang.Thread.currentThread();
        java.lang.management.ThreadMXBean b = java.lang.management.ManagementFactory.getThreadMXBean();

        long startCPU = b.getThreadCpuTime(tread.getId());
        long startUser = b.getThreadUserTime(tread.getId());

        // int num_days = 35;
        int num_persons_per_meeting = 3;
        int persons = 15;

        System.out.println("Gardner dinner problem ");
        store = new Store();

        SetVar[] days = new SetVar[35];
        for (int i = 0; i < days.length; i++)
            days[i] = new SetVar(store, "days[" + i + "]", 1, persons);

        // all_different(days)
        for (int i = 0; i < days.length - 1; i++)
            for (int j = i + 1; j < days.length; j++)
                store.impose(new Not(new AeqB(days[i], days[j])));

        // card(days[i]) = num_persons_per_meeting
        for (int i = 0; i < days.length; i++)
            store.impose(new CardA(days[i], num_persons_per_meeting));

        for (int i = 0; i < days.length - 1; i++)
            for (int j = i + 1; j < days.length; j++) {
                SetVar intersect = new SetVar(store, "" + i + j, 1, persons);
                store.impose(new AintersectBeqC(days[i], days[j], intersect));
                IntVar card = new BooleanVar(store); //IntVar(store, 0, 1);
                store.impose(new CardAeqX(intersect, card));
            }


        System.out.println("\nVariable store size: " + store.size() + "\nNumber of constraints: " + store.numberConstraints());

        boolean Result = store.consistency();
        System.out.println("*** consistency = " + Result);

        Search<SetVar> label = new DepthFirstSearch<SetVar>();

        SelectChoicePoint<SetVar> varSelect = new SimpleSelect<SetVar>(days, null, new IndomainSetMin<SetVar>());

        label.setSolutionListener(new SimpleSolutionListener<SetVar>());
        label.getSolutionListener().searchAll(false);
        label.getSolutionListener().recordSolutions(false);

        // Trace --->
        SelectChoicePoint<SetVar> select = new TraceGenerator<SetVar>(label, varSelect); //, days);
        //      label.setConsistencyListener((ConsistencyListener)select);
        //     label.setExitChildListener((ExitChildListener)select);
        //      label.setExitListener((ExitListener)select);
        // <---

        Result = label.labeling(store, select);

        if (Result) {
            System.out.println("*** Yes");
            for (int i = 0; i < days.length; i++) {
                System.out.println(days[i]);
            }
        } else
            System.out.println("*** No");

        //       T2 = System.currentTimeMillis();
        //       T = T2 - T1;
        //       System.out.println("\n\t*** Execution time = "+ T + " ms");

        System.out.println("ThreadCpuTime = " + (b.getThreadCpuTime(tread.getId()) - startCPU) / (long) 1e+6 + "ms");
        System.out.println("ThreadUserTime = " + (b.getThreadUserTime(tread.getId()) - startUser) / (long) 1e+6 + "ms");

        // 	System.out.printf("CPU time = %5.3fs%n", (float)(((float)b.getThreadCpuTime(tread.getId()) - startCPU)/1e+9));
    }
}
