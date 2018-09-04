/*
 * FilterBenchmarkTest.java
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

package org.jacop;

import org.jacop.core.Store;
import org.jacop.examples.fd.filters.*;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Collection;

import static org.junit.Assert.assertEquals;

/*
* This is a test based on the filter scheduling examples, commonly used in High-Level Synthesis.
*
* @author Mariusz Świerkot and Radoslaw Szymanek
*/
@RunWith(Parameterized.class)
public class FilterBenchmarkTest extends FilterBenchmark {

    private int[] resourcesConfiguration;
    private Filter filter;
    private int costExp;
    private String experiment;

    public FilterBenchmarkTest(int resourcesConfiguration[], Filter filterTest, String experiment, int costExp) {
        this.resourcesConfiguration = resourcesConfiguration;
        this.filter = filterTest;
        this.experiment = experiment;
        this.costExp = costExp;
    }

    @Parameterized.Parameters
    public static Collection primeNumbers() {
        return Arrays.asList(new Object[][]{
                {new int[]{1, 1}, new DFQ(), "experiment1", 13},
                {new int[]{1, 2}, new DFQ(), "experiment1", 8},
                {new int[]{1, 3}, new DFQ(), "experiment1", 7},
                {new int[]{2, 2}, new DFQ(), "experiment1", 7},
                {new int[]{1, 4}, new DFQ(), "experiment1", 6},
                {new int[]{2, 3}, new DFQ(), "experiment1", 6},
                {new int[]{1, 1}, new FIR(), "experiment1", 18},
                {new int[]{1, 2}, new FIR(), "experiment1", 15},
                {new int[]{2, 2}, new FIR(), "experiment1", 11},
                {new int[]{2, 3}, new FIR(), "experiment1", 10},
                {new int[]{1, 1}, new AR(1,1), "experiment2", 18},
                {new int[]{1, 2}, new AR(1,1), "experiment2", 13},
                {new int[]{1, 3}, new AR(1,1), "experiment2", 13},
                {new int[]{2, 3}, new AR(1,1), "experiment2", 10},
                {new int[]{2, 4}, new AR(1,1), "experiment2", 8},
                {new int[]{1, 1}, new EWF(), "experiment1", 28},
                {new int[]{2, 1},  new EWF(), "experiment1", 21},
                {new int[]{2, 2},  new EWF(), "experiment1", 18},
                {new int[]{3, 3},  new EWF(), "experiment1", 17},
                {new int[]{1, 1}, new EWF(1,1), "experiment1", 27},
                {new int[]{2, 1},  new EWF(1,1), "experiment1", 16},
                {new int[]{2, 2},  new EWF(1,1), "experiment1", 16},
                {new int[]{3, 3},  new EWF(1,1), "experiment1", 14},
                {new int[]{1, 1},  new DCT(), "experiment1", 34},
                {new int[]{1, 2},  new DCT(), "experiment1", 32},
                {new int[]{2, 2},  new DCT(), "experiment1", 18},
                {new int[]{2, 3},  new DCT(), "experiment1", 16},
                {new int[]{3, 3},  new DCT(), "experiment1", 14},
                {new int[]{3, 4},  new DCT(), "experiment1", 11},
                {new int[]{4, 4},  new DCT(), "experiment1", 10},
                {new int[]{1, 1},  new DFQ(), "experiment1PM", 8},
                {new int[]{1, 2},  new DFQ(), "experiment1PM", 6},
                {new int[]{1, 1},  new FIR(), "experiment1PM", 15},
                {new int[]{2, 1},  new FIR(), "experiment1PM", 11},
                {new int[]{2, 2},  new FIR(), "experiment1PM", 10},
                {new int[]{1, 1},  new AR(), "experiment2PM", 19},
                {new int[]{2, 1},  new AR(), "experiment2PM", 19},
                {new int[]{2, 2},  new AR(), "experiment2PM", 13},
                {new int[]{2, 4},  new AR(), "experiment2PM", 11},
                {new int[]{2, 1},  new EWF(), "experiment1PM", 19},
                {new int[]{3, 1},  new EWF(), "experiment1PM", 18},
                {new int[]{3, 2},  new EWF(), "experiment1PM", 17},
                {new int[]{1, 1},  new DCT(), "experiment1PM", 32},
                {new int[]{2, 1},  new DCT(), "experiment1PM", 19},
                {new int[]{2, 2},  new DCT(), "experiment1PM", 16},
                {new int[]{3, 2},  new DCT(), "experiment1PM", 11},
                {new int[]{4, 3},  new DCT(), "experiment1PM", 9},
                {new int[]{5, 4},  new DCT(), "experiment1PM", 8},
                {new int[]{6, 5},  new DCT(), "experiment1PM", 7},
                {new int[]{1, 1, 3},  new DFQ(), "experiment1C", 18},
                {new int[]{1, 2, 3},  new DFQ(), "experiment1C", 13},
                {new int[]{2, 2, 3},  new DFQ(), "experiment1C", 9},
                {new int[]{2, 1, 2},  new FIR(), "experiment1C", 19},
                {new int[]{2, 2, 2},  new FIR(), "experiment1C", 15},
                {new int[]{3, 2, 2},  new FIR(), "experiment1C", 12},
                {new int[]{1, 1, 3},  new FIR(), "experiment1C", 43},
                {new int[]{2, 1, 3},  new FIR(), "experiment1C", 24},
                {new int[]{3, 2, 3},  new FIR(), "experiment1C", 15},
                {new int[]{2, 2, 2},  new AR(), "experiment1C", 18},
                {new int[]{2, 3, 2},  new AR(), "experiment1C", 16},
                {new int[]{4, 4, 2},  new AR(), "experiment1C", 12},
                {new int[]{1, 1, 3},  new AR(), "experiment1C", 49},
                {new int[]{1, 2, 3},  new AR(), "experiment1C", 34},
                {new int[]{2, 2, 3},  new AR(), "experiment1C", 25},
                {new int[]{2, 3, 3},  new AR(), "experiment1C", 19},
                {new int[]{3, 4, 3},  new AR(), "experiment1C", 13},
                {new int[]{3, 4, 3},  new AR(), "experiment1C", 13},
                {new int[]{2, 2, 4},  new AR(), "experiment1C", 32},
                {new int[]{2, 3, 4},  new AR(), "experiment1C", 24},
                {new int[]{2, 1, 2},  new EWF(), "experiment1C", 29},
                {new int[]{3, 1, 2},  new EWF(), "experiment1C", 21},
                {new int[]{1, 1, 3},  new EWF(), "experiment1C", 76},
                {new int[]{2, 1, 3},  new EWF(), "experiment1C", 40},
                {new int[]{3, 1, 3},  new EWF(), "experiment1C", 30},
                {new int[]{1, 1, 4},  new EWF(), "experiment1C", 101},
                {new int[]{2, 1, 4},  new EWF(), "experiment1C", 49},
                {new int[]{3, 1, 4},  new EWF(), "experiment1C", 35},
                {new int[]{2, 1, 2},  new DCT(), "experiment1C", 35},
                {new int[]{2, 2, 2},  new DCT(), "experiment1C", 31},
                {new int[]{3, 2, 2},  new DCT(), "experiment1C", 21},
                {new int[]{4, 2, 2},  new DCT(), "experiment1C", 19},
                {new int[]{4, 3, 2},  new DCT(), "experiment1C", 15},
                {new int[]{5, 4, 2},  new DCT(), "experiment1C", 13},
                {new int[]{1, 1, 3},  new DCT(), "experiment1C", 94},
                {new int[]{2, 1, 3},  new DCT(), "experiment1C", 48},
                {new int[]{3, 2, 3},  new DCT(), "experiment1C", 31},
                {new int[]{4, 2, 3},  new DCT(), "experiment1C", 24},
                {new int[]{5, 3, 3},  new DCT(), "experiment1C", 19},
                {new int[]{1, 3},  new DFQ(), "experiment1P", 5}
        });
    }

    @Test
    public void testFilter() throws InvocationTargetException, IllegalAccessException, ClassNotFoundException, NoSuchMethodException {

        Class cls = this.getClass();
        Method exp = cls.getMethod(experiment, Store.class, Filter.class, int[].class);
        
        int costFound = (Integer) exp.invoke(this, new Store(), filter, resourcesConfiguration);

        assertEquals("Test " + experiment + " failed for " + Filter.class , costExp, costFound);
    }


        /**
         * It solves available filters for different scenario
         * consisting of different number of resources.
         */
//        public void schedule(int dfqeX[][], Filter filter ) {
//
////            int dfqEx[][] = {{1, 1}, {1, 2}, {1, 3}, {2, 2}, {1, 4}, {2, 3}};
//                experiment1(store, dfq, a, m);

//            int firEx[][] = {{1, 1}, {1, 2}, {2, 2}, {2, 3}};
//                experiment1(store, fir, a, m);
//
//            int arEx[][] = {{1, 1}, {1, 2}, {1, 3}, {2, 3}, {2, 4}};
//                experiment2(store, ar, a, m);
//
//            int ewfEx[][] = {{1, 1}, {2, 1}, {2, 2}, {3, 3}};
//                experiment1(store, ewf, a, m);
//
//            int ewfEx2[][] = {{1, 1}, {2, 1}, {2, 2}, {3, 3}};
//                experiment1(store, ewf, a, m);
//
//            int dctEx[][] = {{1, 1}, {1, 2}, {2, 2}, {2, 3}, {3, 3}, {3, 4}, {4, 4}};
//                experiment1(store, dct, a, m);

//
//            int dfqEx[][] = {{1, 1}, {1, 2}};
//                experiment1PM(store, dfq, a, m);
//
//            int firEx[][] = {{1, 1}, {2, 1}, {2, 2}};
//                experiment1PM(store, fir, a, m);

//            int arEx[][] = {{1, 1}, {1, 2}, {2, 2}, {2, 4}};
//                experiment2PM(store, ar, a, m);
//
//            int ewfEx[][] = {{2, 1}, {3, 1}, {3, 2}};
//                experiment1PM(store, ewf, a, m);

//            int dctEx[][] = {{1, 1}, {2, 1}, {2, 2}, {3, 2}, {4, 3}, {5, 4}, {6, 5}};
//                experiment1PM(store, dct, a, m);
//
//        }
//
//
//            int dfqEx[][] = {{1, 1, 3}, {1, 2, 3}, {2, 2, 3}};
//                experiment1C(store, dfq, a, m, s);
//
//            int firEx[][] = {{2, 1, 2}, {2, 2, 2}, {3, 2, 2}, {1, 1, 3}, {2, 1, 3}, {3, 2, 3}};
//                experiment1C(store, fir, a, m, s);
//
//            int arEx[][] =
//                    {{2, 2, 2}, {2, 3, 2}, {4, 4, 2}, {1, 1, 3}, {1, 2, 3}, {2, 2, 3}, {2, 3, 3}, {2, 4, 3}, {3, 4, 3}, {2, 2, 4}, {2, 3, 4},
//                            {3, 4, 4}};
//                experiment1C(store, ar, a, m, s);
//
//            int ewfEx[][] = {{2, 1, 2}, {3, 1, 2}, {1, 1, 3}, {2, 1, 3}, {3, 1, 3}, {1, 1, 4}, {2, 1, 4}, {3, 1, 4}};
//                experiment1C(store, ewf, a, m, s);
//
//            int dctEx[][] =
//                    {{2, 1, 2}, {2, 2, 2}, {3, 2, 2}, {4, 2, 2}, {4, 3, 2}, {5, 4, 2}, {1, 1, 3}, {2, 1, 3}, {3, 2, 3}, {4, 2, 3}, {5, 3, 3}};
//                experiment1C(store, dct, a, m, s);
//
//
//            int dfqEx[][] = {{1, 3}, {2, 3}};
//                experiment1P(store, dfqP, a, m);
//
//            int firEx[][] = {{2, 2}, {3, 3}, {3, 4}};
//                experiment1P(store, firP, a, m);
//            }
//
//            int arEx[][] = {{2, 4}, {2, 6}, {3, 8}};
//                experiment1P(store, arP, a, m);
//
//            int ewfEx[][] = {{3, 2}, {4, 2}, {4, 3}, {5, 4}};
//                experiment1P(store, ewfP, a, m);
//
//            int dctEx[][] = {{4, 4}, {4, 5}, {5, 6}, {6, 7}, {7, 8}};
//                experiment1P(store, dctP, a, m);
//
//            int fftEx[][] = {{1, 1}, {1, 2}, {2, 2}, {3, 4}};
//                experiment1P(store, fftP, a, m);
//

        /**
         * It optimizes scheduling of filter operations.
         *
         * @param store the constraint store in which the constraints are imposed.
         * @param filter the filter being scheduled.
         */
        public int experiment1(Store store, Filter filter, int[] configuration) {
            return experiment1(store, filter, configuration[0], configuration[1]);
        }


    public int experiment2(Store store, Filter filter, int[] configuration) {
        return experiment2(store, filter, configuration[0], configuration[1]);
    }


        /**
         * It optimizes scheduling of filter operation in fashion allowing
         * chaining of operations within one clock cycle.
         *
         * @param store the constraint store in which the constraints are imposed.
         * @param filter the filter being scheduled.
         * @param configuration number of adders available, number of multipliers available, number of time units within a clock.
         */
        public int experiment1C(Store store, Filter filter, int[] configuration) {

            return experiment1C(store, filter, configuration[0], configuration[1], configuration[2]);

        }

        /**
         * It optimizes scheduling of filter operations in a fashion allowing
         * pipelining of multiplication operations.
         *
         * @param store the constraint store in which the constraints are imposed.
         * @param filter the filter being scheduled.
         * @param configuration number of adders available, number of multipliers available.
         */
        public int experiment1PM(Store store, Filter filter, int[] configuration) {
            return experiment1PM(store, filter, configuration[0], configuration[1]);
        }

        /**
         * It optimizes scheduling of filter operation in fashion allowing
         * pipelining of multiplication operations.
         *
         * @param store the constraint store in which the constraints are imposed.
         * @param filter the filter being scheduled.
         * @param configuration it specifies number of resource available.
         */
        public int experiment2PM(Store store, Filter filter, int[] configuration) {

            return experiment2PM(store, filter, configuration[0], configuration[1]);

        }



        /**
         * It optimizes scheduling of filter operations. It performs algorithmic
         * pipelining.
         *
         * @param store the constraint store in which the constraints are imposed.
         * @param filter the filter being scheduled.
         * @param addNum number of adders available.
         * @param mulNum number of multipliers available.
         */
        public int experiment1P(Store store, Filter filter, int[] configuration ) {

            return experiment1P(store, filter, configuration[0], configuration[1]);

        }

        /**
         * It optimizes scheduling of filter operations. It performs
         * algorithmic pipelining three times.
         *
         * @param store the constraint store in which the constraints are imposed.
         * @param filter the filter being scheduled.
         * @param addNum number of adders available.
         * @param mulNum number of multipliers available.
         */
        public int experiment2P(Store store, Filter filter, int[] configuration) {

            return experiment2P(store, filter, configuration[0], configuration[1]);
        }


        /**
         * It optimizes scheduling of filter operation in fashion allowing
         * chaining of operations within one clock cycle.
         *
         * @param store the constraint store in which the constraints are imposed.
         * @param filter the filter being scheduled.
         * @param addNum number of adders available.
         * @param mulNum number of multipliers available.
         * @param clock number of time units within a clock.
         */
        public int experiment2C(Store store, Filter filter, int[] configuration) {

            return experiment2C(store, filter, configuration[0], configuration[1], configuration[2]);

        }

    }



