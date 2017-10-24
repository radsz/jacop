/*
 * TupleUtils.java
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

package org.jacop.util;

/**
 * Util functions for arrays of tuples.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */
public class TupleUtils {

    int tupleNumber = 0;

    int[][] tuples;

    /**
     * It recordTuples to store so tuples can be reused across multiple
     * extensional constraints. It can potentially save memory.
     * @param ts tuples to be recorded.
     * @return two-dimensional array with tuples.
     */

    public int[][] recordTuples(int[][] ts) {

        int[][] sortedTs = sortTuples(ts);

        if (tuples == null) {
            tuples = new int[sortedTs.length][];
            for (int i = 0; i < sortedTs.length; i++) {
                tuples[i] = new int[sortedTs[i].length];
                for (int j = 0; j < sortedTs[i].length; j++)
                    tuples[i][j] = sortedTs[i][j];
            }
            tupleNumber = sortedTs.length;

            int[][] reusedTuples = new int[sortedTs.length][];
            for (int i = 0; i < sortedTs.length; i++)
                reusedTuples[i] = tuples[i];

            return reusedTuples;
        }

        int[] position = new int[sortedTs.length];
        boolean[] insert = new boolean[sortedTs.length];
        int insertNo = 0;

        int[][] reusedTuples = new int[sortedTs.length][];

        for (int i = 0; i < sortedTs.length; i++) {
            position[i] = findPositionForInsert(sortedTs[i]);

            insert[i] = true;

            if (smallerEqualTuple(tuples[position[i]], sortedTs[i]) && smallerEqualTuple(sortedTs[i], tuples[position[i]]))
                insert[i] = false;

            if (insert[i])
                insertNo++;
            else
                reusedTuples[i] = tuples[position[i]];
        }

        if (insertNo == 0)
            return reusedTuples;

        int[][] tuplesBeforeExtension = tuples;

        if (tupleNumber + insertNo > tuples.length)
            tuples = new int[tuples.length * 2][];
        else
            tuples = new int[tuples.length][];

        int previousPosition = 0;
        int performedInserts = 1;

        for (; previousPosition < insert.length; previousPosition++)
            if (insert[previousPosition])
                break;

        System.arraycopy(tuplesBeforeExtension, 0, tuples, 0, position[previousPosition]);

        tuplesBeforeExtension[position[previousPosition]] = new int[sortedTs[previousPosition].length];

        for (int j = 0; j < sortedTs[previousPosition].length; j++)
            tuplesBeforeExtension[position[previousPosition]][j] = sortedTs[previousPosition][j];

        reusedTuples[previousPosition] = tuplesBeforeExtension[position[previousPosition]];

        for (int i = previousPosition + 1; i < sortedTs.length; i++) {

            if (!insert[i])
                continue;

            System.arraycopy(tuplesBeforeExtension, position[previousPosition], // source
                tuples, position[previousPosition] + performedInserts, // target
                position[i] - position[previousPosition]); // quantity

            tuplesBeforeExtension[position[i] + performedInserts] = new int[sortedTs[i].length];

            for (int j = 0; j < sortedTs[i].length; j++)
                tuplesBeforeExtension[position[i] + performedInserts][j] = sortedTs[i][j];

            reusedTuples[i] = tuplesBeforeExtension[position[i] + performedInserts];

            performedInserts++;
            previousPosition = i;
        }

        System.arraycopy(tuplesBeforeExtension, position[previousPosition], // source
            tuples, position[previousPosition] + performedInserts, // target
            tupleNumber - position[previousPosition]); // quantity

        tupleNumber += performedInserts;

        return reusedTuples;

    }

    /**
     * searches for the position of the tuple in the tuple list.
     * @param tuple to be compared to.
     * @return position at which the tuple is stored in tuple list array.
     */
    public int findPositionForInsert(int[] tuple) {

        int left = 0;
        int right = tupleNumber;

        int position = (left + right) >> 1;

        while (!(left + 1 >= right)) {

            if (smallerEqualTuple(tuples[position], tuple)) {
                left = position;
            } else {
                right = position;
            }

            position = (left + right) >> 1;

        }

        if (smallerEqualTuple(tuple, tuples[left]))
            return left;

        if (smallerEqualTuple(tuple, tuples[right]))
            return right;

        return -1;
    }

    /**
     * @param ts tuples to be sorted.
     * @return sorted tuples.
     *
     */
    public int[][] sortTuples(int[][] ts) {

        int[][] result = new int[ts.length][];

        System.arraycopy(ts, 0, result, 0, ts.length);

        for (int i = 0; i < result.length; i++) {

            boolean change = false;

            for (int j = result.length - 1; j > i; j--)
                if (!smallerEqualTuple(result[j - 1], result[j])) {
                    change = true;
                    int[] tmp = result[j - 1];
                    result[j - 1] = result[j];
                    result[j] = tmp;
                }

            if (!change)
                break;
        }

        return result;

    }

    /**
     * It sorts tuples.
     * @param ts tuples to be sorted.
     */
    public static void sortTuplesWithin(int[][] ts) {

        for (int i = 0; i < ts.length; i++) {

            boolean change = false;

            for (int j = ts.length - 1; j > i; j--)
                if (!smallerEqualTuple(ts[j - 1], ts[j])) {
                    change = true;
                    int[] tmp = ts[j - 1];
                    ts[j - 1] = ts[j];
                    ts[j] = tmp;
                }

            if (!change)
                break;
        }

    }

    /**
     * It compares tuples.
     * @param left tuple to be compared to.
     * @param right tuple to compar with.
     * @return true if the left tuple is larger than right tuple.
     */
    public static boolean smallerEqualTuple(int[] left, int[] right) {

        if (right.length < left.length)
            return false;

        if (right.length > left.length)
            return true;

        for (int i = 0; i < left.length; i++) {
            if (left[i] < right[i])
                return true;
            if (left[i] > right[i])
                return false;
        }

        return true;
    }

}
