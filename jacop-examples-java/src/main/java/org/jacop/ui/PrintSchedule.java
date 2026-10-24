/*
 * PrintSchedule.java
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

package org.jacop.ui;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.List;
import org.jacop.core.IntDomain;
import org.jacop.core.IntVar;

/**
 * Prints the computed schedule.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
public class PrintSchedule {

  final int[] d;

  final List<String> n;

  final IntVar[] t;
  final IntVar[] r;

  /**
   * It constructs PrintSchedule object.
   *
   * @param name name of the operations.
   * @param t start time of the operations.
   * @param d duration time of the operations.
   * @param r resource usage of the operations.
   */
  public PrintSchedule(String[] name, IntVar[] t, int[] d, IntVar[] r) {
    n = new ArrayList<>();
    n.addAll(Arrays.asList(name));

    this.t = new IntVar[t.length];
    System.arraycopy(t, 0, this.t, 0, t.length);
    this.r = new IntVar[r.length];
    System.arraycopy(r, 0, this.r, 0, r.length);
    this.d = new int[d.length];
    System.arraycopy(d, 0, this.d, 0, d.length);
  }

  /**
   * It constructs PrintSchedule object.
   *
   * @param name name of the operations.
   * @param t start time of the operations.
   * @param d duration time of the operations.
   * @param r resource usage of the operations.
   */
  public PrintSchedule(String[] name, IntVar[] t, IntVar[] d, IntVar[] r) {
    n = new ArrayList<>();

    this.t = new IntVar[t.length];
    System.arraycopy(t, 0, this.t, 0, t.length);
    this.r = new IntVar[r.length];
    System.arraycopy(r, 0, this.r, 0, r.length);

    this.d = new int[d.length];
    for (int i = 0; i < d.length; i++) {
      this.d[i] = d[i].min();
      n.add(name[i]);
    }
  }

  /**
   * It constructs PrintSchedule object.
   *
   * @param name name of the operations.
   * @param t start time of the operations.
   * @param d duration time of the operations.
   * @param r resource usage of the operations.
   */
  public PrintSchedule(
      List<String> name, List<? extends IntVar> t, List<Integer> d, List<? extends IntVar> r) {
    n = name;
    this.t = new IntVar[t.size()];
    for (int i = 0; i < t.size(); i++) {
      this.t[i] = t.get(i);
    }
    this.r = new IntVar[r.size()];
    for (int i = 0; i < r.size(); i++) {
      this.r[i] = r.get(i);
    }
    this.d = new int[d.size()];
    for (int i = 0; i < d.size(); i++) {
      this.d[i] = d.get(i);
    }
  }

  /**
   * It constructs PrintSchedule object.
   *
   * @param name name of the operations.
   * @param t start time of the operations.
   * @param d duration time of the operations.
   * @param r resource usage of the operations.
   */
  public PrintSchedule(
      List<String> name, List<? extends IntVar> t, int[] d, List<? extends IntVar> r) {
    n = new ArrayList<>();
    n.addAll(name);

    this.t = new IntVar[t.size()];
    for (int i = 0; i < t.size(); i++) {
      this.t[i] = t.get(i);
    }
    this.r = new IntVar[r.size()];
    for (int i = 0; i < r.size(); i++) {
      this.r[i] = r.get(i);
    }
    this.d = new int[d.length];
    System.arraycopy(d, 0, this.d, 0, d.length);
  }

  /**
   * It constructs PrintSchedule object.
   *
   * @param name name of the operations.
   * @param t start time of the operations.
   * @param d duration time of the operations.
   * @param r resource usage of the operations.
   */
  public PrintSchedule(List<String> name, IntVar[] t, int[] d, IntVar[] r) {
    n = new ArrayList<>();
    n.addAll(name);

    this.t = new IntVar[t.length];
    System.arraycopy(t, 0, this.t, 0, t.length);
    this.r = new IntVar[r.length];
    System.arraycopy(r, 0, this.r, 0, r.length);
    this.d = new int[d.length];
    System.arraycopy(d, 0, this.d, 0, d.length);
  }

  /**
   * It constructs PrintSchedule object.
   *
   * @param name name of the operations.
   * @param t start time of the operations.
   * @param d duration time of the operations.
   * @param r resource usage of the operations.
   */
  public PrintSchedule(List<String> name, IntVar[] t, IntVar[] d, IntVar[] r) {
    n = new ArrayList<>();
    n.addAll(name);

    this.t = new IntVar[t.length];
    System.arraycopy(t, 0, this.t, 0, t.length);
    this.r = new IntVar[r.length];
    System.arraycopy(r, 0, this.r, 0, r.length);
    this.d = new int[d.length];
    for (int i = 0; i < d.length; i++) {
      this.d[i] = d[i].min();
    }
  }

  int findMaxR() {
    int m = 0;
    for (IntVar intVar : r) {
      if (m < intVar.min()) {
        m = intVar.min();
      }
    }
    return m;
  }

  int findMaxT() {
    int m = 0;
    for (int i = 0; i < d.length; i++) {
      if (m < t[i].min() + d[i] - 1) {
        m = t[i].min() + d[i] - 1;
      }
    }
    return m;
  }

  int findMinR() {
    int m = IntDomain.MAX_INT;
    for (IntVar intVar : r) {
      if (m > intVar.min()) {
        m = intVar.min();
      }
    }
    return m;
  }

  String tab(int i) {
    return " ".repeat(Math.max(0, i));
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder("\n");
    List<?>[] taskArr = buildSortedTaskArray();
    int maxR = findMaxR();
    int minR = findMinR();
    int resSize = maxR - minR + 1;
    int maxT = findMaxT();

    appendScheduleHeaderRow(result, minR, maxR);
    appendScheduleTimeRows(result, taskArr, minR, resSize, maxT);

    return result.toString();
  }

  private List<?>[] buildSortedTaskArray() {
    List<?>[] taskArr = new ArrayList[n.size()];
    for (int i = 0; i < n.size(); i++) {
      List<Object> v = new ArrayList<>();
      v.add(n.get(i));
      v.add(t[i]);
      v.add(d[i]);
      v.add(r[i]);
      taskArr[i] = v;
    }
    Comparator<List<?>> c =
        Comparator.comparingInt(o -> ((IntVar) o.get(1)).min() * 1000 + ((IntVar) o.get(3)).min());
    Arrays.sort(taskArr, c);
    return taskArr;
  }

  private void appendScheduleHeaderRow(StringBuilder result, int minR, int maxR) {
    result.append("\t").append(minR);
    for (int i = minR + 1; i <= maxR; i++) {
      result.append("\t\t").append(i);
    }
    result.append("\n");
  }

  private void appendScheduleTimeRows(
      StringBuilder result, List<?>[] taskArr, int minR, int resSize, int maxT) {
    for (int i = 0; i <= maxT; i++) {
      result.append(i).append("\t");
      List<List<Integer>> line = new ArrayList<>(resSize);
      for (int k = 0; k < resSize; k++) {
        line.add(new ArrayList<>());
      }
      fillLineForTime(i, taskArr, line, minR);
      for (List<Integer> integers : line) {
        int sp = result.length();
        for (Integer integer : integers) {
          result.append("[").append(taskArr[integer].getFirst()).append("]");
        }
        if (integers.isEmpty()) {
          result.append("-");
        }
        result.append(tab(16 - result.length() + sp));
      }
      result.append("\n");
    }
  }

  private void fillLineForTime(int time, List<?>[] taskArr, List<List<Integer>> line, int minR) {
    int j = 0;
    int start = taskArr.length > 0 ? ((IntVar) taskArr[0].get(1)).min() : time + 1;
    while (start <= time && j < taskArr.length) {
      int res = ((IntVar) taskArr[j].get(3)).min();
      start = ((IntVar) taskArr[j].get(1)).min();
      int dur = (Integer) taskArr[j].get(2);
      if (start <= time && start + dur > time) {
        line.get(res - minR).add(j);
      }
      j++;
    }
  }
}
