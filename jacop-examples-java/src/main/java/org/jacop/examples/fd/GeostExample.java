/*
 * GeostExample.java
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

package org.jacop.examples.fd;

import java.util.ArrayList;
import java.util.List;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.geost.Dbox;
import org.jacop.constraints.geost.ExternalConstraint;
import org.jacop.constraints.geost.Geost;
import org.jacop.constraints.geost.GeostObject;
import org.jacop.constraints.geost.InArea;
import org.jacop.constraints.geost.NonOverlapping;
import org.jacop.constraints.geost.Shape;
import org.jacop.core.IntVar;
import org.jacop.core.Store;

/**
 * It specifies an example where squares of the given size must be placed within a square of a given
 * size.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class GeostExample extends ExampleFd {

  /**
   * It specifies and runs a very simple Geost example. It is just to present how Geost constraint
   * can be created and imposed to store.
   *
   * @param args no parameters read.
   */
  static void main(String[] args) {
    if (args == null) {
      throw new IllegalArgumentException("args must not be null");
    }
    GeostExample example = new GeostExample();
    example.model();
    example.search();
  }

  /** Creates the constraint model for the Geost constraint example. */
  @Override
  public void model() {

    store = new Store();

    final List<Shape> shapes = new ArrayList<>();
    final List<GeostObject> objects = new ArrayList<>();
    final List<ExternalConstraint> constraints = new ArrayList<>();

    // Object O1- shapes 1, 2, 3 and 4
    List<Dbox> shape1 = new ArrayList<>();
    shape1.add(new Dbox(new int[] {0, 0}, new int[] {2, 1}));
    shape1.add(new Dbox(new int[] {0, 1}, new int[] {1, 2}));
    shape1.add(new Dbox(new int[] {1, 2}, new int[] {3, 1}));
    shapes.add(new Shape(0, shape1));

    List<Dbox> shape2 = new ArrayList<>();
    shape2.add(new Dbox(new int[] {0, 0}, new int[] {3, 1}));
    shape2.add(new Dbox(new int[] {0, 1}, new int[] {1, 3}));
    shape2.add(new Dbox(new int[] {2, 1}, new int[] {1, 1}));
    shapes.add(new Shape(1, shape2));

    List<Dbox> shape3 = new ArrayList<>();
    shape3.add(new Dbox(new int[] {0, 0}, new int[] {2, 1}));
    shape3.add(new Dbox(new int[] {1, 1}, new int[] {1, 2}));
    shape3.add(new Dbox(new int[] {2, 2}, new int[] {3, 1}));
    shapes.add(new Shape(2, shape3));

    List<Dbox> shape4 = new ArrayList<>();
    shape4.add(new Dbox(new int[] {0, 0}, new int[] {3, 1}));
    shape4.add(new Dbox(new int[] {0, 1}, new int[] {1, 1}));
    shape4.add(new Dbox(new int[] {2, 1}, new int[] {1, 3}));
    shapes.add(new Shape(3, shape4));

    IntVar X_o1 = new IntVar(store, "x1", 0, 1);
    IntVar Y_o1 = new IntVar(store, "y1", 0, 1);
    IntVar[] coords_o1 = {X_o1, Y_o1};
    IntVar shape_o1 = new IntVar(store, "shape_o1", 0, 3);
    IntVar start_o1 = new IntVar(store, "start_o1", 2, 2);
    IntVar duration_o1 = new IntVar(store, "duration_o1", 12, 12);
    IntVar end_o1 = new IntVar(store, "end_o1", 14, 14);
    GeostObject o1 = new GeostObject(0, coords_o1, shape_o1, start_o1, duration_o1, end_o1);
    objects.add(o1);

    //  Object o2- shapes 5 and 6
    List<Dbox> shape5 = new ArrayList<>();
    shape5.add(new Dbox(new int[] {0, 0}, new int[] {2, 1}));
    shape5.add(new Dbox(new int[] {1, 1}, new int[] {1, 1}));
    shape5.add(new Dbox(new int[] {0, 2}, new int[] {2, 1}));
    shapes.add(new Shape(4, shape5));

    List<Dbox> shape6 = new ArrayList<>();
    shape6.add(new Dbox(new int[] {0, 0}, new int[] {3, 1}));
    shape6.add(new Dbox(new int[] {0, 1}, new int[] {1, 1}));
    shape6.add(new Dbox(new int[] {2, 1}, new int[] {1, 1}));
    shapes.add(new Shape(5, shape6));

    IntVar X_o2 = new IntVar(store, "x2", 0, 2);
    IntVar Y_o2 = new IntVar(store, "y2", 0, 1);
    IntVar[] coords_o2 = {X_o2, Y_o2};
    IntVar shape_o2 = new IntVar(store, "shape_o2", 4, 5);
    IntVar start_o2 = new IntVar(store, "start_o2", 10, 10);
    IntVar duration_o2 = new IntVar(store, "duration_o2", 12, 12);
    IntVar end_o2 = new IntVar(store, "end_o2", 22, 22);
    GeostObject o2 = new GeostObject(1, coords_o2, shape_o2, start_o2, duration_o2, end_o2);
    objects.add(o2);

    //  Object o3- shapes 7 and 8
    List<Dbox> shape7 = new ArrayList<>();
    shape7.add(new Dbox(new int[] {0, 0}, new int[] {3, 2}));
    shapes.add(new Shape(6, shape7));

    List<Dbox> shape8 = new ArrayList<>();
    shape8.add(new Dbox(new int[] {0, 0}, new int[] {2, 3}));
    shapes.add(new Shape(7, shape8));

    IntVar X_o3 = new IntVar(store, "x3", 0, 4);
    IntVar Y_o3 = new IntVar(store, "y3", 0, 0);
    IntVar[] coords_o3 = {X_o3, Y_o3};
    IntVar shape_o3 = new IntVar(store, "shape_o3", 6, 7);
    IntVar start_o3 = new IntVar(store, "start_o3", 10, 10);
    IntVar duration_o3 = new IntVar(store, "duration_o3", 12, 12);
    IntVar end_o3 = new IntVar(store, "end_o3", 22, 22);
    GeostObject o3 = new GeostObject(2, coords_o3, shape_o3, start_o3, duration_o3, end_o3);
    objects.add(o3);

    //  Object o4- shape 9
    List<Dbox> shape9 = new ArrayList<>();
    shape9.add(new Dbox(new int[] {0, 0}, new int[] {1, 4}));
    shapes.add(new Shape(8, shape9));

    IntVar X_o4 = new IntVar(store, "x4", 0, 1);
    IntVar Y_o4 = new IntVar(store, "y4", 0, 1);
    IntVar[] coords_o4 = {X_o4, Y_o4};
    IntVar shape_o4 = new IntVar(store, "shape_o4", 8, 8);
    IntVar start_o4 = new IntVar(store, "start_o4", 14, 14);
    IntVar duration_o4 = new IntVar(store, "duration_o4", 8, 8);
    IntVar end_o4 = new IntVar(store, "end_o4", 22, 22);
    GeostObject o4 = new GeostObject(3, coords_o4, shape_o4, start_o4, duration_o4, end_o4);
    objects.add(o4);

    // dimension 2 must be added so the time dimension is also present.
    int[] dimensions = {0, 1, 2};
    NonOverlapping constraint1 = new NonOverlapping(objects, dimensions);
    constraints.add(constraint1);
    InArea constraint2 = new InArea(new Dbox(new int[] {0, 0}, new int[] {5, 4}), null);
    constraints.add(constraint2);

    Constraint c = new Geost(objects, constraints, shapes);
    store.impose(c);
  }

  /**
   * Executes the search for a solution by checking store consistency.
   *
   * @return true if a solution is found, false otherwise
   */
  @Override
  public boolean search() {

    long t1;
    long t2;
    long t;
    t1 = System.currentTimeMillis();

    boolean result = store.consistency();

    if (result) {
      log.info("*** Yes");
      log.info("{}", store);
    } else {
      log.info("*** No");
    }

    t2 = System.currentTimeMillis();
    t = t2 - t1;
    log.info("\n\t*** Execution time = " + t + " ms");

    return result;
  }
}
