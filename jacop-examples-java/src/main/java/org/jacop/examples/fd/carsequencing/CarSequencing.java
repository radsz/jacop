/*
 * CarSequencing.java
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.examples.fd.carsequencing;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;
import org.jacop.constraints.Constraint;
import org.jacop.constraints.Count;
import org.jacop.constraints.DecomposedConstraint;
import org.jacop.constraints.ExtensionalSupportMdd;
import org.jacop.constraints.Sequence;
import org.jacop.constraints.regular.Regular;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.core.ValueEnumeration;
import org.jacop.examples.fd.ExampleFd;
import org.jacop.util.fsm.Fsm;
import org.jacop.util.fsm.FsmState;
import org.jacop.util.fsm.FsmTransition;

/**
 * It is program to model and solve simple problems of car sequencing problem (CSPLIB-p1).
 *
 * @author Radoslaw Szymanek
 * @version 4.10
 */
public class CarSequencing extends ExampleFd {

  /**
   * It specifies if the slide based decomposition of the regular constraint should be applied. This
   * decomposition uses ternary extensional support constraints. It achieves GAC if Fsm is
   * deterministic.
   */
  public final boolean slideDecomposition = false;

  /** It specifies if the regular constraint should be used. */
  public final boolean regular = true;

  /**
   * It specifies if one extensional constraint based on Mdd created from Fsm should be used. The
   * translation process works if Fsm is deterministic.
   */
  public final boolean extensionalMdd = false;

  /** It specifies number of cars. */
  public int noCar;

  /** It specifies the no of options in the car sequencing problem. */
  public int noOption;

  /** It specifies the number of different car classes. */
  public int noClass;

  /**
   * For a given sequence length then can be different maximum number of cars with a given option.
   */
  public int[] maxNoOfCarsPerOption;

  /** The sequence length for which the maximum number restriction is specified. */
  public int[] blockSizePerOption;

  /** It specifies how many cars of each option should be produced. */
  public int[] noOfCarsPerClass;

  /**
   * It specifies if the given class (the first dimension) requires given option (the second
   * dimension).
   */
  public boolean[][] required;

  /**
   * A simple car sequencing problem.
   *
   * @return problem description.
   */
  public static String[] problem() {
    return new String[] {
      "10 5 6",
      "1 2 1 2 1",
      "2 3 3 5 5",
      "0 1 1 0 1 1 0",
      "1 1 0 0 0 1 0",
      "2 2 0 1 0 0 1",
      "3 2 0 1 0 1 0",
      "4 2 1 0 1 0 0",
      "5 2 1 1 0 0 0"
    };
  }

  /**
   * It transforms string representation of the problem into an array of ints representation. It
   * stores the whole description in the internal attributes.
   *
   * @param description array of strings representing the problem.
   * @param example example in which the passed instance is stored.
   */
  public static void readFromArray(String[] description, CarSequencing example) {

    Pattern pat = Pattern.compile(" ");
    String[] result = pat.split(description[0]);

    example.noCar = Integer.parseInt(result[0]);
    example.noOption = Integer.parseInt(result[1]);
    example.noClass = Integer.parseInt(result[2]);

    result = pat.split(description[1]);

    example.maxNoOfCarsPerOption = new int[example.noOption];

    for (int i = 0; i < result.length; i++) {
      example.maxNoOfCarsPerOption[i] = Integer.parseInt(result[i]);
    }

    result = pat.split(description[2]);

    example.blockSizePerOption = new int[example.noOption];

    for (int i = 0; i < result.length; i++) {
      example.blockSizePerOption[i] = Integer.parseInt(result[i]);
    }

    example.noOfCarsPerClass = new int[example.noClass];
    example.required = new boolean[example.noClass][example.noOption];

    for (int i = 3; i < description.length; i++) {
      // Reading info about each class.

      result = pat.split(description[i]);

      int classNo = Integer.parseInt(result[0]);

      example.noOfCarsPerClass[classNo] = Integer.parseInt(result[1]);

      for (int j = 2; j < result.length; j++) {
        if (Integer.parseInt(result[j]) == 1) {
          example.required[classNo][j - 2] = true;
        }
      }
    }
  }

  /**
   * It creates a String representation of the problem being supplied.
   *
   * @param example example in which the passed instance is stored.
   * @return the string representation of the problem instance.
   */
  public static String[] toStringArray(CarSequencing example) {

    String[] result = new String[example.noClass + 3];

    result[0] = example.noCar + " " + example.noOption + " " + example.noClass;

    StringBuilder resultBuffer = new StringBuilder();

    for (int i = 0; i < example.noOption; i++) {
      resultBuffer.append(example.maxNoOfCarsPerOption[i]).append(" ");
    }

    result[1] = resultBuffer.toString().trim();

    resultBuffer = new StringBuilder();

    for (int i = 0; i < example.noOption; i++) {
      resultBuffer.append(example.blockSizePerOption[i]).append(" ");
    }

    result[2] = resultBuffer.toString().trim();

    for (int i = 0; i < example.noClass; i++) {

      resultBuffer = new StringBuilder();

      resultBuffer.append(i).append(" ");
      resultBuffer.append(example.noOfCarsPerClass[i]);

      for (int j = 0; j < example.noOption; j++) {
        if (example.required[i][j]) {
          resultBuffer.append(" 1");
        } else {
          resultBuffer.append(" 0");
        }
      }

      result[i + 3] = resultBuffer.toString();
    }

    return result;
  }

  /**
   * @param count The number of times a value from yes domain needs to be encountered.
   * @param yes the values which are counted.
   * @param no the values which are not counted.
   * @return Fsm for simple count constraint.
   */
  public static Fsm createFsm(int count, IntervalDomain yes, IntervalDomain no) {

    Fsm result = new Fsm();

    result.initState = new FsmState();
    FsmState currentState = result.initState;

    int current = 0;
    while (current <= count) {

      FsmState nextStateYes = new FsmState();

      if (current < count) {
        currentState.transitions.add(new FsmTransition(yes, nextStateYes));
      }

      for (ValueEnumeration enumer = no.valueEnumeration(); enumer.hasMoreElements(); ) {
        int value = enumer.nextElement();
        IntervalDomain transitionCondition = new IntervalDomain(value, value);
        currentState.transitions.add(new FsmTransition(transitionCondition, currentState));
      }

      result.allStates.add(currentState);

      if (current == count) {
        result.finalStates.add(currentState);
      }

      currentState = nextStateYes;

      current++;
    }

    return result;
  }

  /* @TODO: Add functionality to Fsm to be able to do intersections and use the model below.
   public void modelIntersection() {

    store = new FDstore();
    vars = new ArrayList<Variable>();

    Variable[] cars = new Variable[noCar];

    for (int i = 0; i < noCar; i++) {
      cars[i] = new Variable(store, "car" + (i+1), 0, noClass);
      vars.add(cars[i]);
    }

    ArrayList<Constraint> regulars = new ArrayList<Constraint>();

    for (int i = 0; i < noOption; i++) {

      IntervalDomain classesWithGivenOption = new IntervalDomain();
      for (int j = 0; j < noClass; j++)
        if (required[j][i])
          classesWithGivenOption.addDom(j, j);

      DecomposedConstraint c =
          Sequence.builder()
              .list(cars)
              .set(classesWithGivenOption)
              .q(blockSizePerOption[i])
              .min(0)
              .max(maxNoOfCarsPerOption[i])
              .build();
      ArrayList<Constraint> decomposition = c.decompose(store);

      regulars.addAll(decomposition);

      for (Constraint regular : decomposition)
        store.imposeDecomposition(regular);
    }

    Fsm union = null;

    for (Constraint constraint : regulars)
      if (union == null)
        union = ((Regular) constraint).fsm;
      else
        union = union.union( ((Regular) constraint).fsm );

    System.out.println("Size +++++++++++ " + union.states.size());

    store.impose(new Regular(union, cars));

    for (int i = 0; i < noClass; i++) {

      IntervalDomain yes = new IntervalDomain(i, i);
      IntervalDomain no = new IntervalDomain(0, noClass);
      no = (IntervalDomain) no.subtract(i);

      Fsm counter = createFsm(noOfCarsPerClass[i], yes, no);

      System.out.println( counter );

    // store.impose(new Regular(counter, cars));

      if (i == 0)
        union = counter;
      else
        //union = union.concatenation( counter );
        union = union.union( counter );

      System.out.println("Union +++++++++++ " + union);

    }

    System.out.println(union);

    store.impose(new Regular(union, cars));


  }
   */

  /**
   * It reads the problem description from the file and returns string representation of the
   * problem.
   *
   * @param file the file containing the problem description.
   * @return the problem description
   */
  public static String[] readFile(String file) {

    List<String> result = new ArrayList<>();

    IO.println("readFile(" + file + ")");

    try (BufferedReader inr =
        new BufferedReader(
            new InputStreamReader(new FileInputStream(file), StandardCharsets.UTF_8))) {

      String str;

      while ((str = inr.readLine()) != null && !str.isEmpty()) {

        str = str.trim();

        // ignore comments
        if (str.startsWith("#") || str.startsWith("%")) {
          continue;
        }

        result.add(str);
      } // end while

      // inr.close(); not needed; auto close

    } catch (IOException e) {
      IO.println(e);
    }

    return result.toArray(new String[0]);
  } // end readFile

  /**
   * It executes the program to solve car sequencing problem.
   *
   * @param args parameters (none)
   */
  static void main(String[] args) {

    CarSequencing example = new CarSequencing();

    readFromArray(CarSequencing.problem(), example);

    example.model();

    String[] description = toStringArray(example);

    for (String line : description) {
      IO.println(line);
    }

    example.searchAllAtOnce();
  }

  /**
   * It executes the program to solve car sequencing problem.
   *
   * @param args parameters (none)
   */
  public static void test(String[] args) {

    CarSequencing example = new CarSequencing();

    readFromArray(CarSequencing.problem(), example);

    example.model();

    String[] description = toStringArray(example);

    for (String line : description) {
      IO.println(line);
    }

    example.searchAllAtOnce();

    String[] problemDescription = readFile("ExamplesJaCoP/carSeq1.txt");

    readFromArray(problemDescription, example);
    example.model();

    example.searchLds(3);
  }

  @Override
  public void model() {

    store = new Store();
    vars = new ArrayList<>();

    IntVar[] cars = new IntVar[noCar];

    for (int i = 0; i < noCar; i++) {
      cars[i] = new IntVar(store, "car" + (i + 1), 0, noClass);
      vars.add(cars[i]);
    }

    for (int i = 0; i < noOption; i++) {

      IntervalDomain classesWithGivenOption = new IntervalDomain();
      for (int j = 0; j < noClass; j++) {
        if (required[j][i]) {
          classesWithGivenOption.unionAdapt(j, j);
        }
      }

      // It uses Regular constraint.
      if (regular) {
        store.imposeDecomposition(
            Sequence.builder()
                .list(cars)
                .set(classesWithGivenOption)
                .q(blockSizePerOption[i])
                .min(0)
                .max(maxNoOfCarsPerOption[i])
                .build());
      }

      // It uses decomposition of Regular into ternary constraints.
      if (slideDecomposition) {
        DecomposedConstraint<Constraint> c =
            Sequence.builder()
                .list(cars)
                .set(classesWithGivenOption)
                .q(blockSizePerOption[i])
                .min(0)
                .max(maxNoOfCarsPerOption[i])
                .build();
        List<Constraint> decomposition = c.decompose(store);

        for (Constraint regular : decomposition) {
          store.imposeDecomposition(regular);
        }
      }

      // It uses replacement for Regular, namely one extensional support constraint
      // based on MDDs.
      if (extensionalMdd) {
        DecomposedConstraint<Constraint> c =
            Sequence.builder()
                .list(cars)
                .set(classesWithGivenOption)
                .q(blockSizePerOption[i])
                .min(0)
                .max(maxNoOfCarsPerOption[i])
                .build();
        List<Constraint> decomposition = c.decompose(store);

        for (Constraint constraint : decomposition) {
          Regular regular = (Regular) constraint;
          store.impose(
              new ExtensionalSupportMdd(regular.fsm.transformDirectlyIntoMdd(regular.list)));
        }
      }
    }

    for (int i = 0; i < noClass; i++) {

      IntVar counter = new IntVar(store, "counter" + i, noOfCarsPerClass[i], noOfCarsPerClass[i]);

      store.impose(new Count(cars, counter, i));

      // Possible replacement for Count constraint.

    }
  }
}
