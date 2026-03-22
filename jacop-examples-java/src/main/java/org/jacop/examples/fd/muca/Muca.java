/*
 * Muca.java
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

package org.jacop.examples.fd.muca;

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.StringTokenizer;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.Among;
import org.jacop.constraints.ExtensionalSupportVa;
import org.jacop.constraints.IfThen;
import org.jacop.constraints.SumInt;
import org.jacop.constraints.XeqC;
import org.jacop.constraints.XgteqC;
import org.jacop.constraints.XplusYgtC;
import org.jacop.core.IntVar;
import org.jacop.core.IntervalDomain;
import org.jacop.core.Store;
import org.jacop.examples.fd.ExampleFd;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.MaxRegret;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * It solves the Mixed Multi-Unit Combinatorial Auctions.
 *
 * <p>The idea originated from reading the following paper where the first attempt to use CP was
 * presented.
 *
 * <p>Comparing Winner Determination Algorithms for Mixed Multi-Unit Combinatorial Auctions by
 * Brammert Ottens Ulle Endriss
 *
 * @author Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class Muca extends ExampleFd {

  private static final Logger log = LoggerFactory.getLogger(Muca.class);

  /** It specifies the minimal value for the cost. */
  public final int minCost = -100000;

  /** It specifies the maximal value for the cost. */
  public final int maxCost = 100000;

  /** The maximal number of products. */
  public final int maxProducts = 100;

  /**
   * ArrayList of bids issued by different bidders. Each bidder issues an ArrayList of xor bids.
   * Each Xor bid is a list of transformations.
   */
  public List<List<List<Transformation>>> bids;

  /** For each bidder and each xor bid there is an integer representing a cost of the xor bid. */
  public List<List<Integer>> costs;

  /** It specifies the initial quantities of goods. */
  public List<Integer> initialQuantity;

  /** It specifies the minimal quantities of items seeked to achieve. */
  public List<Integer> finalQuantity;

  /** It specifies number of goods which are in the focus of the auction. */
  public int noGoods = 7;

  /** It specifies the minimal possible delta of goods for any transformation. */
  public int minDelta = -10;

  /** It specifies the maximal possible delta of goods for any transformation. */
  public int maxDelta = 10;

  /** For each bidder it specifies variable representing the cost of the chosen xor bid. */
  public List<IntVar> bidCosts;

  /** It specifies the sequence of transitions used by an auctioneer. */
  public IntVar[] transitions;

  /** It specifies the maximal number of transformations used by the auctioneer. */
  public int maxNoTransformations;

  /**
   * For each transition and each good it specifies the delta change of that good before the
   * transition takes place.
   */
  public IntVar[][] deltasI;

  /**
   * For each transition and each good it specifies the delta change of that good after the
   * transition takes place.
   */
  public IntVar[][] deltasO;

  /** It specifies the number of goods after the last transition. */
  public IntVar[] sum;

  /** It reads auction problem description from the file. */
  public String filename = "src/main/java/org/jacop/examples/fd/muca/testset3.auct";

  /**
   * It executes the program which solve the supplied auction problem or solves three problems
   * available within the files.
   *
   * @param args the first argument specifies the name of the file containing the problem
   *     description.
   */
  void main(String[] args) {
    if (args == null) {
      throw new IllegalArgumentException("args must not be null");
    }
    Muca problem = new Muca();

    if (args.length > 0) {
      problem.filename = args[0];

      problem.model();

      problem.searchSpecial();

      return;
    }

    problem.model();
    problem.searchSpecial();

    problem = new Muca();
    problem.filename = "src/main/java/org/jacop/examples/fd/muca/testset1.auct";
    problem.model();
    problem.searchSpecial();

    problem = new Muca();
    problem.filename = "src/main/java/org/jacop/examples/fd/muca/testset2.auct";
    problem.model();
    problem.searchSpecial();
  }

  /** It creates an instance of the auction problem. */
  public void setupProblem1() {
    bids = new ArrayList<>();

    Transformation t1 = new Transformation(List.of(3, 10), new Delta(0, 1), new Delta(5, 0));
    Transformation t2 =
        new Transformation(List.of(4, 10, 11), new Delta(0, 2), new Delta(2, 0), new Delta(2, 0));
    bids.add(List.of(List.of(t1, t2)));

    Transformation t3 =
        new Transformation(List.of(5, 11, 12), new Delta(0, 1), new Delta(1, 0), new Delta(1, 1));
    Transformation t4 =
        new Transformation(
            List.of(6, 11, 12, 13),
            new Delta(0, 2),
            new Delta(2, 0),
            new Delta(2, 0),
            new Delta(2, 0));
    Transformation t5 =
        new Transformation(List.of(7, 12, 13), new Delta(1), new Delta(-1), new Delta(-1));
    bids.add(List.of(List.of(t3, t4, t5)));

    Transformation t6 =
        new Transformation(List.of(8, 13, 14), new Delta(2), new Delta(-2), new Delta(-2));
    Transformation t7 =
        new Transformation(List.of(9, 13, 14), new Delta(2), new Delta(-3), new Delta(-10));
    bids.add(List.of(List.of(t6, t7)));

    Transformation t8 =
        new Transformation(List.of(0, 3, 4), new Delta(1), new Delta(-1), new Delta(-1));
    bids.add(List.of(List.of(t8)));

    Transformation t9 =
        new Transformation(
            List.of(1, 5, 6, 7), new Delta(4), new Delta(-1), new Delta(-2), new Delta(-1));
    bids.add(List.of(List.of(t9)));

    Transformation t10 =
        new Transformation(List.of(2, 8, 9), new Delta(1), new Delta(-1), new Delta(-1));
    bids.add(List.of(List.of(t10)));

    Transformation t11 =
        new Transformation(List.of(5, 11, 12), new Delta(1), new Delta(-1), new Delta(-1));
    Transformation t12 =
        new Transformation(
            List.of(6, 11, 12, 13), new Delta(2), new Delta(-2), new Delta(-2), new Delta(-2));
    Transformation t13 =
        new Transformation(List.of(7, 12, 13), new Delta(1), new Delta(-1), new Delta(-1));
    bids.add(List.of(List.of(t11, t12, t13)));

    Transformation t14 =
        new Transformation(
            List.of(1, 5, 6, 7), new Delta(4), new Delta(-1), new Delta(-2), new Delta(-1));
    bids.add(List.of(List.of(t14)));

    initialQuantity = new ArrayList<>(List.of(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 4, 3));
    finalQuantity = new ArrayList<>(List.of(0, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0));

    costs = new ArrayList<>();
    addBidCost(-10);
    addBidCost(-20);
    addBidCost(25);
    addBidCost(-30);
    addBidCost(35);
    addBidCost(-32);
    addBidCost(-15);
    addBidCost(-30);
  }

  /** It creates an instance of the auction problem. */
  public void setupProblem2() {
    bids = new ArrayList<>();

    Transformation t1 =
        new Transformation(List.of(3, 0, 1), new Delta(1), new Delta(-1), new Delta(-1));
    Transformation t2 =
        new Transformation(
            List.of(4, 0, 1, 2), new Delta(2), new Delta(-2), new Delta(-2), new Delta(-2));
    Transformation t3 =
        new Transformation(List.of(5, 1, 2), new Delta(1), new Delta(-1), new Delta(-1));
    bids.add(List.of(List.of(t1, t2, t3)));

    Transformation t4 =
        new Transformation(
            List.of(6, 3, 4, 5), new Delta(4), new Delta(-1), new Delta(-2), new Delta(-1));
    bids.add(List.of(List.of(t4)));

    Transformation t5 =
        new Transformation(List.of(3, 0, 1), new Delta(1), new Delta(-1), new Delta(-1));
    Transformation t6 =
        new Transformation(
            List.of(4, 0, 1, 2), new Delta(2), new Delta(-2), new Delta(-2), new Delta(-2));
    Transformation t7 =
        new Transformation(List.of(5, 1, 2), new Delta(1), new Delta(-1), new Delta(-1));
    bids.add(List.of(List.of(t5, t6, t7)));

    Transformation t8 =
        new Transformation(
            List.of(6, 3, 4, 5), new Delta(4), new Delta(-1), new Delta(-2), new Delta(-1));
    bids.add(List.of(List.of(t8)));

    initialQuantity = new ArrayList<>(List.of(3, 4, 3, 0, 0, 0, 0));
    finalQuantity = new ArrayList<>(List.of(0, 0, 0, 0, 0, 0, 4));

    costs = new ArrayList<>();
    addBidCost(-20);
    addBidCost(-35);
    addBidCost(-15);
    addBidCost(-30);
  }

  /** It creates an instance of the auction problem. */
  public void setupProblem3() {
    bids = new ArrayList<>();

    Transformation t1 = new Transformation(List.of(0, 1), new Delta(-1), new Delta(1));
    Transformation t2 = new Transformation(List.of(2, 3), new Delta(-1), new Delta(1));
    bids.add(List.of(List.of(t1, t2)));

    Transformation t4 = new Transformation(List.of(0, 1), new Delta(-1), new Delta(1));
    Transformation t5 = new Transformation(List.of(2, 3), new Delta(-1), new Delta(1));
    bids.add(List.of(List.of(t4, t5)));

    Transformation t3 = new Transformation(List.of(1, 2), new Delta(-1), new Delta(1));
    bids.add(List.of(List.of(t3)));

    initialQuantity = new ArrayList<>(List.of(1, 0, 0, 0));
    finalQuantity = new ArrayList<>(List.of(0, 0, 0, 1));

    costs = new ArrayList<>();
    addBidCost(-5);
    addBidCost(-8);
    addBidCost(-2);
  }

  /** It creates an instance of the auction problem. */
  public void setupProblem4() {
    noGoods = 4;
    bids = new ArrayList<>();

    Transformation t1 = new Transformation(List.of(0, 1), new Delta(-1), new Delta(1));
    Transformation t2 = new Transformation(List.of(2, 3), new Delta(-1), new Delta(1));
    Transformation t4 = new Transformation(List.of(0, 1), new Delta(-1), new Delta(1));
    Transformation t5 = new Transformation(List.of(2, 3), new Delta(-1), new Delta(1));
    bids.add(List.of(List.of(t1, t2), List.of(t4, t5)));

    Transformation t3 = new Transformation(List.of(1, 2), new Delta(-1), new Delta(1));
    bids.add(List.of(List.of(t3)));

    initialQuantity = new ArrayList<>(List.of(1, 0, 0, 0));
    finalQuantity = new ArrayList<>(List.of(0, 0, 0, 1));

    costs = new ArrayList<>();
    addBidCost(-5, -8);
    addBidCost(-2);
  }

  private void addBidCost(int... values) {
    List<Integer> costList = new ArrayList<>();
    for (int v : values) {
      costList.add(v);
    }
    costs.add(costList);
  }

  @Override
  public void model() {

    readAuction(filename);

    store = new Store();

    int noAvailableTransformations = computeMaxNoTransformations();

    IntVar[] usedTransformation = createTransitionsAndAmong(noAvailableTransformations);

    createBidCostsAndExtensional(usedTransformation);

    createDeltasAndPartialSums();

    createWeightsAndSum(usedTransformation);

    cost = new IntVar(store, "cost", minCost, maxCost);

    store.impose(new SumInt(bidCosts, "==", cost));
  }

  private int computeMaxNoTransformations() {
    maxNoTransformations = 0;
    int noAvailableTransformations = 0;
    for (List<List<Transformation>> bid : bids) {
      int max = 0;
      for (List<Transformation> bid_xor : bid) {
        noAvailableTransformations += bid_xor.size();
        if (bid_xor.size() > max) {
          max = bid_xor.size();
        }
      }
      maxNoTransformations += max;
    }
    return noAvailableTransformations;
  }

  private IntVar[] createTransitionsAndAmong(int noAvailableTransformations) {
    transitions = new IntVar[maxNoTransformations];
    for (int i = 0; i < maxNoTransformations; i++) {
      transitions[i] = new IntVar(store, "t" + (i + 1), 0, noAvailableTransformations);
    }
    for (int i = 0; i < maxNoTransformations - 1; i++) {
      store.impose(new IfThen(new XeqC(transitions[i], 0), new XeqC(transitions[i + 1], 0)));
    }
    IntVar[] usedTransformation = new IntVar[noAvailableTransformations];
    for (int i = 0; i < noAvailableTransformations; i++) {
      usedTransformation[i] = new IntVar(store, "isUsed_" + (i + 1), 0, 1);
      IntervalDomain kSet = new IntervalDomain(i + 1, i + 1);
      store.impose(new Among(transitions, kSet, usedTransformation[i]));
    }
    return usedTransformation;
  }

  private void createBidCostsAndExtensional(IntVar[] usedTransformation) {
    int noTransformations = 0;
    int no = 0;
    bidCosts = new ArrayList<>();
    for (List<List<Transformation>> bid : bids) {
      IntVar[] nVars = new IntVar[bid.size() + 1];
      int[][] tuples = new int[bid.size() + 1][];
      tuples[0] = new int[bid.size() + 1];
      int i = 0;
      for (List<Transformation> bid_xor : bid) {
        IntervalDomain kSet = new IntervalDomain();
        List<IntVar> xorUsedTransformation = new ArrayList<>();
        for (Transformation t : bid_xor) {
          noTransformations++;
          t.id = noTransformations;
          kSet.unionAdapt(noTransformations, noTransformations);
          xorUsedTransformation.add(usedTransformation[t.id - 1]);
        }
        IntVar n = new IntVar(store, "ind_" + no + "_" + i);
        n.addDom(0, 0);
        n.addDom(bid_xor.size(), bid_xor.size());
        store.impose(new SumInt(xorUsedTransformation, "==", n));
        nVars[++i] = n;
        tuples[i] = new int[bid.size() + 1];
        tuples[i][0] = costs.get(no).get(i - 1);
        tuples[i][i] = n.max();
        store.impose(new Among(transitions, kSet, n));
      }
      IntVar bidCost = new IntVar(store, "bidCost" + (bidCosts.size() + 1), minCost, maxCost);
      nVars[0] = bidCost;
      store.impose(new ExtensionalSupportVa(nVars, tuples));
      bidCosts.add(bidCost);
      no++;
    }
  }

  private void createDeltasAndPartialSums() {
    deltasI = new IntVar[maxNoTransformations][noGoods];
    deltasO = new IntVar[maxNoTransformations][noGoods];
    sum = new IntVar[noGoods];
    for (int g = 0; g < noGoods; g++) {
      List<int[]> tuples4transitions = new ArrayList<>();
      tuples4transitions.add(new int[] {0, 0, 0});
      for (List<List<Transformation>> bid : bids) {
        for (List<Transformation> bid_xor : bid) {
          for (Transformation t : bid_xor) {
            tuples4transitions.add(new int[] {t.id, -t.getDeltaInput(g), t.getDeltaOutput(g)});
          }
        }
      }
      int[][] tuples = new int[tuples4transitions.size()][];
      for (int i = 0; i < tuples4transitions.size(); i++) {
        tuples[i] = tuples4transitions.get(i);
      }
      IntVar previousPartialSum =
          new IntVar(store, "initialQuantity_" + g, initialQuantity.get(g), initialQuantity.get(g));
      for (int i = 0; i < maxNoTransformations; i++) {
        List<IntVar> vars = new ArrayList<>();
        vars.add(transitions[i]);
        deltasI[i][g] = new IntVar(store, "deltaI_g" + g + "t" + i, minDelta, maxDelta);
        vars.add(deltasI[i][g]);
        deltasO[i][g] = new IntVar(store, "deltaO_g" + g + "t" + i, minDelta, maxDelta);
        vars.add(deltasO[i][g]);
        store.impose(new ExtensionalSupportVa(vars, tuples));
        store.impose(new XplusYgtC(previousPartialSum, deltasI[i][g], -1));
        IntVar partialSum = new IntVar(store, "partialSum_" + g + "_" + i, 0, maxProducts);
        store.impose(
            new SumInt(
                new IntVar[] {previousPartialSum, deltasI[i][g], deltasO[i][g]}, "==", partialSum));
        previousPartialSum = partialSum;
      }
      store.impose(new XgteqC(previousPartialSum, finalQuantity.get(g)));
      sum[g] = previousPartialSum;
    }
  }

  private void createWeightsAndSum(IntVar[] usedTransformation) {
    for (int g = 0; g < noGoods; g++) {
      IntVar[] weights = new IntVar[usedTransformation.length + 1];
      weights[0] =
          new IntVar(
              store,
              initialQuantity.get(g) + "of-g" + g,
              initialQuantity.get(g),
              initialQuantity.get(g));
      for (List<List<Transformation>> bid : bids) {
        for (List<Transformation> bid_xor : bid) {
          for (Transformation t : bid_xor) {
            if (t.getDelta(g) >= 0) {
              weights[t.id] = new IntVar(store, "delta_tid_" + t.id + "_g" + g, 0, t.getDelta(g));
            } else {
              weights[t.id] = new IntVar(store, "delta_t" + t.id + "_g" + g, t.getDelta(g), 0);
            }
            int[][] tuples = new int[2][2];
            tuples[0][0] = 0;
            tuples[0][1] = 0;
            tuples[1][0] = 1;
            tuples[1][1] = t.getDelta(g);
            IntVar[] vars = {usedTransformation[t.id - 1], weights[t.id]};
            store.impose(new ExtensionalSupportVa(vars, tuples));
          }
        }
      }
      store.impose(new SumInt(weights, "==", sum[g]));
    }
  }

  /**
   * It executes special master-slave search. The master search uses costs variables and maxregret
   * criteria to choose an interesting bids. The second search (slave) looks for the sequence of
   * chosen transactions such as that all constraints concerning goods quantity (deltas of
   * transitions) are respected.
   *
   * @return true if there is a solution, false otherwise.
   */
  public boolean searchSpecial() {

    Search<IntVar> search1 = new DepthFirstSearch<>();
    SelectChoicePoint<IntVar> select1 =
        new SimpleSelect<>(bidCosts.toArray(new IntVar[1]), new MaxRegret<>(), new IndomainMin<>());

    Search<IntVar> search2 = new DepthFirstSearch<>();
    SelectChoicePoint<IntVar> select2 = new SimpleSelect<>(transitions, null, new IndomainMin<>());

    search1.addChildSearch(search2);
    search2.setSelectChoicePoint(select2);

    boolean result = search1.labeling(store, select1, cost);

    printSearchSpecialTransitions();
    printSearchSpecialGoods();

    return result;
  }

  private void printSearchSpecialTransitions() {
    IO.print("\t");
    for (int i = 0; i < maxNoTransformations && transitions[i].value() != 0; i++) {
      IO.print(transitions[i] + "\t");
    }
    log.info("");
  }

  private void printSearchSpecialGoods() {
    for (int g = 0; g < noGoods; g++) {
      IO.print(initialQuantity.get(g) + "\t");
      for (int i = 0; i < maxNoTransformations && transitions[i].value() != 0; i++) {
        IO.print(deltasI[i][g].value() + "," + deltasO[i][g].value() + "\t");
      }
      log.info(sum[g].value() + ">=" + finalQuantity.get(g));
    }
  }

  /**
   * It reads the auction problem from the file.
   *
   * @param filename file describing the auction problem.
   */
  public void readAuction(String filename) {

    noGoods = 0;

    try (BufferedReader br =
        new BufferedReader(
            new InputStreamReader(new FileInputStream(filename), StandardCharsets.UTF_8))) {

      readInitialQuantity(br);
      readFinalQuantity(br);

      bids = new ArrayList<>();
      bids.add(new ArrayList<>());
      bids.getFirst().add(new ArrayList<>());

      String line = br.readLine();
      int bidCounter = 1;
      int bidXorCounter = 1;
      int transformationCounter = 0;

      while (!"price".equals(line)) {
        int[] next =
            readOneTransformationLine(line, bidCounter, bidXorCounter, transformationCounter);
        bidCounter = next[0];
        bidXorCounter = next[1];
        transformationCounter = next[2];
        line = br.readLine();
      }

      readCosts(br, br.readLine());

    } catch (FileNotFoundException ex) {
      log.error("You need to run this program in a directory that contains the required file.", ex);
      throw new RuntimeException(
          "You need to run this program in a directory that contains the "
              + "required file : "
              + filename);
    } catch (IOException ex) {
      log.error("Exception occurred", ex);
    }

    log.info("{}", this.maxCost);
    log.info("{}", this.maxDelta);
    log.info("{}", this.minDelta);
  }

  private void readInitialQuantity(BufferedReader br) throws IOException {
    String line = br.readLine();
    StringTokenizer tk = new StringTokenizer(line, "(),: ");
    initialQuantity = new ArrayList<>();
    while (tk.hasMoreTokens()) {
      noGoods++;
      tk.nextToken();
      initialQuantity.add(Integer.parseInt(tk.nextToken()));
    }
  }

  private void readFinalQuantity(BufferedReader br) throws IOException {
    String line = br.readLine();
    StringTokenizer tk = new StringTokenizer(line, "(),: ");
    finalQuantity = new ArrayList<>();
    while (tk.hasMoreTokens()) {
      tk.nextToken();
      finalQuantity.add(Integer.parseInt(tk.nextToken()));
    }
  }

  /**
   * Returns int[] { bidCounter, bidXorCounter, transformationCounter } after processing one line.
   */
  private int[] readOneTransformationLine(
      String line, int bidCounter, int bidXorCounter, int transformationCounter) {
    StringTokenizer tk = new StringTokenizer(line, "():, ");
    transformationCounter++;

    if (Integer.parseInt(tk.nextToken()) > bidCounter) {
      bidCounter++;
      bidXorCounter = 1;
      transformationCounter = 1;
      bids.add(new ArrayList<>());
      bids.get(bidCounter - 1).add(new ArrayList<>());
    }
    if (Integer.parseInt(tk.nextToken()) > bidXorCounter) {
      bidXorCounter++;
      transformationCounter = 1;
      bids.get(bidCounter - 1).add(new ArrayList<>());
    }
    tk.nextToken();
    bids.get(bidCounter - 1).get(bidXorCounter - 1).add(new Transformation());
    Transformation t =
        bids.get(bidCounter - 1).get(bidXorCounter - 1).get(transformationCounter - 1);
    t.goodsIds = new ArrayList<>();
    t.delta = new ArrayList<>();

    int[] input = new int[noGoods];
    int[] output = new int[noGoods];
    int goodsCounter = 0;
    while (tk.hasMoreTokens()) {
      goodsCounter++;
      if (goodsCounter <= noGoods) {
        int id = Integer.parseInt(tk.nextToken()) - 1;
        int in = Integer.parseInt(tk.nextToken());
        input[id] = in;
      } else {
        int id = Integer.parseInt(tk.nextToken()) - 1;
        int out = Integer.parseInt(tk.nextToken());
        output[id] = out;
      }
    }

    addTransformationDeltas(bidCounter, bidXorCounter, transformationCounter, input, output);
    IO.print("\n");
    return new int[] {bidCounter, bidXorCounter, transformationCounter};
  }

  private void addTransformationDeltas(
      int bidCounter, int bidXorCounter, int transformationCounter, int[] input, int[] output) {
    Transformation t =
        bids.get(bidCounter - 1).get(bidXorCounter - 1).get(transformationCounter - 1);
    for (int i = 0; i < noGoods; i++) {
      if (output[i] > maxDelta) {
        maxDelta = output[i];
      } else if (-input[i] < minDelta) {
        minDelta = -input[i];
      }
      if (output[i] != 0 || input[i] != 0) {
        t.goodsIds.add(i);
        t.delta.add(new Delta(input[i], output[i]));
      }
    }
  }

  private void readCosts(BufferedReader br, String line) throws IOException {
    costs = new ArrayList<>();
    costs.add(new ArrayList<>());
    int bidCounter = 1;
    while (line != null) {
      StringTokenizer tk = new StringTokenizer(line, "(): ");
      if (Integer.parseInt(tk.nextToken()) > bidCounter) {
        bidCounter++;
        costs.add(new ArrayList<>());
      }
      tk.nextToken();
      costs.get(bidCounter - 1).add(Integer.parseInt(tk.nextToken()));
      line = br.readLine();
    }
  }

  static class Delta {

    // Both must be positive, even if input means consuming.

    public final int input;
    public final int output;

    public Delta(int input, int output) {

      this.input = input;
      this.output = output;
    }

    // negative means consumption, positive means production.
    public Delta(int delta) {
      if (delta > 0) {
        input = 0;
        output = delta;
      } else {
        input = -delta;
        output = 0;
      }
    }
  }

  static class Transformation {

    public List<Integer> goodsIds;
    public List<Delta> delta;
    public int id;

    /** Default constructor for programmatic building (used by readAuction). */
    Transformation() {}

    /** Convenience constructor for compact problem setup. */
    Transformation(List<Integer> goodsIds, Delta... deltas) {
      this.goodsIds = new ArrayList<>(goodsIds);
      this.delta = new ArrayList<>(List.of(deltas));
    }

    private int findGoodIndex(int goodId) {
      for (int i = 0; i < goodsIds.size(); i++) {
        if (goodsIds.get(i) == goodId) {
          return i;
        }
      }
      return -1;
    }

    public int getDelta(int goodId) {
      int i = findGoodIndex(goodId);
      return i >= 0 ? delta.get(i).output - delta.get(i).input : 0;
    }

    public int getDeltaInput(int goodId) {
      int i = findGoodIndex(goodId);
      return i >= 0 ? delta.get(i).input : 0;
    }

    public int getDeltaOutput(int goodId) {
      int i = findGoodIndex(goodId);
      return i >= 0 ? delta.get(i).output : 0;
    }
  }
}
