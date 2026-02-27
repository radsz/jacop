package org.jacop;

import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.ExtensionalConflictVa;
import org.jacop.constraints.knapsack.Knapsack;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.jupiter.api.Test;

@Slf4j
class ConstraintStatusKnownAtImposition {

  @Test
  void testSimpleFailSetupAtImpositionKnapsack() {

    Store store = new Store();

    IntVar v0 = new IntVar(store, "v0", 1, 1);
    IntVar v1 = new IntVar(store, "v1", 0, 0);
    IntVar v2 = new IntVar(store, "v2", 1, 1);
    IntVar v3 = new IntVar(store, "v3", 0, 0);
    IntVar v4 = new IntVar(store, "v4", 0, 0);

    Knapsack cons =
        Knapsack.builder()
            .profits(new int[] {1, 2, 3})
            .weights(new int[] {1, 2, 3})
            .quantity(new IntVar[] {v1, v2, v3})
            .knapsackCapacity(v4)
            .knapsackProfit(v0)
            .build();

    store.impose(cons);
  }

  @Test
  void testSimpleAlreadySatisfiedSetupAtImpositionConflictVA() {
    Store store = new Store();

    IntVar v1 = new IntVar(store, "v1", 0, 0);
    IntVar v2 = new IntVar(store, "v2", 1, 1);

    ExtensionalConflictVa cons =
        new ExtensionalConflictVa(
            new IntVar[] {v1, v2}, new int[][] {new int[] {0, 0}, new int[] {1, 1}});

    store.impose(cons);

    log.info("{}", cons);
    log.info("{}", store);

    store.consistency();
  }
}
