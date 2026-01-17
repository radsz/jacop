package org.jacop;

import org.jacop.constraints.ExtensionalConflictVA;
import org.jacop.constraints.knapsack.Knapsack;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.junit.Test;

public class ConstraintStatusKnownAtImposition {

    @Test
    public void testSimpleFailSetupAtImpositionKnapsack() {

        Store store = new Store();

        IntVar v0 = new IntVar(store, "v0", 1, 1);
        IntVar v1 = new IntVar(store, "v1", 0, 0);
        IntVar v2 = new IntVar(store, "v2", 1, 1);
        IntVar v3 = new IntVar(store, "v3", 0, 0);
        IntVar v4 = new IntVar(store, "v4", 0, 0);

        Knapsack cons = new Knapsack(
                new int[]{1, 2, 3},
                new int[]{1, 2, 3},
                new IntVar[]{v1, v2, v3},
                v4,
                v0);

        store.impose(cons);

    }

    @Test
    public void testSimpleAlreadySatisfiedSetupAtImpositionConflictVA() {
            Store store = new Store ();

            IntVar v1 = new IntVar (store, "v1", 0, 0);
            IntVar v2 = new IntVar (store, "v2", 1, 1);

            ExtensionalConflictVA cons = new ExtensionalConflictVA (
                    new IntVar[] { v1, v2 },
                    new int[][] {
                            new int[] {0, 0},  new int[] {1, 1}
                    }
            );

            store.impose(cons);

            System.out.println(cons);
            System.out.println(store);

            store.consistency();
    }


}
