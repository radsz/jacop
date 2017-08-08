package org.jacop.api;

/**
 * Author : Radoslaw Szymanek
 * Email : radoslaw.szymanek@osolpro.com
 * <p/>
 * Copyright 2012, All rights reserved.
 */
public interface Stateful {

    /**
     * This function is called in case of the backtrack, so a constraint can
     * clear the queue of changed variables which is no longer valid. This
     * function is called *before* all timestamps, variables, mutablevariables
     * have reverted to their previous value.
     *
     * @param level the level which is being removed.
     */
    void removeLevel(int level);

}
