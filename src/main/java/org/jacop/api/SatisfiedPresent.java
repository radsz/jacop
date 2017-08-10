package org.jacop.api;

/**
 * Author : Radoslaw Szymanek
 * Email : radoslaw.szymanek@osolpro.com
 * <p/>
 * Copyright 2012, All rights reserved.
 */
public interface SatisfiedPresent {

    /**
     * It checks if the constraint is satisfied. It can return false even if constraint
     * is satisfied but not all variables in its scope are grounded. It needs to return
     * true if all variables in its scope are grounded and constraint is satisfied.
     *
     * Implementations of this interface for constraints that are not PrimitiveConstraint
     * may require constraint imposition and consistency check as a requirement to work
     * correctly.
     *
     * @return true if constraint is possible to verify that it is satisfied.
     */
    boolean satisfied();

}
