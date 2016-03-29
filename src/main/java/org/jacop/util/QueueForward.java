package org.jacop.util;

import org.jacop.constraints.Constraint;
import org.jacop.core.Var;

import java.util.*;

/**
 *
 * Utility class that allows for constraints like Xor, Reified, etc that take other constraints
 * as parameters to forward any changes of variables to the constraints that were provided as arguments.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.4
 */
public class QueueForward {

    final public HashMap<Var, List<Constraint>> forwardMap;

    final public boolean isEmpty;

    public QueueForward(Constraint[] constraints, Var[] variables) {

        forwardMap = new HashMap<>();

        for (Var var : variables) {
            forwardMap.put(var, new ArrayList<Constraint>());
            for (Constraint constraint : constraints) {

                if (constraint.arguments().contains(var)) {

                    try {
                        constraint.getClass().getDeclaredMethod("queueVariable", int.class, Var.class);
                        forwardMap.get(var).add(constraint);
                    } catch (NoSuchMethodException e) {
                        // constraint may use empty queueVariable provided by abstract class Constraint
                    }
                }
            }
        }

	for (Var var : variables) {
	    List<Constraint> c =  forwardMap.get(var);

	    if (c == null)
		forwardMap.remove(var);
	    else if (c.isEmpty())
		forwardMap.remove(var);
	}

        isEmpty = forwardMap.isEmpty();

    }

    public QueueForward(Collection<Constraint> constraints, Collection<Var> variables) {
        this(constraints.toArray(new Constraint[constraints.size()]), variables.toArray(new Var[variables.size()]));
    }

    public QueueForward(Constraint constraint, Collection<Var> vars) {
        this(Arrays.asList(constraint), vars);
    }

    public QueueForward(Collection<Constraint> constraints, Var var) {
        this(constraints, Arrays.asList(var));
    }

    public QueueForward(Constraint constraint, Var var) {
        this(Arrays.asList(constraint), Arrays.asList(var));
    }

    public boolean isEmpty() {
        return isEmpty;
    }

    public void queueForward(int level, Var variable) {

        if (isEmpty)
            return;

        List<Constraint> constraints = forwardMap.get(variable);

        if (constraints == null)
            return;

        for (Constraint constraint : constraints) {
            constraint.queueVariable(level, variable);
        }
    }

}
