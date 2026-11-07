int: P; % Number of Periods
int: T; % Trucks
array[1..P] of int: Demand;
array[1..T] of int: Cost;
array[1..T] of int: Loads;
array[1..T] of int: Limit;
array[1..P] of var set of 1..T: x;

constraint forall(p in 1..P)(
    sum(t in 1..T)( Loads[t] * bool2int(t in x[p])) >= Demand[p]);

constraint
    forall(t in 1..T)(
        forall(tau in 1..P-Limit[t]+1)(
            sum(p in tau..tau+Limit[t]-1)( bool2int(t in x[p]) ) <= 1
    ));

solve :: set_search(x, first_fail, indomain, complete)
    minimize sum(p in 1..P)(sum(t in 1..T)( Cost[t] * bool2int(t in x[p]) ));
