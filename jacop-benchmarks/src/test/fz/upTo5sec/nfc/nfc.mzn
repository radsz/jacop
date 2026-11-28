include "network_flow.mzn";

% instance data
int: n_periods;
int: shift_periods;
set of int: Periods = 0..n_periods - 1;
array[Periods] of int: worker_count;

% solution
array[Periods] of var 0..max(worker_count): w;
array[Periods] of var 0..max(worker_count): f;

var 0..n_periods * max(worker_count): objective;

constraint forall (t in Periods) (w[t] >= worker_count[t]);

constraint network_flow_cost(
  array2d(
    1..2 * n_periods,
    1..2,
    [
      1 + (i + j) mod n_periods
    | i in Periods,
      j in 0..1 % 0 = tail, 1 = head
    ] ++
    [
      1 + (i + (n_periods - shift_periods) * j) mod n_periods
    | i in Periods,
      j in 0..1 % 0 = tail, 1 = head
    ]
  ), % arc
  [0 | t in Periods], % balance
  [1 | i in Periods] ++
  [0 | i in Periods], % weight
  array1d(1..n_periods, w) ++ array1d(1..n_periods, f), % flow
  objective % cost
);

constraint forall (t in 0..n_periods - 1) (
  w[t] = sum (i in 1..shift_periods) (f[(t + i) mod n_periods])
);

solve
    :: seq_search([
        int_search([w[i] | i in Periods], first_fail, indomain_split, complete),
        int_search([f[i] | i in Periods], first_fail, indomain_split, complete),
        int_search([objective], input_order, indomain_min, complete)
    ])
    minimize objective;

output [
    "w = array1d(\(Periods), \(w));\n",
    "f = array1d(\(Periods), \(f));\n",
    "objective = \(objective);\n"
];

