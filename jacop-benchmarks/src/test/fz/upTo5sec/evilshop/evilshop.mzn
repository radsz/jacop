%------------------------------------------------------------------------%
% Evil Job-Shop Scheduling
%------------------------------------------------------------------------%
%
% This is a classic job-shop scheduling problem, with a few twists to make
% it more evil:
%  * It uses the cumulative scheduling constraint. This is not evil by itself,
%    after all it enables solvers to use global scheduling propagators.
%  * Instead of a resource with capacity 1 and tasks that use capacity 1,
%    the capacity is left as a variable, and the tasks use more than half
%    of the possible maximum capacity (so it is again a disjunctive problem).
%  * The start times are scaled up, which makes decomposition of cumulative
%    difficult if it is based on all possible time points.
%
%------------------------------------------------------------------------%


include "globals.mzn";



%%%%%%%%% Input

int: n_jobs;
int: n_machines;
array[1..n_jobs,1..2*n_machines] of int: input;

%%%%%%%%% Degree of evilness

int: scale = 97;
var 0..10000: capacity;
int: maxusage = (ub(capacity)*2) div 3;
int: minusage = ub(capacity) div 2;

% int: scale = 1;
% var 1..1: capacity;
% int: maxusage = 1;
% int: minusage = 1;

%%%%%%%%% Preprocess input

array[1..n_jobs,1..n_machines] of int: machine =
    array2d(1..n_jobs,1..n_machines,
        [input[i,2*j-1] | i in 1..n_jobs, j in 1..n_machines]);

int: mindur = min (i in 1..n_jobs, j in 1..n_machines) (scale*input[i,2*j]);
int: maxdur = max (i in 1..n_jobs, j in 1..n_machines) (scale*input[i,2*j]);

int: lst =
    sum (i in 1..n_jobs, j in 1..n_machines) (scale*input[i,2*j]);
int: lct = lst+max (i in 1..n_jobs, j in 1..n_machines)
    (scale*input[i,2*j]);

%%%%%%%%% Model

array[1..n_jobs,1..n_machines] of var 0..lst: start;

array[1..n_jobs,1..n_machines] of var mindur..maxdur: duration;

constraint forall (i in 1..n_jobs, j in 1..n_machines) (
        duration[i,j] >= scale*input[i,2*j]
    /\  duration[i,j] < (scale+1)*input[i,2*j]
    );

constraint forall (i in 1..n_jobs, j in 1..n_machines) (
        start[i,j] mod scale = 0
    );

constraint
    forall (i in 1..n_jobs, j in 1..n_machines-1) (
        start[i,j] + duration[i,j] <= start[i,j+1]
    )
/\  forall (m in 0..n_machines-1) (let {
        array[1..n_jobs] of var int: sm =
            [start[i,j] | i in 1..n_jobs, j in 1..n_machines 
                          where machine[i,j]=m],
        array[1..n_jobs] of var int: dm =
            [duration[i,j] | i in 1..n_jobs, j in 1..n_machines 
                          where machine[i,j]=m],
        array[2..n_jobs] of var maxusage..ub(capacity): usage,
        var minusage..ub(capacity): mu
        } in
        cumulative(sm,dm,[mu]++usage,capacity)
    )
    ;

var 0..lct: objective =
    max (i in 1..n_jobs) (start[i,n_machines]+duration[i,n_machines]);

solve
    ::int_search([start[i,j]| j in 1..n_machines, i in 1..n_jobs],
                 input_order,indomain_split,complete)
    minimize objective;

output [
    "start = ", show(start), "\n",
    "objective = ", show(objective), "\n"
]; 
