%------------------------------------------------------------------------------%
% Includes

include "inverse.mzn";

%------------------------------------------------------------------------------%
% Parameters

int: n;                             % Number of visits
set of int: VISIT = 1..n;
set of int: VISIT1 = 1..n+1;
array[VISIT] of int: D;             % Duration of the visit 

int: q;                             % Number of precedences
set of int: PREC = 1..q;
array[PREC,1..2] of VISIT: prec;    % prec[i][1] is before prec[i][2]

int: steps;                         % Number of time steps
int: l;                             % Travel time granularity
int: H = steps * l - 1;             % Time horizon;
set of int: TIME = 0..H;

int: r;                                 % Number of forbidden regions
set of int: FORBID = 1..r;
array[FORBID] of VISIT: which;          % which visit is forbidden
array[FORBID,1..2] of TIME: interval;   % in between which times

array[VISIT1,VISIT1,0..steps] of int: T;    % time travel matrix

%------------------------------------------------------------------------------%
% Variables

array[VISIT1] of var VISIT1: position;
array[VISIT1] of var VISIT1: next;
array[VISIT1] of var VISIT1: prev;
array[VISIT1] of var TIME: tvar;

var TIME: objective;
constraint objective = tvar[n+1];

    % NOTE atposition variables only for search!
    %
array[VISIT1] of var VISIT1: atposition;

%------------------------------------------------------------------------------%
% Consistency checks

constraint forall(i in FORBID)(
    assert(
        interval[i,1] <= interval[i,2],
        "forbidden interval \(i) is incorrect [\(interval[i,1])..\(interval[i,2])"
    )
); 

%------------------------------------------------------------------------------%
% Constraints

constraint inverse(next,prev);
constraint position[1] = 1;
constraint position[n+1] = n+1;
constraint tvar[1] = 0;
constraint prev[1] = n+1 /\ next[n+1] = 1;

    % proper tour
    %
constraint forall(i in VISIT1)(next[i] != i /\ prev[i] != i);

    % relation between next and prev and position
    %
constraint forall(i in VISIT)(position[next[i]] = position[i] + 1); 
constraint forall(i in 2..n+1)(position[i] = position[prev[i]] + 1);

    % travel time constraints (using prev)
    %
constraint forall(i in 2..n+1)(
    tvar[i] >= tvar[prev[i]] + D[prev[i]] + T[prev[i],i,tvar[prev[i]] div l]
);

    % travel time constraints (using next)
    %
constraint forall(i in 1..n)(
    tvar[next[i]] >= tvar[i] + D[i] + T[i,next[i],tvar[i] div l]
);

    % precedence constraints
    %
constraint forall(i in PREC)(
    tvar[prec[i,1]] + D[prec[i,1]] <= tvar[prec[i,2]]
);

    % forbidden times
    %
constraint forall(i in FORBID)(
    tvar[which[i]] + D[which[i]] <= interval[i,1] 
\/  tvar[which[i]] >= interval[i,2]
); 

    % redundant constraints about last time
    %
constraint redundant_constraint(
    tvar[n+1] >= sum(D) + sum(i in VISIT)(T[i,next[i],tvar[i] div l])
);
constraint redundant_constraint(
    tvar[n+1] >= sum(D) + sum(i in 2..n+1)(T[prev[i],i,tvar[prev[i]] div l])
);

%------------------------------------------------------------------------------%
% Redundant constraints regarding the search variables

constraint redundant_constraint(inverse(position,atposition));
constraint redundant_constraint(atposition[1] = 1);
constraint redundant_constraint(atposition[n+1] = n+1);
constraint redundant_constraint(
    forall(j in VISIT)(next[atposition[j]] = atposition[j+1])
);
constraint redundant_constraint(
    forall(j in VISIT)(prev[atposition[j+1]] = atposition[j])
);

%------------------------------------------------------------------------------%
% Search and solve item

solve 
        % search first fix the positions in order, then the times?
        %
    :: seq_search([
        int_search(atposition, input_order, indomain_min, complete),
        int_search(tvar, smallest, indomain_min, complete)
    ])
    minimize objective;

%------------------------------------------------------------------------------%
% Output item

output [
    "position = \(position);\n",
    "tvar = \(tvar);\n",
    "objective = \(objective);\n"
];

%------------------------------------------------------------------------------%

