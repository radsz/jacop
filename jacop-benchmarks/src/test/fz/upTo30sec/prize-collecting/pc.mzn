%------------------------------------------------------------------------------%
% Parameters

int: n; % size

array[1..n,  0..n] of int: p;
int: min_p = min(i in 1..n, j in 0..n)(p[i, j]);
int: max_p = max(i in 1..n, j in 0..n)(p[i, j]);

int: max_obj = sum(i in 1..n)(max(0,max([p[i, j] | j in 1..n])));

%------------------------------------------------------------------------------%
% Variables

array[1..n] of var 0..n: pos; % posn of node i in path, 0 = notin
array[1..n] of var 0..n: next;% next posn in tour : 
                              % 1 for last edge, 0 for unused
array[1..n] of var min_p..max_p: prize;
var 0..max_obj: objective;

%------------------------------------------------------------------------------%
% Parameters

constraint pos[1] = 1;

constraint forall(i in 1..n) (
  % if used, the next position in tour is non-zero
  ( pos[i] > 0 <-> next[i] > 0 ) /\

  % Except if unused, there is at most 1 node with i as its successor
  ( sum(k in 1..n) (bool2int(next[k] = i)) <= 1) /\

  % next[i] > 1 means used, and not last
  ( next[i] > 1 -> pos[next[i]] = pos[i]+1 ) /\

  ( prize[i] = p[i, next[i]]  )
);

constraint objective = sum(i in 1..n)(prize[i]);

%------------------------------------------------------------------------------%
% Solve item

solve 
    :: seq_search([
        int_search(next, largest, indomain_max, complete),
        int_search(pos, largest, indomain_max, complete),
        int_search(prize, largest, indomain_max, complete),
        int_search([objective], input_order, indomain_max, complete)
    ])
    maximize objective;

%------------------------------------------------------------------------------%
% Output item

output [
    "pos = \(pos);\n",
    "next = \(next);\n",
    "prize = \(prize);\n",
    "objective = \(objective);\n"
];
