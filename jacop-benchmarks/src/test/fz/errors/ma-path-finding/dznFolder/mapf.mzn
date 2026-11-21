% 
% multi-agent path finding for grid maps and the sum-of-costs objective
% in Picat, by Neng-Fa Zhou, 2016
%
% Translated to MiniZinc by Hakan Kjellerstrand, 2017.
% 
int: as_len;
array[1..as_len,1..2] of int: as;
int: makespan;
int: makespan1 = makespan+1;
int: rel_len;
array[1..rel_len] of set of int: rel;
int: k;
int: n = rel_len; % number of nodes in the graph

% decision variables
array[1..makespan1,1..k,1..n] of var 0..1: B;
array[1..k] of var 1..makespan1: ET; % the end time of agent a is ET[a]
var k..(k*makespan1) : objective;
constraint objective = sum(ET);

solve 
    :: seq_search([
        int_search([agentAtTimeT[t, a] | t in 1..makespan1, a in 1..k], first_fail, indomain_split, complete),
        int_search(ET, smallest, indomain_min, complete),
    ])
    minimize objective;

%------------------------------------------------------------------------------%
% Added

include "alldifferent.mzn";

array[1..makespan1,1..k] of var 1..n: agentAtTimeT;

constraint redundant_constraint(
    % Agent can't occupy the same node at the same time
    forall(t in 1..makespan1)( 
        all_different([ agentAtTimeT[t,a] | a in 1..k ])
    )
    % Once the agent is at its destination it stays there
/\  forall(t in 1..makespan, a in 1..k)(
        agentAtTimeT[t, a] = as[a, 2] -> agentAtTimeT[t + 1, a] = as[a, 2]
    )
    % Transition constraints
    % XXX NOTE that this constraint creates auxiliary set variables.
    % Thus it is not allowed for the MiniZinc challenge
%/\  forall(t in 1..makespan, a in 1..k)(
%        agentAtTimeT[t + 1, a] in rel[agentAtTimeT[t, a]]
%    )
    % Source and target node
/\  forall(a in 1..k)(
        % Source node of agent
        agentAtTimeT[1, a] = as[a, 1]
        % Target node of agent
    /\  agentAtTimeT[makespan1, a] = as[a, 2]
    )
    % End times of the agent
/\  forall(a in 1..k)(
        ET[a] = sum(t in 1..makespan)(
            (t + 1) * (B[t, a, as[a, 2]] = 0 /\ B[t + 1, a, as[a, 2]] = 1)
        ) + 1 * (B[1, a, as[a, 2]] = 1)
    )
);

constraint forall(t in 1..makespan1, a in 1..k, v in 1..n)(
    % Linking the Boolean variables in B with the integer variables
    B[t, a, v] = 1 <-> agentAtTimeT[t, a] = v
);

%------------------------------------------------------------------------------%

constraint
   % Initialize the first and last states
   forall(a in 1..k) (
      B[1,a,as[a,1]] = 1 /\
      B[makespan1,a,as[a,2]] = 1
   )
   /\
   % Each agent occupies exactly one vertex at each time.
   forall (t in 1..makespan1, a in 1..k) (
     sum([B[t,a,v] | v in 1..n]) = 1
   )
   /\
   % No two agents occupy the same vertex at any time.
   forall(t in 1..makespan1, v in 1..n) ( 
     sum([B[t,a,v] | a in 1..k]) <= 1   
   )
   /\
   % Every transition is valid
   forall(t in 1..makespan, a in 1..k, v in 1..n) ( 
    B[t,a,v] = 1 -> sum([B[t+1,a,u] | u in rel[v]]) >= 1
   )

   /\
   % end time of agent a
   forall(a in 1..k, t in 1..makespan) (
     let {
       var 0..1: endAtT
     } in
     (endAtT = 1 <-> ET[a] = t)
     /\
     if t > 1 then
       endAtT = 1 -> B[t-1,a,as[a,2]] = 0
     else 
       true
     endif
     /\
     forall(t1 in t..makespan+1) (
       endAtT = 1 -> B[t1,a,as[a,2]] = 1
     )
   )
;

%------------------------------------------------------------------------------%
% Output item

output [
    %"B = array3d(1..\(makespan1), 1..\(k), 1..\(n), \(B));\n",
    "agentAtTimeT = array2d(1..\(makespan1), 1..\(k), \(agentAtTimeT));\n",
    "ET = \(ET);\n",
    "objective = \(objective);\n",
];

