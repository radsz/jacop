%% ===== JaCoP specific search annotations =====

annotation lds(int: d);
annotation credit(int: c, ann: b);
annotation bbs(int: b);
annotation priority(int: p);

annotation smallest_max;
annotation smallest_most_constrained;
annotation smallest_first_fail;
annotation random;
annotation afc_max;
annotation afc_min;
annotation afc_max_deg;
annotation afc_min_deg;
annotation activity_max;
annotation activity_min;
annotation activity_max_deg;
annotation activity_min_deg;

annotation tiebreak(array[int] of ann: a);
annotation tiebreak(ann: a1, ann: a2) = tiebreak([a1,a2]);

%% ===== Multi-objective optimisation =====

include "experimental.mzn";

/** Asks for the Pareto front of the goals \a s (min_goal, max_goal, int_min_goal, int_max_goal
  and sat_goal of std/experimental.mzn): every solution that no other solution improves in one
  goal without worsening another, one for each vector of goal values. Each one is printed when it
  is proven, followed by ========== when the front is complete. It is attached to the solve item:

  \code
  solve :: pareto([min_goal(cost), max_goal(quality)]) satisfy;
  \endcode

  MiniZinc's goal_hierarchy(s) asks for the lexicographic optimum of the goals instead. */
annotation pareto(array [int] of ann: s);

%------------------------------------------------------------------------------%
% Following search annotation is a place holders until it is included in the
% MiniZinc distribution

/** @group annotations.search Specify search on a group of searches \a search,
  for which variables \a x act as delegates for the search selection with 
  variable selection strategy \a select, and exploration strategy \a explore.
*/

annotation priority_search(
    array[int] of var int: x,
    array[int] of ann: search,
    ann: select,
    ann: explore
);

annotation priority_search(
    array[int] of var int: x,
    array[int] of ann: search,
    ann: select
) = priority_search(x, search, select, complete);

%% ===== JaCoP specific global constraints =====
include "all_distinct.mzn";
include "among_var.mzn";
include "diff2.mzn";
include "stretch.mzn";
include "soft_all_different_int.mzn";
include "soft_global_cardinality_int.mzn";
include "GCC.mzn";
include "channel.mzn";
include "disjunctive_setup.mzn";
include "subcircuit_cost.mzn";
include "weighted_subcircuits.mzn";
include "deviation.mzn";
include "inter_distance.mzn";
include "multi_inter_distance.mzn";
include "reservoir.mzn";

%% ===== JaCoP graph constraints =====
opt bool: use_jacop_graph_constraints;

include "graph/graph_match.mzn";
include "graph/digraph_match.mzn";
include "graph/sub_graph_match.mzn";
include "graph/sub_digraph_match.mzn";
include "graph/clique.mzn";
include "graph/graph_isomorphism.mzn";
