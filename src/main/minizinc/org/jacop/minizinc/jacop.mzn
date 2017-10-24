%% ===== JaCoP specific search annotations =====
annotation weighted_degree;

annotation lds(int: d);
annotation credit(int: c, ann: b);
annotation bbs(int: b);

annotation smallest_max;
annotation smallest_most_constrained;
annotation smallest_first_fail;

%% ===== JaCoP specific global constraints =====
include "all_distinct.mzn";
include "among_var.mzn";
include "diff2.mzn";
include "stretch.mzn";
include "soft_all_different_int.mzn";
include "soft_global_cardinality_int.mzn";