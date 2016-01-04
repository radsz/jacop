%% ===== JaCoP specific search annotations =====
annotation weighted_degree;

annotation lds(int: d);
annotation credit(int: c, ann: b);
annotation bbs(int: b);

%% ===== JaCoP specific global constraints =====
include "all_distinct.mzn";
include "among_var.mzn";
include "diff2.mzn";
include "stretch.mzn";
