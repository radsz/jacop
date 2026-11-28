%-----------------------------------------------------------------------------%
% Defines the JaCoP global constraint disjunctive_setup: a unary resource with
% sequence-dependent transition (setup) times.
% s - the start times of the tasks.
% d - the durations of the tasks (not negative).
% f - the family of each task, an index of the rows and columns of t.
% t - t[f1, f2] is the smallest time between the end of a task of family f1
%     and the start of the next task of family f2 (not negative).
% For every two tasks i and j:
%   s[i] + d[i] + t[f[i], f[j]] <= s[j] \/ s[j] + d[j] + t[f[j], f[i]] <= s[i],
% also for tasks of zero duration.
%-----------------------------------------------------------------------------%
predicate disjunctive_setup(array[int] of var int: s, array[int] of var int: d,
                            array[int] of int: f, array[int, int] of int: t) =
    assert(index_set(s) = index_set(d) /\ index_set(s) = index_set(f),
        "disjunctive_setup: s, d and f must have the same index set") /\
    assert(index_set_1of2(t) = index_set_2of2(t),
        "disjunctive_setup: t must be square") /\
    assert(forall (i in index_set(f)) (f[i] in index_set_1of2(t)),
        "disjunctive_setup: every family must index t") /\
    assert(forall (a, b in index_set_1of2(t)) (t[a, b] >= 0),
        "disjunctive_setup: transition times must not be negative") /\
    forall (i in index_set(d)) (d[i] >= 0) /\
    jacop_disjunctive_setup(s, d,
        [f[i] - min(index_set_1of2(t)) | i in index_set(f)], array1d(t));

predicate jacop_disjunctive_setup(array[int] of var int: s, array[int] of var int: d,
                                  array[int] of int: f, array[int] of int: t);

%-----------------------------------------------------------------------------%
% disjunctive_setup with optional tasks: an absent task (s[i] absent) does not
% use the resource; the transition times hold between every two present tasks.
%-----------------------------------------------------------------------------%
predicate disjunctive_setup(array[int] of var opt int: s, array[int] of var int: d,
                            array[int] of int: f, array[int, int] of int: t) =
    assert(index_set(s) = index_set(d) /\ index_set(s) = index_set(f),
        "disjunctive_setup: s, d and f must have the same index set") /\
    assert(index_set_1of2(t) = index_set_2of2(t),
        "disjunctive_setup: t must be square") /\
    assert(forall (i in index_set(f)) (f[i] in index_set_1of2(t)),
        "disjunctive_setup: every family must index t") /\
    assert(forall (a, b in index_set_1of2(t)) (t[a, b] >= 0),
        "disjunctive_setup: transition times must not be negative") /\
    forall (i in index_set(d)) (d[i] >= 0) /\
    jacop_disjunctive_setup_optional(
        [if is_fixed(si) /\ absent(fix(si)) then 0 else deopt(si) endif | si in s], d,
        [f[i] - min(index_set_1of2(t)) | i in index_set(f)], array1d(t),
        [occurs(si) | si in s]);

predicate jacop_disjunctive_setup_optional(array[int] of var int: s,
    array[int] of var int: d, array[int] of int: f, array[int] of int: t,
    array[int] of var bool: o);
