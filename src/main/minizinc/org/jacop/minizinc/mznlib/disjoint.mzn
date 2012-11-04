%-----------------------------------------------------------------------------%
% Requires that sets 's1' and 's2' do not intersect.
%-----------------------------------------------------------------------------%
predicate disjoint(var set of int: s1, var set of int: s2) =
    jacop_disjoint(s1, s2);

%    s1 intersect s2 == {};

predicate jacop_disjoint(var set of int: s1, var set of int: s2);