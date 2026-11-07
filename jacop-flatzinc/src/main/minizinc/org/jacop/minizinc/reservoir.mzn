%-----------------------------------------------------------------------------%
% Defines the JaCoP predicate reservoir.
%
% reservoir(times, changes, min_level, max_level): event i changes the level of a reservoir by
%   changes[i] at time times[i]. The level starts at 0, and the level at time t, the sum of the
%   changes of the events at or before t, stays within min_level..max_level at all times.
%   Positive changes are productions, negative ones consumptions.
%
% JaCoP propagates it with the balance constraint of Laborie (AIJ 2003), using the precedences
% x + c <= y of the model between the times of the events.
%-----------------------------------------------------------------------------%
predicate reservoir(array[int] of var int: times, array[int] of int: changes,
                    int: min_level, int: max_level) =
          assert(index_set(times) = index_set(changes),
                 "reservoir: times and changes must have the same index set",
          assert(min_level <= 0 /\ 0 <= max_level,
                 "reservoir: the initial level 0 must be within min_level..max_level",
          jacop_reservoir(times, changes, min_level, max_level)));

predicate jacop_reservoir(array[int] of var int: times, array[int] of int: changes,
                          int: min_level, int: max_level);
