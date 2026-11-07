%-----------------------------------------------------------------------------
% Placing people on a photo
%
% Guido Tack
% 2007-02-22
%
% Ported from the Gecode example
%
%-----------------------------------------------------------------------------

% A group of people wants to take a group photo. Each person can give
% preferences next to whom he or she wants to be placed on the
% photo. The problem to be solved is to find a placement that
% satisfies as many preferences as possible.

include "globals.mzn";

%-----------------------------------------------------------------------------
% Specification

int: n_names;
int: n_prefs;
array[1..n_prefs, 0..1] of int: prefs;

%-----------------------------------------------------------------------------
% Model

array[0..n_names-1] of var 0..n_names-1: pos;
var 0..n_prefs: satisfies;

array[1..n_prefs] of var bool: ful;

constraint
  forall (i in 1..n_prefs) (
    let {
      int: pa = prefs[i,0],
      int: pb = prefs[i,1]
    } in
    ful[i] = (pos[pb]-pos[pa] == 1 xor pos[pa]-pos[pb] == 1)
  );

constraint
  sum (i in 1..n_prefs) (bool2int(ful[i])) = satisfies;

constraint
  alldifferent(pos);

% Break some symmetry
constraint
  pos[0] < pos[1];

solve :: int_search(pos, first_fail, indomain, complete) 
    maximize satisfies;

output [
    "pos = ", show(pos), "\n",
    "satisifes = ", show(satisfies), "\n"
];

%-----------------------------------------------------------------------------
%-----------------------------------------------------------------------------
