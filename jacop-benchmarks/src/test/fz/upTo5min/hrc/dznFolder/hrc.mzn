int: num_bp;  % Target number of blocking pairs

int: nres;    % Number of residents
int: ncoup;   % Number of couples
int: nhosp;   % Number of hospitals

set of int: Hospitals = 1..nhosp;
set of int: Couples = 1..ncoup;
set of int: Singles = (2*ncoup+1)..nres;
set of int: Residents = 1..nres; 

int: max_rpref_len;  % The max length of a res pref list
int: max_hpref_len;  % The max length of a hosp pref list

% Resident pref lists (each list has at least one dummy zero at the end)
array[Residents,1..max_rpref_len+1] of int: rpref;  
array[Residents] of int: rpref_len;  % The length of each resident's pref list

array[Hospitals,1..max_hpref_len] of int: hpref; % Hospital preference lists
array[Hospitals] of int: hpref_len; % Lengths of hospital pref lists

% Hospital capacities
array[Hospitals] of int: hosp_cap;

% hrank[i][j] is the rank that hosp i gives res j, or 0 if hosp i doesn't rank res j
array[Hospitals,Residents] of int: hrank;  

array[Couples,1..max_rpref_len] of var bool: coup_bp;  % Couple blocking pairs
array[Singles,1..max_rpref_len] of var bool: single_bp;  % Single res blocking pairs

% coup_assigned[i][j] <-> Couple i assigned is assigned to its jth-preference hospital
array[Couples,1..max_rpref_len] of var bool: coup_assigned;
% single_assigned[i][j] <-> Single resident i is assigned is assigned to her jth-preference hospital
array[Singles,1..max_rpref_len] of var bool: single_assigned;

array[Couples] of var bool: coup_unassigned; % For each couple c, is c unassigned?
array[Singles] of var bool: single_unassigned; % For each single resident r, is r unassigned?

% Which position on pref list does couple get?
% This takes a value one greater than the length of the pref list if unmatched.
array[Couples] of var 1..(max_rpref_len+1): coup_pos; 
array[Singles] of var 1..(max_rpref_len+1): single_pos; % Which position on pref list does single res get?

% hosp_assigned[i][j] <-> Hospital i is assigned to resident j
array[Hospitals,1..max_hpref_len] of var bool: hosp_assigned;

% Functions to get IDs of first and second resident in a couple
function int: first_in_couple(int:i) = i * 2 - 1;
function int: second_in_couple(int:i) = i * 2;

% Ensure that exactly the target number of blocking pairs are present
constraint sum(i in Couples, j in 1..rpref_len[i*2-1]) (bool2int(coup_bp[i,j])) +
           sum(i in Singles, j in 1..rpref_len[i]) (bool2int(single_bp[i,j])) = num_bp;

% Boolean channeling for resident prefs, and ensure that selected
% resident pref position is one of the resident's prefs, or one past
% the end of the list (representing unmatched)
constraint forall (i in Singles) (
    single_pos[i] <= rpref_len[i] + 1 /\
    (single_unassigned[i] <-> single_pos[i] = rpref_len[i] + 1) /\
    forall (j in 1..rpref_len[i]) (single_assigned[i,j] <-> single_pos[i] = j) /\
    forall (j in rpref_len[i]+1..max_rpref_len) (single_assigned[i,j] = false)
);

constraint forall (i in Couples) (
    coup_pos[i] <= rpref_len[first_in_couple(i)] + 1 /\
    (coup_unassigned[i] <-> coup_pos[i] = rpref_len[first_in_couple(i)] + 1) /\
    forall (j in 1..rpref_len[first_in_couple(i)]) (coup_assigned[i,j] <-> coup_pos[i] = j) /\
    forall (j in rpref_len[first_in_couple(i)]+1..max_rpref_len) (coup_assigned[i,j] = false)
);

% Single-resident assignments match hosp assignments
constraint forall (i in Singles) (
    forall(j in 1..rpref_len[i]) (
        let {var int: h=rpref[i,j]} in
        single_assigned[i,j] <-> hosp_assigned[h, hrank[h,i]]
    )
);

% Couple assignments match hosp assignments
constraint forall (i in Hospitals) (
    forall(j in 1..hpref_len[i] where hpref[i,j] <= ncoup*2) (
        let {int: res=hpref[i,j], int: coup=(hpref[i,j]+1) div 2} in
        hosp_assigned[i,j] <-> sum(k in 1..rpref_len[res] where rpref[res,k]=i) (bool2int(coup_assigned[coup,k])) = 1
    )
);

% A hospital can't have any assigned positions beyond the end of its pref list
constraint forall (i in Hospitals) (
    forall(j in hpref_len[i]+1..max_hpref_len) (hosp_assigned[i,j] = false)
);

% Hospital capacities
constraint forall (i in Hospitals) (
    sum(j in 1..hpref_len[i])(bool2int(hosp_assigned[i,j])) <= hosp_cap[i]
);

% This predicate is true iff hospital h is not full with residents strictly preferred
% to its qth-preference resident
predicate hosp_would_prefer(int:h, int:q) =
    if q <= hosp_cap[h] then
        true
    else
        sum(k in 1..q-1)(bool2int(hosp_assigned[h,k])) < hosp_cap[h] \/
        sum(k in q+1..hpref_len[h])(bool2int(hosp_assigned[h,k])) > 0
    endif;

% This predicate is true iff the number of residents assigned to h that h strictly
% prefers to its q-th preference resident is less than the hospital's capacity minus 1
predicate hosp_would_prefer2(int:h, int:q) =
    sum(k in 1..q-1)(bool2int(hosp_assigned[h,k])) < hosp_cap[h] - 1 \/
    sum(k in q+1..hpref_len[h])(bool2int(hosp_assigned[h,k])) > 1;

% This predicate is used for the type-2 blocking pairs constraints. It is true
% iff hospital h1 is not full with residents who are either (a) or (b):
% (a) residents strictly preferred to h1's q1-th preference
% (b) if hospitals h1 and h2 are the same and q2>q1, then hospital h1's q2-th preference
predicate hosp_would_prefer_exc_partner(int:h1, int:h2, int:q1, int:q2) =
    if h2=h1 /\ q2>q1 then
        sum(k in 1..q1-1)(bool2int(hosp_assigned[h1,k])) + bool2int(hosp_assigned[h1,q2]) < hosp_cap[h1]
    else
        sum(k in 1..q1-1)(bool2int(hosp_assigned[h1,k])) < hosp_cap[h1]
    endif;

% Type 1
constraint forall(i in Singles) (
    forall(j in 1..rpref_len[i]) (
        let {int: h=rpref[i,j], int: q=hrank[h,i]} in
        single_pos[i] > j /\ hosp_would_prefer(h,q) -> single_bp[i,j] 
    )
);

% Types 2a and 2b
constraint forall (i in Couples) (
    let {int: r1=first_in_couple(i), int: r2=second_in_couple(i)} in
    forall(j in 1..rpref_len[r1]) ( 
        let {int: h1=rpref[r1,j], int: h2=rpref[r2,j], int: q1=hrank[h1,r1], int: q2=hrank[h2,r2]} in
        coup_pos[i] > j /\
        ((hosp_would_prefer_exc_partner(h1, h2, q1, q2) /\ h2 = rpref[r2,coup_pos[i]]) \/
         (hosp_would_prefer_exc_partner(h2, h1, q2, q1) /\ h1 = rpref[r1,coup_pos[i]]))
                -> coup_bp[i,j]
    )
);

% Type 3a
constraint forall (i in Couples) (
    let {int: r1=first_in_couple(i), int: r2=second_in_couple(i)} in
    forall(j in 1..rpref_len[r1] where rpref[r1,j] != rpref[r2,j]) (
        let {int: h1=rpref[r1,j], int: h2=rpref[r2,j], int: q1=hrank[h1,r1], int: q2=hrank[h2,r2]} in
        hosp_would_prefer(h1,q1) /\
        hosp_would_prefer(h2,q2) /\
        coup_pos[i] > j /\
        h2 != rpref[r2,coup_pos[i]] /\
        h1 != rpref[r1,coup_pos[i]]
                -> coup_bp[i,j]
    )
);

% Type 3bcd
constraint forall (i in Couples) (
    let {int: r1=first_in_couple(i), int: r2=second_in_couple(i)} in
    forall(j in 1..rpref_len[r1] where rpref[r1,j] = rpref[r2,j]) (
        let {int: h=rpref[r1,j], int: q1=hrank[h,r1], int: q2=hrank[h,r2]} in
        if q1 < q2 then
            hosp_would_prefer2(h,q1) /\ hosp_would_prefer(h,q2)
        else
            hosp_would_prefer(h,q1) /\ hosp_would_prefer2(h,q2)
        endif /\
        coup_pos[i] > j /\
        h != rpref[r2,coup_pos[i]] /\
        h != rpref[r1,coup_pos[i]]
                -> coup_bp[i,j]
    )
);

var 0..2*card(Couples)+card(Singles): objective;
constraint objective = sum(i in Couples)(2 * bool2int(coup_unassigned[i])) +
        sum(i in Singles)(bool2int(single_unassigned[i]));

solve
    %:: seq_search([
    %    bool_search(array1d(coup_unassigned), input_order, indomain_max, complete),
    %    bool_search(array1d(single_unassigned), input_order, indomain_max, complete),
    %    %int_search(single_pos ++ coup_pos, smallest, indomain_min, complete)
    %])
    %:: seq_search([
    %    int_search(coup_pos, smallest, indomain_min, complete),
    %    int_search(single_pos, smallest, indomain_min, complete),
    %])
    :: int_search(single_pos ++ coup_pos, first_fail, indomain_min, complete)
    minimize objective;

output [
    "coup_pos = array1d(\(Couples), \(coup_pos));\n",
    "single_pos = array1d(\(Singles), \(single_pos));\n",
    "objective = \(objective);\n",
];

%output [show(nres - sum(i in Couples)(2 * bool2int(coup_unassigned[i])) -
%             sum(i in Singles)(bool2int(single_unassigned[i]))) ++ "\n"]
%             ;
%             ++
%       [show(i) ++ " " ++ show(coup_pos[i]) ++ " " ++ show(rpref[i*2-1,coup_pos[i]]) ++ "-" ++ show(rpref[i*2,coup_pos[i]]) ++ "   " | i in Couples]
%       ++ ["\n"] ++
%       [show(i) ++ " " ++ show(single_pos[i]) ++ " (" ++ show(rpref[i,single_pos[i]]) ++ ")   " | i in Singles] ++ ["\n"] ++
%       [(if j==1 then "\n" else "" endif) ++ show(if hosp_assigned[i,j] then show(hpref[i,j]) ++ " " else "- " endif)
%            | i in Hospitals, j in 1..hpref_len[i]];
