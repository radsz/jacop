%
% Model for group splitting problem
%
% A group of people want to do activities (Cinema then Restaurant)  
% in subgroups where the activities for subgroups are supposed to 
% match better members' preferences.
% The aim of our model is to find the best activities and group
% combinations to recommend.
%
% @authors:
%
% Jacopo Mauro <mauro.jacopo@gmail.com>
% Tong Liu <t.liu@unibo.it>
%

include "count.mzn";
include "table.mzn";

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Variables and array definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% number of users
set of int: user_ids;

% activities for phase 1
set of int: activity1_ids;

% activities for phase 2
set of int: activity2_ids;

% number of cells
set of int: cell_ids;

% number of groups
set of int: group_ids;

% time domain
set of int: time_slot_ids;

% rating domains
set of int: pub_rating_domain = 0..5;
set of int: user_rating_domain = -2..2;

% global constraint Variables
int: min_group_size; % min cardinality of a subgroup
int: usersn; % number of users
int: max_wait; % wait time btw 2 activities
int: startAfter; % time after which schedule starts 
int: eta; % balance user's rating and public rating

array[activity1_ids,1..5] of int: activities1;
array[activity2_ids,1..5] of int: activities2;

array[user_ids,activity1_ids] of user_rating_domain: preferences1; 
array[user_ids,activity2_ids] of user_rating_domain: preferences2; 

array[activity1_ids] of int: oid1; 
array[activity2_ids] of int: oid2; 

array[cell_ids,cell_ids] of int: distances;

% Create activities1_new for the calculation inserting index in the first position. 
array[activity1_ids,1..6] of int: activities1_data = array2d(activity1_ids,1..6,
  [ if i=1 then j else activities1[j,i-1] endif | j in activity1_ids, i in 1..6 ]);
array[activity2_ids,1..6] of int: activities2_data = array2d(activity2_ids,1..6,
  [ if i=1 then j else activities2[j,i-1] endif | j in activity2_ids, i in 1..6  ]);

% Configure datalist for table constraint
array[1..max(user_ids)*max(activity1_ids),1..3] of int: preferences1_data = array2d(1..max(user_ids)*max(activity1_ids),1..3,
  [ if k=1 then i else if k=2 then j else preferences1[i,j] endif endif | i in user_ids, j in activity1_ids, k in 1..3 ]); 
array[1..max(user_ids)*max(activity2_ids),1..3] of int: preferences2_data = array2d(1..max(user_ids)*max(activity2_ids),1..3,
  [ if k=1 then i else if k=2 then j else preferences2[i,j] endif endif | i in user_ids, j in activity2_ids, k in 1..3 ]);  
array[1..max(cell_ids)*max(cell_ids),1..3] of int: distances_data = array2d(1..max(cell_ids)*max(cell_ids),1..3,
  [ if k=1 then i else if k=2 then j else distances[i,j] endif endif | i in cell_ids, j in cell_ids, k in 1..3 ]); 



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Maps to define a solution
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% map user -> group
array[user_ids] of var group_ids: user_group_map1;
array[user_ids] of var group_ids: user_group_map2;

% map group -> activity
array[group_ids] of var activity1_ids: group_act_map1;
array[group_ids] of var activity2_ids: group_act_map2;

% map user -> activity
array[user_ids] of var activity1_ids: user_act_map1;
array[user_ids] of var activity2_ids: user_act_map2;

% map user -> start of activity
array[user_ids] of var time_slot_ids: user_start_time_map1;
array[user_ids] of var time_slot_ids: user_start_time_map2;

% map user -> duration
array[user_ids] of var time_slot_ids: user_duration_map1;
array[user_ids] of var time_slot_ids: user_duration_map2;

% map user -> begin
array[user_ids] of var time_slot_ids: activity_available_from1;
array[user_ids] of var time_slot_ids: activity_available_from2;

% map user -> end
array[user_ids] of var time_slot_ids: user_end_map1;
array[user_ids] of var time_slot_ids: user_end_map2;

% map user -> cell
array[user_ids] of var cell_ids: user_cell_map1;
array[user_ids] of var cell_ids: user_cell_map2;

% map user -> type
array[user_ids] of var pub_rating_domain: user_pub_rating_map1;
array[user_ids] of var pub_rating_domain: user_pub_rating_map2;

% map user -> weight
array[user_ids] of var user_rating_domain: user_weight_map1;
array[user_ids] of var user_rating_domain: user_weight_map2;

% map user -> distance
array[user_ids] of var time_slot_ids: user_distance_map;

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Check that the group members satisfy minCardinality
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint forall(i in group_ids) (
  let { var min_group_size..usersn: c} in (
    count(user_group_map1,i,c)) );

constraint forall(i in group_ids) (
  let { var min_group_size..usersn: c} in (
    count(user_group_map2,i,c)) );


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Channel constraints
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint forall(i in user_ids) (
   table( [ user_act_map1[i], activity_available_from1[i], user_end_map1[i], user_duration_map1[i], user_cell_map1[i], user_pub_rating_map1[i] ], activities1_data) );

constraint forall(i in user_ids) (
   table( [ user_act_map2[i], activity_available_from2[i], user_end_map2[i], user_duration_map2[i], user_cell_map2[i], user_pub_rating_map2[i] ], activities2_data) );
  
constraint forall(i in user_ids) (
  table( [ i, user_act_map1[i], user_weight_map1[i] ], preferences1_data));

constraint forall(i in user_ids) (
  table( [ i, user_act_map2[i], user_weight_map2[i] ], preferences2_data));

constraint forall(i in user_ids) (
  table( [ user_cell_map1[i], user_cell_map2[i], user_distance_map[i] ], distances_data));

% user's activity is also group's activity

constraint forall(i in user_ids) (
  user_act_map1[i] = group_act_map1[user_group_map1[i]] );

constraint forall(i in user_ids) (
  user_act_map2[i] = group_act_map2[user_group_map2[i]] );


% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% % Symmetry breaking constraints
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% user 1 belongs always to the first group
constraint redundant_constraint(
  user_group_map1[min(user_ids)] = min(group_ids) /\
  user_group_map2[min(user_ids)] = min(group_ids));

% next user belongs to the group of the previous users or +1
constraint symmetry_breaking_constraint(
  forall (i in 1..max(group_ids)-min(group_ids)+1) (
  user_group_map1[min(user_ids)+i] in min(group_ids)..min(group_ids)+i /\
  user_group_map2[min(user_ids)+i] in min(group_ids)..min(group_ids)+i
));

% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%  
% % Activity temporal constraints
% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint forall(i in user_ids) (
  user_start_time_map1[i] >= activity_available_from1[i] /\
  user_start_time_map1[i] <= user_end_map1[i] - user_duration_map1[i]);

constraint forall(i in user_ids) (
  user_start_time_map2[i] >= activity_available_from2[i] /\
  user_start_time_map2[i] <= user_end_map2[i] - user_duration_map2[i]);

constraint forall(i in user_ids) (
  user_start_time_map2[i] >= user_start_time_map1[i] + user_duration_map1[i] +
    user_distance_map[i] /\
  user_start_time_map2[i] <= user_start_time_map1[i] + user_duration_map1[i] + max_wait );

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Start After Constraint
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

constraint forall(i in user_ids) (
  user_start_time_map1[i] >= startAfter);

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Compute objective function
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

int: objub = eta*card(user_ids)*2 + (10-eta)*card(user_ids)*5 + (10-eta)*card(user_ids)*5 + eta*card(user_ids)*2;
int: objlb=eta*card(user_ids)*(-2)+ (10-eta)*card(user_ids)*0 + (10-eta)*card(user_ids)*0 + eta*card(user_ids)*(-2);
var objlb..objub: objective;

constraint objective = (
  eta * sum (user_weight_map1) + (10-eta) * sum (user_pub_rating_map1) + (10-eta) * sum (user_pub_rating_map2) + eta * sum (user_weight_map2) );

solve :: seq_search([
    int_search(user_group_map1,first_fail, indomain_min, complete),
    int_search(user_group_map2,first_fail, indomain_min, complete),
    int_search(user_weight_map1, first_fail, indomain_min, complete),
    int_search(user_weight_map2, first_fail, indomain_min, complete),
    int_search(user_act_map1, first_fail, indomain_min, complete),
    int_search(user_act_map2, first_fail, indomain_min, complete),
    int_search(user_start_time_map1, first_fail, indomain_min, complete),
    int_search(user_start_time_map2, first_fail, indomain_min, complete),
    int_search(user_duration_map1, first_fail, indomain_min, complete),
    int_search(user_duration_map2, first_fail, indomain_min, complete),
    int_search(user_end_map1, first_fail, indomain_min, complete),
    int_search(user_end_map2, first_fail, indomain_min, complete),
  ])
  maximize objective;


output [
    "user_group_map1 = \(user_group_map1);\n",
    "user_group_map2 = \(user_group_map2);\n",
    "user_weight_map1 = \(user_weight_map1);\n",
    "user_weight_map2 = \(user_weight_map2);\n",
    "user_act_map1 = \(user_act_map1);\n",
    "user_act_map2 = \(user_act_map2);\n",
    "user_start_time_map1 = \(user_start_time_map1);\n",
    "user_start_time_map2 = \(user_start_time_map2);\n",
    "user_duration_map1 = \(user_duration_map1);\n",
    "user_duration_map2 = \(user_duration_map2);\n",
    "user_end_map1 = \(user_end_map1);\n",
    "user_end_map2 = \(user_end_map2);\n",
    "objective = \(objective);\n"
];

