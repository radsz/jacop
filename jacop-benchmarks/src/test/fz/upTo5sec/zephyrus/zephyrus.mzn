% Copyright (c) 2016, Jacopo Mauro. All rights reserved. 
% This file is licensed under the terms of the ISC License.


% Please note that you will need to set the MiniZinc standard library 
% environment variable $MZN_STDLIB_PATH to share/minizinc to include 
% the MiniSearch builtins

include "lex_greatereq.mzn";
include "lex_less.mzn";

int: MAX_INT = 4096;
%%%%%%%%%%%%%%%%
% Input parameters
%%%%%%%%%%%%%%%%

% components
set of int: comps;
% ports
set of int: ports;
% multiple provide port
set of int: multi_provide_ports;

% locations
set of int: locations;
% resources
set of int: resources;

% map of components with their requirements number
array[ comps, ports] of int: requirement_port_nums;
% map of components with their provided multi-ports
% -1 means infinite multi-port provider
array[ comps, multi_provide_ports] of int: provide_port_nums;
% map of components with their conflicts
array[ comps, ports] of bool: conflicts;
% map of multi-ports with their ports
array[ multi_provide_ports, ports] of bool: multi_provides;

% map of location with their costs
array[ locations ] of int: costs;
% map of locations with the resouces they provide
array[ locations, resources ] of int: resource_provisions;
% map of components with the resources they consume
array[ comps, resources ] of int: resource_consumptions;

%%%%%%%%%%%%%%%%
% variables
%%%%%%%%%%%%%%%%
% bindings number
array[ multi_provide_ports, ports, comps, comps] of var 0..MAX_INT: bindings;
% components number
array[ comps ] of var 0..MAX_INT: comps_num;
% location to number of component map
array[ locations, comps] of var 0..MAX_INT: comp_locations; 

% total number of components
var 0..MAX_INT: sum_comp;

%%%%%%%%%%%%%%%%
% constraints (no location)
%%%%%%%%%%%%%%%%

% bind the total number of components
constraint sum_comp = sum( i in comps)(comps_num[i]);

% bindings 0 if the multiprovide does not provide port
constraint forall(mport in multi_provide_ports, port in ports) (
  if multi_provides[mport,port]
  then true
  else forall(i in comps, j in comps) ( bindings[mport,port,i,j] = 0)
  endif
);

% provides must be greater or equal to bindings & infinite provide port constraints
constraint forall(mport in multi_provide_ports, pcomp in comps) (
  if provide_port_nums[pcomp,mport]=0
  then forall(port in ports, rcomp in comps) (
    bindings[mport,port,pcomp,rcomp] = 0  
  )
  else
    if (provide_port_nums[pcomp,mport] = -1)
    then forall(port in ports, rcomp in comps) (
     (comps_num[pcomp] = 0) -> (bindings[mport,port,pcomp,rcomp]=0))
    else sum( port in ports, rcomp in comps)(
      bindings[mport,port,pcomp,rcomp] ) <= comps_num[pcomp] * provide_port_nums[pcomp,mport]
    endif
  endif
);

% requires must be equal to bindings
% note: here is possible to require also smaller than or equal
constraint forall(port in ports, rcomp in comps) (
  sum( mport in multi_provide_ports, pcomp in comps)(
    bindings[mport,port,pcomp,rcomp] ) = comps_num[rcomp] * requirement_port_nums[rcomp,port]
);


% conflict constraints if component provide same port
constraint forall(port in ports, pcomp in comps) (
  if (conflicts[pcomp,port] /\ exists(mport in multi_provide_ports) (
    (multi_provides[mport,port]) /\ provide_port_nums[pcomp,mport] != 0))
  then comps_num[pcomp] <= 1
  else true
  endif
);

% conflict constraints
constraint forall(port in ports, pcomp in comps, rcomp in comps) (
  if (conflicts[rcomp,port] /\ exists(mport in multi_provide_ports) (
    (multi_provides[mport,port]) /\ provide_port_nums[pcomp,mport] != 0))
  then comps_num[pcomp] > 0 -> comps_num[rcomp] = 0
  else true
  endif
);

% unicity constraint
% note that we require that a component does not
% require more than one port provided by a
% multiple provide port
constraint forall(mport in multi_provide_ports, pcomp in comps, rcomp in comps) (
  let
      { int: max_req = sum(port in ports) (
          if multi_provides[mport,port]
          then requirement_port_nums[rcomp,port]
          else 0
          endif
        )
      } in
      if pcomp = rcomp
      then
        ( comps_num[pcomp] >= max_req  -> 
          sum(port in ports)(bindings[mport,port,pcomp,rcomp])
            <= max_req * (comps_num[rcomp] - 1))
        /\
        ( comps_num[pcomp] < max_req  ->
          forall (i in 1..max_req)( comps_num[pcomp] = i -> 
            sum(port in ports)(bindings[mport,port,pcomp,rcomp])  <= i * (i-1) ))
      else  
        ( comps_num[pcomp] >= max_req  -> 
          sum(port in ports)(bindings[mport,port,pcomp,rcomp])
            <= max_req * comps_num[rcomp] )
        /\
        ( comps_num[pcomp] < max_req  -> 
          forall (i in 0..max_req)( comps_num[pcomp] = i -> 
            sum(port in ports)(bindings[mport,port,pcomp,rcomp])  <= i * comps_num[rcomp] ) )
      endif
);

%%%%%%%%%%%%%%%%
% constraints for deciding locations
%%%%%%%%%%%%%%%%

% map location used or not used
array[ locations ] of var 0..1: used_locations;
constraint forall( l in locations)(
  sum(c in comps)(comp_locations[l,c]) = 0 <-> used_locations[l] = 0
);

constraint forall( c in comps) (
  sum( l in locations) ( comp_locations[l,c]) = comps_num[c] 
);


constraint forall( res in resources, loc in locations) (
  sum( comp in comps)( comp_locations[loc,comp] * resource_consumptions[comp,res] )
    <= resource_provisions[loc,res]
);

% the number of locations can not be greater than the number of components
% i.e, one component per location in the worst case
constraint sum(i in locations) (used_locations[i]) <= sum_comp;

%------------------------------------------------------------------------------%
% symmetry constraints (wrap in a unique predicate following minizinc specs


constraint symmetry_breaking_constraint(
  %if location are equal then first location has more comps than the second
  %in lexicographically order (based on the cost)
  forall( l1 in locations, l2 in locations)(
    if l1 < l2 /\ forall ( r in resources)(resource_provisions[l1,r] = resource_provisions[l2,r] )
    then
      if costs[l1] > costs[l2]
      then lex_greatereq(
        [comp_locations[l2,c] | c in comps],
        [comp_locations[l1,c] | c in comps])
        /\
        (used_locations[l1] = 1 -> used_locations[l2] = 1)
      else
        lex_greatereq(
          [comp_locations[l1,c] | c in comps],
          [comp_locations[l2,c] | c in comps])
          /\
          (used_locations[l2] = 1 -> used_locations[l1] = 1)
      endif
    else
      true
    endif
  ));


%------------------------------------------------------------------------------%
% Redundant constraints

%constraint redundant_constraint(
%  % Ralf constraints
%  forall (rcomp in comps, port in ports)(
%    if requirement_port_nums[rcomp,port]!=0
%    then 
%      comps_num[rcomp] > 0 -> sum( mport in multi_provide_ports, pcomp in comps)(
%      if provide_port_nums[pcomp,mport] != 0 /\ multi_provides[mport,port]
%      then comps_num[pcomp]
%      else 0
%      endif ) >= requirement_port_nums[rcomp,port] 
%    else
%      true
%    endif
%  ));

%------------------------------------------------------------------------------%
% Constraints
constraint 
    (   sum(l in locations)(comp_locations[l,1]) > 0
    \/  sum(l in locations)(comp_locations[l,2]) > 0
    )
/\  forall(x in locations)(comp_locations[x,3] < 2)
/\  forall(x in locations)(comp_locations[x,4] < 2)
;

int: obj_min = sum(l in locations)(if costs[l] < 0 then costs[l] else 0 endif);
int: obj_max = sum(l in locations)(if costs[l] > 0 then costs[l] else 0 endif);
var obj_min..obj_max: objective;

constraint objective = sum(l in locations)(used_locations[l] * costs[l]);

%------------------------------------------------------------------------------%
% Solve item

array [locations] of locations: costs_asc  = arg_sort(costs);
array [locations] of locations: costs_desc = reverse(costs_asc);

solve 
    :: seq_search([
        int_search([used_locations[costs_desc[i]] | i in locations], 
            input_order, indomain_min, complete),
        int_search([comp_locations[l, i] | l in locations, i in comps], 
            first_fail, indomain_max, complete),
        int_search(comps_num, first_fail, indomain_max, complete),
        int_search([bindings[m,p,i,j] | m in multi_provide_ports, p in ports, i,j in comps], 
            first_fail, indomain_max, complete)
    ])
    minimize objective;

%------------------------------------------------------------------------------%
% Output item

output [
    "bindings = array4d(\(multi_provide_ports), \(ports), \(comps), \(comps), \(bindings));\n",
    "comps_num = \(comps_num);\n",
    "comp_locations = array2d(\(locations), \(comps), \(comp_locations));\n",
    "used_locations = \(used_locations);\n",
    "objective = \(objective);\n",
    "% [\(objective), \(sum(x in locations)(sum(y in comps)(comp_locations[x,y])))]\n"
];


