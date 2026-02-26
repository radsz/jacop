%------------------------------------------------------------------------------%
% ShipSchedulingConstraints.mzn
% Elena Kelareva 11/06/2011
%------------------------------------------------------------------------------%

%%%%%%%%%%%%%%%%%%% PARAMETERS %%%%%%%%%%%%%%%%%%%

% Number of ships to schedule
int: NShips;

% Number of available sailing times to calculate for.
int: NTimeSlots;

% Earliest time at which each ship can sail. (Some ships may finish loading later than 
% time slot 1.)
array[1..NShips] of int: EarliestStartTimeSlotForShip;

% The maximum draft that each ship is allowed to sail with at each time slot, calculated from 
% the predicted tide and wave conditions, as well as the port's safety rules.
% A value of 0 indicates that this ship cannot sail at all at this time.
array[1..NTimeSlots, 1..NShips] of int: MaxSailingDraft_cm;

% Specifies the separation time (in time slots) that is required between each pair of ships.
array[1..NShips, 1..NShips] of int: MinSeparationTimeSlots;

% Specifies the extra tonnes of cargo that can be loaded onto each ship per extra centimetre of 
% allowable draft. A higher value indicates that this is a big ship, which will benefit more 
% from higher draft compared to a smaller ship.
array[1..NShips] of int: TonnesPerCmDraft;


% Number of pairs of incoming/outgoing ships that use the same berth.
int: NBerthSwaps;

% Incoming ships that require an outgoing ship to move before they can use the same berth.
array[1..NBerthSwaps] of int: BerthSwap_Incoming;

% Outgoing ships that must move to make room for incoming ships.
array[1..NBerthSwaps] of int: BerthSwap_Outgoing;

% Maximum time difference between the start of the incoming ship transit and the start of the 
% outgoing ship transit.
array[1..NBerthSwaps] of int: BerthSwap_MaxTimeDiff;


%%%%%%%%%%%%%%%%%%% VARIABLES %%%%%%%%%%%%%%%%%%%

% The time at which each ship starts sailing.
array[1..NShips] of var 1..NTimeSlots: TransitStartTimeSlot;

% Variable indicating whether each ship sails.
array[1..NShips] of var 0..1: ShipSails;




%%%%%%%%%%%%%%%%%%% CONSTRAINTS %%%%%%%%%%%%%%%%%%%    
	
% Each ship is scheduled to sail with the highest allowable draft at the time of sailing.
int: Draft_cm_min = min(s in 1..NShips, t in 1..NTimeSlots)(MaxSailingDraft_cm[t, s]);
int: Draft_cm_max = max(s in 1..NShips, t in 1..NTimeSlots)(MaxSailingDraft_cm[t, s]);
array[1..NShips] of var Draft_cm_min..Draft_cm_max: Draft_cm;
constraint 
    forall(s in 1..NShips)(
        Draft_cm[s] == MaxSailingDraft_cm[TransitStartTimeSlot[s], s]
    );
    
    
% If the max draft for a ship at its scheduled time slot is 0, the ship cannot sail.
constraint
	forall(s in 1..NShips)(
		Draft_cm[s] == 0
		->
		ShipSails[s] == 0
	);

    
% No ship can sail before its earliest allowable sailing time.
constraint 
    forall(i in 1..NShips) (
        ShipSails[i] == 1 -> TransitStartTimeSlot[i] >= EarliestStartTimeSlotForShip[i]
    );
    
    
% If an incoming ship is going to a berth that an outgoing ship is leaving from, the outgoing ship 
% must have left by the time the incoming ship arrives at the berth.
constraint
	forall(ship in 1..NBerthSwaps) (
		TransitStartTimeSlot[BerthSwap_Outgoing[ship]] <= 
			TransitStartTimeSlot[BerthSwap_Incoming[ship]] + BerthSwap_MaxTimeDiff[ship]
	);
	
    
% Constraint for separation time between all pairs of ships.
% For every pair of different ships that are included in the schedule, either ship1 sails first, 
% or ship2 sails first, with sufficient separation time between them.
constraint
	forall(ship1 in 1..NShips) (
		forall(ship2 in ship1+1..NShips) (
            ShipSails[ship1] == 1 /\ ShipSails[ship2] == 1 ->
            (
		    	(TransitStartTimeSlot[ship2] - TransitStartTimeSlot[ship1]) >= MinSeparationTimeSlots[ship1, ship2]
			    \/
			    (TransitStartTimeSlot[ship1] - TransitStartTimeSlot[ship2]) >= MinSeparationTimeSlots[ship2, ship1]		
			)
		)
	);
    
    
%%%%%%%%%%%%%%%%%%%      SANITY CHECKS      %%%%%%%%%%%%%%%%%%%
% Ships
constraint assert(NShips > 0, "Invalid data: NShips must be positive.");

% Times
constraint assert(NTimeSlots > 0, "Invalid data: NTimeSlots must be positive.");
constraint assert(forall(i in 1..NShips) (EarliestStartTimeSlotForShip[i] > 0), "Invalid data: EarliestStartTimeSlotForShip must be positive.");
constraint assert(forall(i in 1..NShips) (EarliestStartTimeSlotForShip[i] <= NTimeSlots), "Invalid data: EarliestStartTimeSlotForShip must be <= NTimeSlots.");


%%%%%%%%%%%%%%%%%%% OBJECTIVE FUNCTION %%%%%%%%%%%%%%%%%%%
% Maximise the objective function (specified in a separate port-specific constraints file).
solve 
  	:: seq_search([
		int_search(TransitStartTimeSlot, input_order, indomain_min, complete),
  		int_search(ShipSails, input_order, indomain_max, complete)
  	])
    maximize objective;    
   
int: minObj = lb(sum(ship in 1..NShips)(objective_function[ship]));
int: maxObj = ub(sum(ship in 1..NShips)(objective_function[ship]));
var minObj..maxObj: objective = sum(ship in 1..NShips)(objective_function[ship]);

int: objective_function_min = min(i in 1..NShips)(lb(ShipSails[i] * Draft_cm[i] * TonnesPerCmDraft[i]));
int: objective_function_max = max(i in 1..NShips)(ub(ShipSails[i] * Draft_cm[i] * TonnesPerCmDraft[i]));
array [1..NShips] of var objective_function_min..objective_function_max: objective_function = [ 
		ShipSails[i] * Draft_cm[i] * TonnesPerCmDraft[i]
        | i in 1..NShips
    ];


%%%%%%%%%%%%%%%%%%% OUTPUT %%%%%%%%%%%%%%%%%%%
output 
[ "% Drafts and sailing slots for each ship:\n% "] ++ 
[ "Ship " ++ show(i) ++ 
	": ship sails: " ++ show(ShipSails[i] > 0) ++ 
	", draft " ++ show(Draft_cm[i]) ++ 
	", time " ++ show(TransitStartTimeSlot[i]) ++ 
	", obj. fun. value " ++ show(objective_function[i]) ++ "\n% " |
    	i in 1..NShips ] ++ 
[ "TOTAL OBJ FUN VALUE: " ++ show(objective) ++"\n"] ++ 
[
    "TransitStartTimeSlot = ", show(TransitStartTimeSlot), ";\n",
    "ShipSails = ", show(ShipSails), ";\n",
    "constraint objective = ", show(objective), ";\n"
];

    % Number of tugs available for this schedule
int: NTugs;
	% Maximum number of sets of tugs that can be required for each ship.
int: MaxNTugSets;
	% Constant: maximum number of tugs used for any ship in this schedule
int: MaxTugsRequiredPerShip = max([max([TugSetsPerShip[s,t] | t in 1..MaxNTugSets]) | s in 1..NShips]);

array [1..NShips] of 0..1: IncomingFlag;
set of 1..NShips: IncomingShips;
set of 1..NShips: OutgoingShips;

	% Number of sets of tugs that have to be specified for each ship.
array[1..NShips] of int: NTugSetsPerShip;
	% Lists number of tugs in each set of tugs with different time constraints 
	% used for this ship.
array[1..NShips, 1..MaxNTugSets] of int: TugSetsPerShip;
	% Turnaround time (time from start of this job to availability for next job) 
	% for each set of tugs for this ship.
array[1..NShips, 1..MaxNTugSets] of int: TugTurnaroundTimeSlots;
	% Extension to tug turnaround time caused by an inbound followed by an outbound transit.
array[1..NShips, 1..NShips] of int: ExtraTugAllowanceTimeSlots;
	

	% Array specifying the number of tugs that are busy at each time slot.
	% This is equal to the number of tugs required for each ship and each set of 
	% tugs, as long as that ship is sailing during the given time slot.
array [1..NShips, 1..NTimeSlots, 1..MaxNTugSets] of var 0..MaxTugsRequiredPerShip: TugsBusy;
	% Array specifying tug overlap consideration for an inbound followed by outbound ship.
array [1..NShips] of var 0..MaxTugsRequiredPerShip: TugsBusyExtra;


int: TugsBusyPerTimeSlot_min = min(t in 1..NTimeSlots)(
		lb(sum(ship in 1..NShips, tugSet in 1..MaxNTugSets)(
			TugsBusy[ship, t, tugSet])));
int: TugsBusyPerTimeSlot_max = max(t in 1..NTimeSlots)(
		ub(sum(ship in 1..NShips, tugSet in 1..MaxNTugSets)(
			TugsBusy[ship, t, tugSet])));
array [1..NTimeSlots] of var TugsBusyPerTimeSlot_min..TugsBusyPerTimeSlot_max: TugsBusyPerTimeSlot;
constraint
	forall(t in 1..NTimeSlots) (
		TugsBusyPerTimeSlot[t] = 
		sum(ship in 1..NShips) (
			sum(tugSet in 1..MaxNTugSets) (
				TugsBusy[ship, t, tugSet]
			)
		)
	);

% Set the number of tugs busy at each time slot for each ship.
constraint
	forall(ship in 1..NShips) (
		forall(t in 1..NTimeSlots) (
			forall(tugSet in 1..MaxNTugSets) (
				ShipSails[ship] == 1 /\
				t >= TransitStartTimeSlot[ship] /\
				t < TransitStartTimeSlot[ship] + TugTurnaroundTimeSlots[ship, tugSet]
				-> 
				TugsBusy[ship, t, tugSet] == TugSetsPerShip[ship,tugSet]
			)
		)
	);
constraint
	forall(ship in 1..NShips) (
		forall(t in 1..NTimeSlots) (
			forall(tugSet in 1..MaxNTugSets) (
				ShipSails[ship] == 0 \/
				t < TransitStartTimeSlot[ship] \/
				t >= TransitStartTimeSlot[ship] + TugTurnaroundTimeSlots[ship, tugSet]
				-> 
				TugsBusy[ship, t, tugSet] == 0
			)
		)
	);





% Check that with the minimum turnaround time for all tugs, we have enough tugs at each point in time.
% The tugs used for each set of inbound and outbound ships must never exceed the total number of tugs available.
constraint
	forall(t in 1..NTimeSlots) (
		sum(ship in IncomingShips) (
			sum(tugSet in 1..MaxNTugSets) (
				TugsBusy[ship, t, tugSet]
			)
		)
		<= NTugs
	);
constraint
	forall(t in 1..NTimeSlots) (
		sum(ship in OutgoingShips) (
			sum(tugSet in 1..MaxNTugSets) (
				TugsBusy[ship, t, tugSet]
			)
			+
			TugsBusyExtra[ship] * bool2int(t == TransitStartTimeSlot[ship])
		)
		<= NTugs
	);



% For all incoming ships followed by outgoing ships, add an extra tug allowance to ensure that 
% incoming tugs have time to move to the next ship.
constraint
	forall(ship1 in IncomingShips) (
		forall(ship2 in OutgoingShips) (
			(TransitStartTimeSlot[ship1] < TransitStartTimeSlot[ship2] /\
				TransitStartTimeSlot[ship1] + max([TugTurnaroundTimeSlots[ship1, tugSet] | tugSet in 1..MaxNTugSets])
				+ ExtraTugAllowanceTimeSlots[ship1, ship2] > TransitStartTimeSlot[ship2])
			->
			TugsBusyExtra[ship2] == sum([TugSetsPerShip[ship1, tugSet] | tugSet in 1..MaxNTugSets])
		)
	);
	

% TugsBusyExtra is 0 for incoming ships, or for outgoing ships that are not shortly after an incoming ship.
constraint
	forall(ship1 in IncomingShips) (
		TugsBusyExtra[ship1] == 0
	);
	
constraint
	forall(ship1 in IncomingShips) (
		forall(ship2 in OutgoingShips) (
			(TransitStartTimeSlot[ship1] > TransitStartTimeSlot[ship2] \/
				TransitStartTimeSlot[ship1] + max([TugTurnaroundTimeSlots[ship1, tugSet] | tugSet in 1..MaxNTugSets])
				+ ExtraTugAllowanceTimeSlots[ship1, ship2] <= TransitStartTimeSlot[ship2])
			->
			TugsBusyExtra[ship2] == 0
		)
	);
