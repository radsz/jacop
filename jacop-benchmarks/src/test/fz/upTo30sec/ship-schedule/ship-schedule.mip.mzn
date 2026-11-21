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

% Variable indicating whether each ship sails at any given time.
array[1..NShips, 1..NTimeSlots] of var 0..1: ShipSails;



%%%%%%%%%%%%%%%%%%% CONSTRAINTS %%%%%%%%%%%%%%%%%%%    
    
% Each ship sails at most once in the schedule.
constraint 
    forall(s in 1..NShips) (
    	sum(t in 1..NTimeSlots) (
        	ShipSails[s,t]
        ) == 1
    );
    
% No ship can sail before its earliest allowable sailing time.
constraint 
    forall(s in 1..NShips) (
    	forall(t in 1..EarliestStartTimeSlotForShip[s]) (
        	ShipSails[s,t] == 0
        )
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
			forall(t in 1..NTimeSlots) (
				ShipSails[ship1,t] + 
				sum(t2 in t..min(NTimeSlots, t+MinSeparationTimeSlots[ship1, ship2])) (
					ShipSails[ship2, t2]
				) <= 1		
			)
		)
	);
constraint
	forall(ship1 in 1..NShips) (
		forall(ship2 in ship1+1..NShips) (
			forall(t in 1..NTimeSlots) (
				ShipSails[ship2,t] + 
				sum(t2 in t..min(NTimeSlots, t+MinSeparationTimeSlots[ship2, ship1])) (
					ShipSails[ship1, t2]
				) <= 1			
			)
		)
	);
    

%%%%%%%%%%%%%%%%%%% OBJECTIVE FUNCTION %%%%%%%%%%%%%%%%%%%
% Maximise the total tonnage for the set of ships.
solve
    maximize sum(ship in 1..NShips)(objective_function[ship]);    
    
array [1..NShips] of var int: objective_function = [ 
		sum([ShipSails[i, t] * MaxSailingDraft_cm[t, i] * TonnesPerCmDraft[i] | t in 1..NTimeSlots])
        | i in 1..NShips
    ];
   


%%%%%%%%%%%%%%%%%%% OUTPUT %%%%%%%%%%%%%%%%%%%

% Each ship is scheduled to sail with the highest allowable draft at the time of sailing.
array [1..NShips] of var int: draft_cm = [ 
		sum([ShipSails[i, t] * MaxSailingDraft_cm[t, i] | t in 1..NTimeSlots])
        | i in 1..NShips
    ];
    
% Get the time of sailing for each ship, for output.
array [1..NShips] of var int: TransitStartTimeSlot = [ 
		sum([ShipSails[i, t] * t | t in 1..NTimeSlots])
        | i in 1..NShips
    ];

% Display resulting schedule.
output 
[ "Drafts and sailing slots for each ship:\n"] ++ 
[ "Ship " ++ show(i) ++ 
	": ship sails: " ++ show(sum([ShipSails[i, t] * MaxSailingDraft_cm[t, i] | t in 1..NTimeSlots]) > 0) ++ 
	", draft " ++ show(draft_cm[i]) ++ 
	", time " ++ show(TransitStartTimeSlot[i]) ++ 
	", obj. fun. value " ++ show(objective_function[i]) ++ "\n" |
    	i in 1..NShips ] ++ 
[ "TOTAL OBJ FUN VALUE: " ++ show(sum(ship in 1..NShips)(objective_function[ship])) ++"\n"] ++
[ "\n" ];

    % Number of tugs available for this schedule
int: NTugs;
	% Maximum number of sets of tugs that can be required for each ship.
int: MaxNTugSets;
	% Constant: maximum number of tugs used for any ship in this schedule
int: MaxTugsRequiredPerShip = max([sum([TugSetsPerShip[s,t] | t in 1..MaxNTugSets]) | s in 1..NShips]);

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
array [1..NShips, 1..NTimeSlots] of var 0..MaxTugsRequiredPerShip: TugsBusyExtra;


array [1..NTimeSlots] of var int: TugsBusyPerTimeSlot;
constraint
	forall(t in 1..NTimeSlots) (
		TugsBusyPerTimeSlot[t] = 
		sum(ship in 1..NShips) (
			sum(tugSet in 1..MaxNTugSets) (
				TugsBusy[ship, t, tugSet]
			)
		)
	);
	
	
% Calculate the number of tugs busy at each time slot for each ship.
% If the ship has recently sailed, and the tug turnaround time has not yet passed, then the tugs in
% the given tug set are busy.
constraint
	forall(ship in 1..NShips) (
		forall(tugSet in 1..NTugSetsPerShip[ship]) (
			forall(t in TugTurnaroundTimeSlots[ship, tugSet]..NTimeSlots) (
				TugsBusy[ship, t, tugSet] == 
					sum([ShipSails[ship, t2] | t2 in t-TugTurnaroundTimeSlots[ship, tugSet]+1..t])
					* TugSetsPerShip[ship,tugSet]
			)
		)
	);
constraint
	forall(ship in 1..NShips) (
		forall(tugSet in 1..NTugSetsPerShip[ship]) (
			forall(t in 1..TugTurnaroundTimeSlots[ship, tugSet]-1) (
				TugsBusy[ship, t, tugSet] == sum([ShipSails[ship, t2] | t2 in 1..t]) * TugSetsPerShip[ship,tugSet]
			)
		)
	);
	
	
% If any ship does not require the maximum number of tug sets, set TugsBusy to 0 for 
% any unused tug sets.
constraint
	forall(ship in 1..NShips) (
		forall(tugSet in NTugSetsPerShip[ship]+1..MaxNTugSets) (
			forall(t in 1..NTimeSlots) (
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
			TugsBusyExtra[ship, t]
		)
		<= NTugs
	);
			

% TugsBusyExtra is 0 for incoming ships.
constraint
	forall(ship in IncomingShips) (
		forall(t in 1..NTimeSlots) (
			TugsBusyExtra[ship, t] == 0
		)
	);
	
% For any outgoing ship, if any incoming ships that have recently sailed have not yet had time for
% the tugs to reach this outgoing ship, assume the tugs are still busy at the time the outgoing ship
% sails.
constraint
	forall(ship2 in OutgoingShips) (
		forall(t2 in 1..NTimeSlots) (
			TugsBusyExtra[ship2, t2] == 
			(
				sum(ship1 in IncomingShips)
				(
					sum(t1 in max(1,(t2 - max([TugTurnaroundTimeSlots[ship1, tugSet] | tugSet in 1..MaxNTugSets]) - ExtraTugAllowanceTimeSlots[ship1, ship2]))..max(1,(t2-1)))
					(
						ShipSails[ship1, t1]
					)
					* sum([TugSetsPerShip[ship1, tugSet] | tugSet in 1..MaxNTugSets])
				)
			)
		)
	);

