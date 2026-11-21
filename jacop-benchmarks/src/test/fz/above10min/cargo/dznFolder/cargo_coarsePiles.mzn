include "cumulative.mzn";
include "diffn.mzn";

int: nV;
int: nS;
set of int: VESSELS = 1..nV;
set of int: PILES = 1..nS;

int: stackbefore;
int: tMaxBetwRecl;
int: discrStackStart;
int: discrPadPos;
int: mulTonnage;
int: mulPileLen;
int: hourDiscr;

array[VESSELS] of int: eta;
array[PILES] of int: whichV;
array[PILES] of int: dS__; 
array[PILES] of int: dR;

int: H;
int: T;
int: stCap;
int: reclN;
int: delayMax;
int: sum_delay_max;

% --------------- INFERRED PARAMS -------------------------------

set of int: StackStartTimes = {o*discrStackStart | o in 0 .. (T div discrStackStart)};
set of int: PadPos = {o*discrPadPos | o in 0 .. (H div discrPadPos)};

array[VESSELS] of int: dRtotal = [ sum(o in PILES where whichV[o]=v)(dR[o]) | v in VESSELS ];
array[PILES] of int: dS = [ dS__[o] * discrStackStart | o in PILES];
array[PILES] of int: stTonnagePerHour = [ dR[o] * mulTonnage div dS[o] | o in PILES];
array[PILES] of int: len = [ dR[o] * mulPileLen div hourDiscr | o in PILES];
array[PILES] of int: len__ = [ (len[o] + discrPadPos - 1) div discrPadPos | o in PILES];

array[VESSELS] of PILES: whichPlast = [max(o in PILES where whichV[o]=v)(o) | v in VESSELS]; 
array[PILES] of int: ones = [1 | o in PILES];

% ---------------------- VARIABLES -------------------------------

array[PILES] of var 0..T div discrStackStart: tS__;
array[PILES] of var 0..T: tS = [tS__[o]*discrStackStart | o in PILES];
array[PILES] of var 0 .. (H div discrPadPos): h__;
array[PILES] of var 0..T: tR;
array[PILES] of var 0..T div discrStackStart: dT__;
array[PILES] of var 0..T: dTotal = [dT__[o]*discrStackStart | o in PILES];
array[VESSELS] of var 0..T: tReady = [ tR[whichPlast[v]]+dR[whichPlast[v]] | v in VESSELS ];

var 0..sum_delay_max: sum_delay;

int: comb_min = min([ lb_array(tR), lb_array(tS__), lb_array(h__) ]);
int: comb_max = max([ ub_array(tR), ub_array(tS__), ub_array(h__) ]);

array[1..nS*3] of var comb_min..comb_max: comb = 
[
	[tR[i], tS__[i], h__[i]][k]
  | i in PILES, k in 1..3
];

% --------------------- CONSTRAINTS -----------------------------

constraint forall(o in PILES)
  (dTotal[o] >= tR[o] + dR[o] - tS[o]);
constraint forall(v in VESSELS) (tS__[whichPlast[v]] + dT__[whichPlast[v]] <= (T + discrStackStart - 1) div discrStackStart); 
constraint forall(o in PILES)(tR[o] >= eta[whichV[o]]);
constraint forall(o in PILES)(tS[o] >= eta[whichV[o]] - stackbefore*discrStackStart);
constraint forall(a,b in PILES where whichV[a]=whichV[b] /\ a+1 = b)
   (tR[b] <= tR[a]+dR[a]+tMaxBetwRecl);
constraint forall(o in PILES)(tS__[o] + dS__[o] <= tR[o] div discrStackStart);
constraint forall(o in PILES)(h__[o] + len__[o] <= H div discrPadPos);
constraint forall(a,b in PILES where whichV[a] = whichV[b] /\ a+1=b)
   (tR[a] + dR[a] <= tR[b]);

% ----------------------- DELAY: -----------------------------------------
constraint (sum_delay = sum(v in VESSELS)
   (tReady[v] - eta[v] - dRtotal[v]));
constraint forall(v in VESSELS)
   (tReady[v] - eta[v] - dRtotal[v] <= delayMax);

% ---------------------------- DIFF2: ------------------------------------
constraint diffn(tS__, h__, dT__, len__);

% --------------- CUMULATIVES --------------------------------------------
constraint cumulative(tS__, dT__, len__, H div discrPadPos);  % low-level
constraint cumulative(tS__, dS__, stTonnagePerHour, stCap);
constraint cumulative(tR, dR, ones, reclN);


% --------------- OBJECTIVE --------------------------------------------

int: obj_min = sum(v in 5..nV-5)(lb(tReady[v]) - eta[v] - dRtotal[v]);
int: obj_max = sum(v in 5..nV-5)(ub(tReady[v]) - eta[v] - dRtotal[v]);
var obj_min..obj_max: objective;

constraint
	objective = sum(v in 5..nV-5)(tReady[v] - eta[v] - dRtotal[v]);


% --------------------------- SOLVE --------------------------------------

solve 
  	:: seq_search([
		int_search(comb, input_order, indomain_split, complete),
		int_search(dT__, first_fail, indomain_min, complete),
		int_search([objective], input_order, indomain_min, complete)
	])
	minimize objective;

output [
    "tS__ = \(tS__);\n",
    "h__ = \(h__);\n",
    "tR = \(tR);\n",
    "dT__ = \(dT__);\n",
    "objective = \(objective);\n",
];
%output [
%	"objective = ", show(objective),
%    ";\nH      = ", show(H),
%    ";\nT      = ", show(T),
%    ";\ntS     = ", show(tS),
%    ";\ntR     = ", show(tR),
%    ";\nh      = ", show(h__),
%    ";\ntReady = ", show([tR[whichPlast[v]] + dR[whichPlast[v]] | v in VESSELS]),
%    ";\ndelay  = ", show([tR[whichPlast[v]] + dR[whichPlast[v]] - eta[v] - dRtotal[v] | v in VESSELS]),
%    ";\ndTotal = ", show(dTotal),
%    ";\nlength = ", show(len),
%    ";\nave_delay = ", show(sum_delay div nV),
%	"\n"
%];
