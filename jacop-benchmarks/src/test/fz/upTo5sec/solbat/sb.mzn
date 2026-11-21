% new zinc file SolitaireBattleships.mzn
% At attempt to build a solution entirely within the IDE
% By Peter Stuckey August 2009
% Solitaire Battleships is a puzzle where
% we are given a partially filled in board and the number
% of ships in each row and column and have to fill it with ships

% "Improved" version does not introduce reified set_in

int: width;   % height of board (usually 10)
int: height;  % width of board (usually 10)
int: maxship; % maximal length of ship (usually 4)


set of int: ROWS = 1..width;
set of int: COLS = 1..height;
set of int: XROWS = 0..width+1;    % extended rows
set of int: XCOLS = 0..height+1;   % extended cols

%% ship types enumerated type
set of int: SHIPS = 1..maxship;  % different ship types
int: submarine = 1;
int: destroyer = 2;
int: cruiser = 3;
int: battleship = 4;


%% the PIECES enumerated type!
set of int: PIECES = 1..7;
int: w = 1; % water
int: c = 2; % circle (submarine)
int: l = 3; % left end of ship
int: r = 4; % right end of ship
int: t = 5; % top of ship
int: b = 6; % bottom of ship
int: m = 7; % middle of ship
array[PIECES] of string: code = [".","c","l","r","t","b","m"];

array[ROWS,COLS] of 0..7: hint; % the initial board configuration
array[ROWS] of int: rowsum;     % sums for each row
array[COLS] of int: colsum;     % sums for each col
array[SHIPS] of int: ship; % the number of each type of ship (usually [4,3,2,1]).



% variables 
array[XROWS,XCOLS] of var PIECES: board;  % the board
 
array[XROWS,XCOLS] of var 0..1: fill;     % which pieces are ships

array[PIECES] of var 0..width*height: npiece; % number of pieces of each type


% model

% ensure hints are respected
constraint forall(i in ROWS, j in COLS)(
			   if hint[i,j] != 0 then
			   		board[i,j] == hint[i,j]
			   else true endif
	       ); 

% make extended rows and cols empty
constraint forall(i in XROWS)(board[i,0] == w /\ board[i,width+1] == w);
constraint forall(j in COLS)(board[0,j] == w /\ board[height+1,j] == w);

% ensure that the fill array matches the board
constraint forall(i in XROWS, j in XCOLS)(
			   fill[i,j] = bool2int(board[i,j] != w)
	       ); 

% spacing constraints: gaps betwen ships
constraint forall(i in ROWS, j in COLS)(
	   (board[i,j] == w \/ board[i+1,j+1] == w)
	/\ (board[i,j] == w \/ board[i+1,j-1] == w)   % diagonal constraints
            /\ (board[i,j] in {c,l,r,t} -> board[i-1,j] == w)
            /\ (board[i,j] in {c,l,r,b} -> board[i+1,j] == w)
            /\ (board[i,j] in {c,l,t,b} -> board[i,j-1] == w)
            /\ (board[i,j] in {c,r,t,b} -> board[i,j+1] == w)
           );
               			                       
% ship shape constraints
constraint forall(i in ROWS, j in COLS)(
               %% a left piece needs a right piece or middle to the right
			   (board[i,j] == l -> (board[i,j+1] == r \/ board[i,j+1] == m))
			/\ (board[i,j] == r -> (board[i,j-1] == l \/ board[i,j-1] == m))
			/\ (board[i,j] == t -> (board[i+1,j] == b \/ board[i+1,j] == m))
			/\ (board[i,j] == b -> (board[i-1,j] == t \/ board[i-1,j] == m))
			   %% a middle piece has to have two opposite sides filled
			/\ (board[i,j] == m -> (   fill[i-1,j] == fill[i+1,j]
			                        /\ fill[i,j-1] == fill[i,j+1]
			                        /\ fill[i-1,j] + fill[i,j-1] == 1))
		   );
		   
% sum up pieces
constraint forall(p in PIECES)(
			   sum(i in ROWS, j in COLS)(bool2int(board[i,j] == p)) == npiece[p]
		   );

% piece sum constraints
constraint npiece[c] == ship[submarine]; % submarines
constraint npiece[l] == npiece[r]; % left right (probably redundant)
constraint npiece[t] == npiece[b]; % top bottom
constraint npiece[l] + npiece[t] == sum(s in destroyer..maxship)(ship[s]); 
                                   % no of ends
constraint npiece[m] == sum(s in cruiser..maxship)(ship[s] * (s - 2)); 
                                   % no of middles 		   
		    
% count number of bigger ships
% at least for standard battleships you can probably simply
% enforce this constraint for s in destroyer..destroyer		
% and still be guaranteed a correct solution    
constraint forall(s in destroyer..maxship)(
	           sum(i in ROWS,j in COLS)(bool2int(
			       if j + s - 1 <= width then
			          board[i,j] == l /\ board[i,j+s-1] == r     % ship length s lr
			       /\ forall(k in j+1..j+s-2)(board[i,k] == m)
			       else false endif
			    \/
			       if i + s - 1 <= height then
			          board[i,j] == t /\ board[i+s-1,j] == b     % ship length s tb
			       /\ forall(k in i+1..i+s-2)(board[k,j] == m)
			       else false endif
		       )) = ship[s]
		   );		    
		    		    

% row sums respected
constraint forall(i in ROWS)(
               sum(j in COLS)(fill[i,j]) == rowsum[i]
           );
           
% column sums respected           
constraint forall(j in COLS)(
               sum(i in ROWS)(fill[i,j]) == colsum[j]
           );           


solve 
    :: seq_search([
        int_search([ fill[i,j] | i in ROWS, j in COLS], 
            input_order, indomain_min, complete),
        int_search([ board[i, j] | i in ROWS, j in COLS], 
            first_fail, indomain_min, complete)
    ])
    satisfy;

output [ "% " ] ++ [ 
    code[fix(board[i,j])] ++ 
    if j == width then " " ++ show(rowsum[i]) ++ "\n% "
    else "" endif
| i in ROWS, j in COLS ] ++ [ 
    show(colsum[j]) 
| j in COLS ] ++ [
    "\n"
] ++ [
    "board = array2d(", show(XROWS), ", ", show(XCOLS), ", ", show(board), ");\n"
];
	   
