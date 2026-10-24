%----------------------------------------------------------------------------%
%
% There are two warehouses, A and B.
% Each warehouse has a fixed set of customers.  No customer
% is served by both warehouses - so the two sets are disjoint.
% Each warehouse has a truck.
% There is a table of distances from customer to warehouse
% and between the customers.
%
% A truck is allowed to deliver not only to customers
% of its own warehouse, but also to customers of the other warehouse.
% To make this possible there is a "depot" where one truck can leave
% some goods for the other truck to pick up and deliver to the customer.
% The choice of depot is a decision variable ranging over customer and 
% warehouse locations.
%
% Naturally before delivering to a customer of another warehouse, the
% truck must first visit the depot to collect the goods for delivery
% to the customer.  The other truck must also visit the depot, of
% course, to drop off the goods.  There are no time constraints, and
% therefore no restriction on which truck visits the depot first.
% (Since there are no time constraints, the first truck to arrive
% could simply wait till the other truck came.)
%
% The objective is to minimise the maximum of the distances
% travelled by the trucks.
%
%----------------------------------------------------------------------------%

include "alldifferent.mzn" ;

%----------------------------------------------------------------------------%
% 
% Parameters
%

% Number of clients each warehouse has.
%
int: PSize;

%   This model allows Depot to be a parameter:
% int: Depot = 11;
%   To ensure trucks only serve their own clients
%   you can set the depot to a non-existent location
% int: Depot = 0 ;
%   ...or a variable over all the possible locations  
var 1..TSize: Depot;

% Total number of locations (Warehouses plus customers) in the problem.
%
int: TSize = (PSize +1 ) * 2 ;

% We use PSize+1 often, so we next give it the name TourLength.
%
int: TourLength = PSize+1 ;

% Warehouse A's clients are from 1..TourLength
% Warehouse B's clients are from TourLength+1..TSize

% Set the location of warehouse A to 1.
%
int: AWHouse = 1 ;

% Set the location of warehouse B to first of its client's locations.
% For a size 3 problem, therefore, warehouse B is at location 5.
%
int: BWHouse = TourLength + 1;

% Each tour may have a different size, but
% to keep things manageable we have only allowed each truck to
% visit at most 1 extra client.  In this model both tours are
% represented as arrrays of the same size: one larger than needed
% to visit all their customers.
% In case the extra location is not needed (the truck only visits
% its own customers) the truck simply remains at the warehouse
% so each of its first AND SECOND location is the warehouse.
%
int: ASize = TourLength + 1;  
int: BSize = TourLength + 1;  

%----------------------------------------------------------------------------%
%
% Variables
%

% Need two "NextCity" arrays when there's a depot!
% This is the easy TSP model, with the awkward cost function
% The tour for truck A, simply listed the locations visited
% in the order of visits.
% Each truck can visit any location.
%
array[1..ASize] of var 1..TSize: TourALoc ;

% The tour for truck B.
%
array[1..BSize] of var 1..TSize: TourBLoc ;

% Set the complete distance table (see the .dzn files for actua numbers).
%
array[1..14, 1..14] of int: AllDist;

int: MaxTotDist = sum([max([AllDist[N,M] |M in 1..TSize]) | N in 1..TSize]) ;
int: MaxLeg = max([max([AllDist[N,M] | M in 1..TSize]) | N in 1..TSize]) ;

% For each tour (A and B) keep an array of distances 
% to use for computing total distance.
%
array[1..ASize] of var 0..MaxLeg: ALegDist ;
array[1..BSize] of var 0..MaxLeg: BLegDist ;

% Represent the optimisation expression as a variable so as to 
% get proper output from lazy MiniZinc.
%
var 0..MaxTotDist: ADist;
var 0..MaxTotDist: BDist;

var 0..MaxTotDist: objective; 

%----------------------------------------------------------------------------%

% The optimisation variable.
%
constraint ADist = sum(ALegDist) ;
constraint BDist = sum(BLegDist) ;
constraint objective = max(ADist,BDist) ;

% The distance between the Nth and (N+1)th locations.
%
constraint
    forall (N in 1..ASize-1) (ALegDist[N] = AllDist[TourALoc[N], TourALoc[N+1]]);

% The distance from the final location back to the warehouse.
%
constraint ALegDist[ASize] = AllDist[TourALoc[ASize],TourALoc[1]] ;  

constraint 
    forall (C in 1..BSize-1) (BLegDist[C] = AllDist[TourBLoc[C], TourBLoc[C+1]]);

constraint BLegDist[BSize] = AllDist[TourBLoc[BSize],TourBLoc[1]] ;   

% Ensure all location are visited by at least one of the tours A or B.
%
constraint forall (C in 1..TSize) ( exists (Y in TourALoc++TourBLoc) (Y = C) );

% Constraints
% Ensure each tour visits different locations.
% BEWARE that these constraint are NOT redundant with the previous one, because they 
% exclude consecutive visits of non-warehouse locations!
%
constraint alldifferent([TourALoc[N]|N in 2..ASize]);
constraint alldifferent([TourBLoc[N]|N in 2..BSize]);

% The warehouse must be visited first
%
constraint TourALoc[1] = AWHouse ;
constraint TourBLoc[1] = BWHouse ;

% Don't come back to the Warehouse until all the
% deliveries are done!
%
constraint forall (N in 3..ASize-1) (TourALoc[N] != AWHouse);
constraint forall (N in 3..BSize-1) (TourBLoc[N] != BWHouse);

% Symmetry breaking constraints
% A second visit of the warehouse must be at the second position
%
constraint symmetry_breaking_constraint( TourALoc[ASize] != AWHouse );
constraint symmetry_breaking_constraint( TourALoc[BSize] != BWHouse );

% Warehouses cannot be visit by different trucks
%
constraint forall (N in 1..ASize) (TourALoc[N] != BWHouse);
constraint forall (N in 1..BSize) (TourBLoc[N] != AWHouse);

%----------------------------------------------------------------------------%
%
% Depot constraints
%
      
% If tour A visits a location from warehouse B, then its must visit the depot
% before visiting this location.
% Thus if the Nth location in tour A is a client of warehouse B, 
% (because its value is greater than TourLength and it is not the Depot)
% then tour A must visit the Depot beforehand (at its Mth location, where M<N).
%
constraint
    forall (N in 1..ASize)
        ( (TourALoc[N] > TourLength /\ TourALoc[N] != Depot ) ->
          ( exists (M in 1..N-1) (TourALoc[M] = Depot) ) );

% If tour B visits one of A's clients, then it must visit the Depot beforehand.
%
constraint
    forall (N in 1..BSize)
        ( (TourBLoc[N] <= TourLength /\ TourBLoc[N] != Depot ) ->
          ( exists (M in 1..N-1) (TourBLoc[M] = Depot) ) ) ;

% Note that a truck always visits the depot if the depot is one of
% its own customers because, if it does not visit any of the other
% warehouse's customers, it must still visit TourLength different locations
% which means it visits ALL its own customers!

%----------------------------------------------------------------------------%

solve 
    :: seq_search([
        int_search(TourALoc ++ TourBLoc, first_fail, indomain_min, complete),
        int_search([Depot], input_order, indomain_min, complete)
    ])
    minimize objective; 

%----------------------------------------------------------------------------%

output[ "%% Maximum Tour Distance: ", show(objective), 
       ";\nDepot = ", show(Depot), 
       ";\n%% ADist is: ",show(ADist), 
       ";\n%% BDist is: ", show(BDist),       
       ";\nTourALoc = ",  show(TourALoc), 
       ";\nTourBLoc = ", show(TourBLoc), 
       ";\nobjective = ", show(objective),
       ";\n" ] ;

%----------------------------------------------------------------------------%
%----------------------------------------------------------------------------%
