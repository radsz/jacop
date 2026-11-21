/*
 * An automatic MiniZinc model
 */

int: nCostSupport0 = 650000;
int: nDSf_Pi2Pi = 1;
int: nLengthUnitMM = 200;	 %%% Discr unit length in mm

var 200..200: nXNd__1_1_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 56..56: nXNd__1_1_Y;
var 122..122: nXNd__1_1_Z;
var -15..365: nXNd__1_2_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 2..165: nXNd__1_2_Y;
var 0..215: nXNd__1_2_Z;
var -15..365: nXNd__1_3_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 2..165: nXNd__1_3_Y;
var 0..215: nXNd__1_3_Z;
var -15..365: nXNd__1_4_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 2..165: nXNd__1_4_Y;
var 0..215: nXNd__1_4_Z;
var -15..365: nXNd__1_5_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 2..165: nXNd__1_5_Y;
var 0..215: nXNd__1_5_Z;
var -15..365: nXNd__1_6_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 2..165: nXNd__1_6_Y;
var 0..215: nXNd__1_6_Z;
var -15..365: nXNd__1_7_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 2..165: nXNd__1_7_Y;
var 0..215: nXNd__1_7_Z;
var -15..365: nXNd__1_8_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 2..165: nXNd__1_8_Y;
var 0..215: nXNd__1_8_Z;
var -15..365: nXNd__1_9_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 2..165: nXNd__1_9_Y;
var 0..215: nXNd__1_9_Z;
var 199..199: nXNd__1_10_X;	 %%% Node coord X/Y/Z for pipe _, node _
var 87..87: nXNd__1_10_Y;
var 100..100: nXNd__1_10_Z;

array[int] of int: nBoxType = [1, 2, 1, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 2, 2, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 2, 2, 2, 2, 2, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 2, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 3, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 3, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 2, 2, 1, 4, 5, 5, 5, 5, 3, ];
array[int] of int: nXBx_1D = [0, 88, 35, 1, 86, 33, 16, 75, 80, 21, 86, 35, 23, 86, 43, 34, 20, 0, 53, 86, 58, 53, 112, 59, 54, 85, 58, 63, 39, 5, 63, 40, 13, 63, 112, 62, 64, 112, 13, 64, 112, 61, 78, 39, 5, 78, 40, 13, 79, 88, 13, 99, 112, 14, 110, 86, 58, 111, 144, 58, 116, 93, 31, 117, 93, 30, 117, 93, 61, 120, 80, 100, 90, 50, 70, 120, 93, 58, 121, 92, 58, 124, 37, 0, 109, 22, 0, 136, 54, 167, 136, 56, 173, 136, 67, 45, 136, 69, 43, 137, 65, 12, 137, 85, 13, 137, 86, 30, 152, 49, 36, 152, 50, 162, 158, 80, 42, 128, 50, 12, 158, 51, 36, 158, 122, 38, 160, 122, 44, 164, 50, 14, 164, 51, 13, 167, 47, 0, 152, 32, 0, 173, 63, 26, 174, 64, 75, 174, 93, 62, 174, 87, 43, 174, 89, 51, 174, 92, 52, 174, 64, 57, 178, 86, 62, 179, 86, 61, 179, 86, 69, 180, 89, 44, 180, 89, 51, 180, 92, 52, 181, 92, 44, 181, 92, 58, 189, 54, 112, 190, 56, 82, 191, 11, 0, 191, 86, 113, 194, 55, 58, 194, 56, 61, 195, 55, 57, 197, 21, 13, 198, 20, 13, 198, 92, 13, 200, 46, 0, 185, 31, 0, 203, 20, 5, 207, 20, 4, 208, 54, 200, 208, 55, 205, 208, 77, 62, 208, 78, 61, 208, 35, 43, 209, 36, 143, 209, 88, 61, 214, 86, 70, 218, 54, 112, 218, 55, 57, 218, 55, 121, 219, 54, 180, 224, 55, 180, 224, 79, 59, 225, 79, 58, 228, 92, 14, 234, 32, 100, 204, 2, 70, 234, 46, 0, 219, 31, 0, 240, 61, 113, 240, 39, 89, 240, 55, 89, 244, 53, 2, 249, 53, 2, 254, 53, 2, 258, 80, 58, 264, 53, 2, 264, 75, 80, 266, 51, 46, 266, 53, 44, 268, 51, 107, 269, 82, 28, 271, 80, 28, 271, 139, 28, 278, 27, 0, 282, 29, 7, 283, 46, 0, 268, 31, 0, 288, 51, 101, 289, 29, 7, 289, 36, 20, 296, 52, 47, 296, 52, 72, 296, 52, 42, 296, 52, 92, 296, 51, 86, 296, 52, 53, 301, 94, 62, 301, 53, 53, 301, 94, 16, 301, 95, 15, 301, 99, 16, 301, 100, 61, 301, 104, 62, 302, 94, 61, 307, 89, 61, 309, 51, 30, 309, 53, 28, 311, 38, 0, 315, 53, 7, 315, 43, 7, 339, 139, 20, 341, 139, 18, 350, 141, 20, -15, 65, 0, 0, 80, 13, 0, 80, 28, 0, 80, 43, 0, 80, 58, -15, 2, 0, ];
array[int] of int: nSzBx_1D = [1, 1, 1, 22, 4, 4, 85, 75, 13, 4, 4, 10, 115, 4, 4, 75, 40, 5, 2, 27, 2, 2, 2, 21, 57, 2, 2, 3, 3, 9, 3, 73, 3, 3, 3, 18, 36, 3, 3, 36, 3, 3, 3, 3, 9, 3, 49, 3, 86, 3, 3, 3, 3, 48, 2, 59, 2, 10, 2, 2, 3, 3, 31, 21, 3, 3, 58, 3, 3, 103, 15, 15, 163, 75, 75, 2, 52, 2, 54, 2, 2, 28, 28, 167, 58, 58, 182, 4, 4, 8, 4, 13, 4, 4, 4, 130, 4, 19, 4, 3, 21, 3, 3, 3, 18, 3, 8, 3, 8, 4, 4, 13, 3, 3, 40, 9, 14, 100, 69, 74, 4, 73, 4, 4, 4, 8, 108, 4, 4, 3, 3, 149, 3, 38, 3, 18, 18, 88, 48, 48, 103, 3, 13, 3, 3, 30, 3, 3, 3, 14, 3, 13, 3, 2, 4, 2, 2, 2, 7, 1, 11, 1, 2, 2, 8, 16, 2, 2, 36, 2, 2, 2, 4, 2, 2, 4, 2, 2, 2, 7, 48, 2, 2, 78, 2, 2, 13, 3, 3, 11, 1, 1, 30, 20, 5, 3, 3, 13, 2, 2, 4, 2, 31, 2, 5, 2, 2, 2, 72, 2, 6, 2, 2, 31, 2, 2, 19, 19, 200, 49, 49, 215, 2, 2, 9, 3, 3, 13, 3, 3, 6, 3, 23, 3, 3, 3, 144, 3, 11, 3, 3, 13, 3, 1, 11, 1, 99, 3, 3, 2, 2, 30, 13, 3, 3, 12, 2, 2, 12, 2, 2, 6, 2, 2, 2, 25, 2, 2, 2, 122, 34, 2, 2, 2, 2, 31, 15, 103, 15, 75, 163, 75, 34, 14, 3, 64, 44, 18, 3, 3, 13, 2, 2, 12, 2, 2, 12, 1, 1, 11, 1, 1, 11, 1, 1, 11, 2, 13, 2, 1, 1, 11, 75, 50, 13, 4, 4, 63, 4, 71, 4, 22, 4, 4, 4, 59, 4, 40, 4, 4, 70, 4, 4, 15, 4, 8, 1, 1, 11, 13, 13, 101, 43, 43, 116, 4, 4, 8, 1, 1, 11, 1, 11, 1, 11, 1, 1, 11, 1, 1, 11, 1, 1, 11, 1, 1, 15, 4, 4, 6, 3, 3, 3, 3, 18, 3, 42, 3, 3, 3, 38, 3, 5, 3, 3, 3, 46, 3, 5, 3, 3, 3, 18, 6, 3, 3, 3, 6, 3, 4, 4, 58, 4, 29, 4, 8, 20, 8, 1, 1, 11, 1, 1, 11, 4, 4, 10, 9, 4, 4, 1, 1, 1, 380, 95, 80, 350, 65, 3, 350, 65, 3, 350, 65, 3, 350, 65, 3, 380, 163, 15, ];
array[int] of int: nDSf2Pi = [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, ];
array[int] of int: nBoxCostSupport = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 650000, 0, 0, 0, 650000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 650000, 0, 0, 0, 0, 0, 0, 650000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 650000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 650000, 0, 650000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 650000, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 650000, 0, 0, 0, 0, 650000, ];
array[int] of int: nNodePipe = [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, ];
array[int] of int: nDiam = [2, ];
array[int] of int: fThruRack = [1, ];
array[int] of int: nLLeg_LB = [4, ];
array[int] of int: nLLeg_UB = [380, ];
array[int] of int: nDirNz1 = [4, ];
array[int] of int: nDirNz2 = [3, ];
array[int] of int: nLLegNz1_LB = [2, ];
array[int] of int: nLLegNz1_UB = [30, ];
array[int] of int: nLLegNz2_LB = [2, ];
array[int] of int: nLLegNz2_UB = [30, ];
array[int] of int: nNz1ModuleBox = [73, ];
array[int] of int: nNz2ModuleBox = [24, ];
array[int] of int: nCostPipePerLenUnit = [13000, ];
array[int] of int: nCostBend = [130000, ];
	 %%% The C'' constants for each pipe: E * D(in) / 48 / S_A
array[int] of float: dGCM_Cpp = [34.317964589686405, ];

array[int] of var int: nXNd_1D = [nXNd__1_1_X, nXNd__1_1_Y, nXNd__1_1_Z, nXNd__1_2_X, nXNd__1_2_Y, nXNd__1_2_Z, nXNd__1_3_X, nXNd__1_3_Y, nXNd__1_3_Z, nXNd__1_4_X, nXNd__1_4_Y, nXNd__1_4_Z, nXNd__1_5_X, nXNd__1_5_Y, nXNd__1_5_Z, nXNd__1_6_X, nXNd__1_6_Y, nXNd__1_6_Z, nXNd__1_7_X, nXNd__1_7_Y, nXNd__1_7_Z, nXNd__1_8_X, nXNd__1_8_Y, nXNd__1_8_Z, nXNd__1_9_X, nXNd__1_9_Y, nXNd__1_9_Z, nXNd__1_10_X, nXNd__1_10_Y, nXNd__1_10_Z, ];


/* Pipe routing submodel
 *
 * TODO  Combine with modules?
 * TODO  Ensure 3D element is linearized well
 * Problem: nozzle legs should go INTO their modules.....?
 * Put future pipe nozzles as fixed boxes, removing them before their pipe
 * TODO  CANNOT GO THROUGH PREFERRED RACK LEVEL BASE
 * 
 * CARE with operator precedence. <->, ->, <-, \/, xor, /\, </ >, <=, >=, ...
 * Say b <-> x in a..b instead of b <-> ( x>=a /\ x<=b ) ??
 */

/*
 * SIMPLIFYING
 * Just ensure every node is in a module's 3m zone or 2-3m above ground
 * No leg between disjoint zones ??
 * Into the rack, nozzles can go as far as 6m !!! ???
 * Lower support costs in rack preferred levels - make sure they are disjoint
 * Now they are 0 - nNodeCstSp can be simplified    TODO
 */

/* INPUT
 * - nNodePipe, array of each Node's pipe number, 11111122222222 etc.
 * - nBoxType, for each fixed box: 1-module, 2- fixed pipe leg,
 *     3-module's support zone, 4-rack big,
 *     5-rack pref level (all latter disj and in a bigger rack)
 * - nDSf2Pi, each box' safety distance to pipes
 * - nDSf_Pi2Pi
 * - nDiam, each pipe's diameter
 * - fNoPockets[], flag for each pipe    TODO
 * - fThruRack[], if the pipe has to make a bend on a rack, to avoid going straight over modules
 * - nLLeg_LB[], nLLeg_UB[] per pipe
 * - nDirNz1[], nDirNz2[] (incoming dir for nz2)  for each pipe     TODO variable nozzle dir
 * - nLLegNz1_LB, nLLegNz1_UB, nLLegNz2_LB, nLLegNz2_UB for each pipe
 * - nNz1ModuleBox, nNz2ModuleBox for each pipe
 * - nCostPipePerLenUnit[]
 * - nCostBend[]
 * - nCostSupport0, default support cost per bend
 * - nBoxCostSupport[], support cost in a box, taken only for pref rack levels which should be disjoint
 * 
 * - nLengthUnitMM
 * - dGCM_Cpp[], the flexibility constraint factor for each pipe
 * 
 * - nXBx_1D, nSzBx_1D, fixed boxes' coords & sizes
 * 
 * - nXNd_1D, coord variables for the nodes, organized in a single linear array[1..3n]
 *       ( each pipe's ends fixed )
 */


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% BASIC SETS %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
set of int: TCOORDS = 1..3;
set of int: TBOXES = index_set( nBoxType );
set of int: T_RACKS = { i | i in TBOXES where 4==nBoxType[i] };
set of int: T_RACKPREFLEVELS = { i | i in TBOXES where 5==nBoxType[i] };
set of int: TSUPPORTS = { i | i in TBOXES where 3<=nBoxType[i] };
set of int: TPIPES = index_set( nDiam );
set of int: TPIPENODES = 1..length( nXNd_1D ) div length( TCOORDS );        %% for all pipes
constraint assert( length( TPIPENODES ) * length( TCOORDS ) == length( nXNd_1D ), "ERR 01" );
set of int: TPIPELEGS_RANGE = TPIPENODES;
test isActualLeg( TPIPELEGS_RANGE: iL ) =
                          ( iL<length( TPIPELEGS_RANGE ) /\ nNodePipe[iL+1]==nNodePipe[iL] );
set of int: TPIPELEGS = { i | i in TPIPELEGS_RANGE where isActualLeg(i) };
%%% For each pipe, the 1st leg is always the 1st in the list
%%% (The last leg is dynamic, see fLastLeg[])
test isFirstLeg( TPIPELEGS_RANGE: iL ) = ( 1==iL \/ nNodePipe[iL-1] != nNodePipe[iL] );
test isLastPossLeg( TPIPELEGS: iL ) = ( not isActualLeg(iL+1) );
array[int] of set of int: TPIPELEGS_BYPIPE = [ { i | i in TPIPELEGS where p==nNodePipe[i] } | p in TPIPES ];
array[int] of int: nPipeLeg1st = [ min( TPIPELEGS_BYPIPE[iP] ) | iP in TPIPES ];
array[int] of int: nPipeLegLast = [ max( TPIPELEGS_BYPIPE[iP] ) | iP in TPIPES ];
%% set of int: TCOSTCLASSES = index_set( nCCCost );

int: nOBJCOEFDIVISOR = 100;     %% For Gurobi 6.5, even 1000


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%% TRANSFORMING 1D->N-D DATA ARRAYS %%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
array[int, int] of int: nXBx = array2d( TBOXES, TCOORDS, nXBx_1D );
array[int, int] of int: nSzBx = array2d( TBOXES, TCOORDS, nSzBx_1D );
array[int, int] of int: nXBx2 = array2d( TBOXES, TCOORDS,                      %% The upper-far-right corner
                                         [ nXBx_1D[ik] + nSzBx_1D[ik] | ik in index_set( nXBx_1D ) ] );


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%% TRANSFORMING OTHER DATA %%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%array[int] of int: nPipeLastNodeIndices_0 =
%%  array1d( 0..length( nPipeLastNodeIndices ), [ 0 ] ++ nPipeLastNodeIndices );
%%constraint assert( nPipeLastNodeIndices[ length( nPipeLastNodeIndices ) ] == length( TPIPENODES ) );

array[int] of int: nRadius = [ nDiam[i] div 2 | i in TPIPES ];

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%% TRANSFORMING / CREATING VAR ARRAYS %%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
array[int, int] of var int: nXNd = array2d( TPIPENODES, TCOORDS, nXNd_1D );

%% A leg's boundaries in dim k. Sorted for each leg. Connecting to leg lengths
array[TPIPELEGS_RANGE, TCOORDS] of var lb_array(nXNd_1D)..ub_array(nXNd_1D): nXLeg1;
array[TPIPELEGS_RANGE, TCOORDS] of var lb_array(nXNd_1D)..ub_array(nXNd_1D): nXLeg2;
%% A leg's length in dim k.
array[TPIPELEGS_RANGE, TCOORDS] of var 0..max( nLLeg_UB ): nLLeg;    %% Adding >=0 for pow()
%% A leg's direction flags, 0: zero, 1..3: positive, 4..6: negative.
array[TPIPELEGS_RANGE] of var 0..6: nDirLeg;
%% A leg's existence and 'being last' flags
array[TPIPELEGS_RANGE] of var 0..1: fExistLeg;
array[TPIPELEGS_RANGE] of var 0..1: fLastLeg;
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% First, set variable bounds / fix
constraint forall( iL in TPIPELEGS_RANGE, k in TCOORDS )(
  if not isActualLeg( iL ) then
    nXLeg1[iL,k]==0 /\ nXLeg2[iL,k]==0
    /\ nDirLeg[iL]==0 /\ nLLeg[iL,k]==0 /\ fExistLeg[iL]==0 /\ fLastLeg[iL]==0
  else
       nXLeg1[iL,k] >= min( lb( nXNd[iL,k] ), lb( nXNd[iL+1,k] ) ) - nRadius[ nNodePipe[iL] ]
    /\ nXLeg1[iL,k] <= max( ub( nXNd[iL,k] ), ub( nXNd[iL+1,k] ) ) - nRadius[ nNodePipe[iL] ]
    /\ nXLeg2[iL,k] >= min( lb( nXNd[iL,k] ), lb( nXNd[iL+1,k] ) ) + nRadius[ nNodePipe[iL] ]
    /\ nXLeg2[iL,k] <= max( ub( nXNd[iL,k] ), ub( nXNd[iL+1,k] ) ) + nRadius[ nNodePipe[iL] ]
    /\    %%% LEG LENGTH >= 0
       nLLeg[iL,k] >= 0
    /\
       if isFirstLeg(iL) then
         nDirLeg[iL] == nDirNz1[ nNodePipe[iL] ]
         /\
         if k==(nDirNz1[ nNodePipe[iL] ]-1) mod 3 + 1 then
           nLLeg[iL,k] >= nLLegNz1_LB[ nNodePipe[iL] ] /\ nLLeg[iL,k] <= nLLegNz1_UB[ nNodePipe[iL] ]
         else
           nLLeg[iL,k] == 0
         endif
       elseif isLastPossLeg(iL) then
         nDirLeg[iL] in {0,nDirNz2[ nNodePipe[iL] ]}
         /\
         if k==(nDirNz2[ nNodePipe[iL] ]-1) mod 3 + 1 then
           nLLeg[iL,k] <= nLLegNz2_UB[ nNodePipe[iL] ]
         else
           nLLeg[iL,k] == 0
         endif
       else
                             %%% NOT HERE: nLLeg[iL,k] >= nLLeg_LB[ nNodePipe[iL] ] /\
         nLLeg[iL,k] <= nLLeg_UB[ nNodePipe[iL] ]
       endif
  endif );
%%% ACTUALLY CONSTRAIN LEG BOX ENDS AND CONNECT TO THE LENGTH
constraint forall( iL in TPIPELEGS, k in TCOORDS )(       %% ALWAYS ADD RADIUS, EVEN ON ENDS
%    nXLeg1[iL,k] <= nXNd[iL,k]-nRadius[nNodePipe[iL]] /\ nXLeg1[iL,k] <= nXNd[iL+1,k]-nRadius[nNodePipe[iL]]
    nXLeg1[iL,k] == min( nXNd[iL,k], nXNd[iL+1,k] ) - nRadius[nNodePipe[iL]]
    /\                          %% >=: +nRadius
%    nXLeg2[iL,k] >= nXNd[iL,k]+nRadius[nNodePipe[iL]] /\ nXLeg2[iL,k] >= nXNd[iL+1,k]+nRadius[nNodePipe[iL]]
    nXLeg2[iL,k] == max( nXNd[iL,k], nXNd[iL+1,k] ) + nRadius[nNodePipe[iL]]
    /\       %%% CONNECTING TO LENGTHS
    nLLeg[ iL,k] == nXLeg2[iL,k] - nXLeg1[iL,k] - 2*nRadius[nNodePipe[iL]]
  );
%%% Leg sequence
constraint forall( iP in TPIPES )(
  1==sum( iL in TPIPELEGS_BYPIPE[iP] )
       ( fLastLeg[iL] )                               %% Also constraint fExistLeg's?
  /\ 0==fLastLeg[ nPipeLeg1st[iP] ]                   %% Not the starting 2 legs
  /\ 0==fLastLeg[ nPipeLeg1st[iP]+1 ]
  /\ 1==fExistLeg[ nPipeLeg1st[iP] ]
  /\ 1==fExistLeg[ nPipeLeg1st[iP]+1 ]
  /\ 1==fExistLeg[ nPipeLeg1st[iP]+2 ]
);
constraint forall( iL in TPIPELEGS )(
  if isLastPossLeg(iL) then
    fExistLeg[iL] == fLastLeg[iL]
  else
    fExistLeg[iL] == fExistLeg[iL+1]+fLastLeg[iL]
  endif
  /\
  ( fExistLeg[iL]>0 <-> nDirLeg[iL]>0 )
);
%%% CONNECT LENGTHS TO DIRECTIONS
constraint forall( iL in TPIPELEGS, k in TCOORDS )(
  ( k==nDirLeg[iL] -> ( nLLeg[iL,k] <= nXNd[iL+1,k]-nXNd[iL,k] ) )
  /\
%%  ( (k==nDirLeg[iL]) + (k+3==nDirLeg[iL]) <= ( nLLeg[iL,k] >= nLLeg_LB[ nNodePipe[iL] ] ) )
  ( nDirLeg[iL] in {k, k+3} -> ( nLLeg[iL,k] >= nLLeg_LB[ nNodePipe[iL] ] ) )
  /\
  ( k+3==nDirLeg[iL] -> ( nLLeg[iL,k] <= nXNd[iL,k]-nXNd[iL+1,k] ) )
  /\
%%  ( 0==nDirLeg[iL] -> ( nLLeg[iL,k] <= 0 ) )
  ( not (nDirLeg[iL] in {k,k+3}) -> ( nLLeg[iL,k] <= 0 ) )
);
%%% ORTHOGONALITY OF LEGS  ( => NOT GOING BACK )
constraint forall( iL in TPIPELEGS, k in TCOORDS where not isLastPossLeg(iL) )(
  (nDirLeg[iL]==k) + (nDirLeg[iL]==k+3) + (nDirLeg[iL+1]==k) + (nDirLeg[iL+1]==k+3) <= 1
);
%% Constraining end nozzle lengths
constraint forall( iL in TPIPELEGS, k in TCOORDS )(
  ( 1==fLastLeg[iL] -> ( nDirLeg[iL]==nDirNz2[ nNodePipe[iL] ] ) )
  /\
  ( 1==fLastLeg[iL] -> nLLeg[ iL, (nDirNz2[ nNodePipe[iL] ]-1) mod 3 + 1 ] >= nLLegNz2_LB[ nNodePipe[iL] ] )
  /\
  ( 1==fLastLeg[iL] -> nLLeg[ iL, (nDirNz2[ nNodePipe[iL] ]-1) mod 3 + 1 ] <= nLLegNz2_UB[ nNodePipe[iL] ] )
  /\
  ( 1==fLastLeg[iL] -> nXNd[ iL+1, k ] == nXNd[ nPipeLegLast[nNodePipe[iL]]+1, k ] )    %% Set to the nz2 connection
);       %%% TODO Could add more direct implications on the low-level vars

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% (Non-strict) disjointness of OBSTACLE BOXES & LEGS along each coord axis,
%% regarding SAFETY DISTANCE
%% HOW to handle in & out of a module / support zone?
array[int, int, int] of var bool: bDisjLegBox_K = array3d( TBOXES, TPIPELEGS_RANGE, TCOORDS,
  [ if 2<nBoxType[iB] \/ not isActualLeg(iL) then true
    else
      nXBx2[iB,k] + nDSf2Pi[iB] <= nXLeg1[iL,k] \/ nXBx[iB,k] - nDSf2Pi[iB] >= nXLeg2[iL,k]
    endif
    | iB in TBOXES, iL in TPIPELEGS_RANGE, k in TCOORDS ]
);
constraint forall( iB in TBOXES, iL in TPIPELEGS where 2>=nBoxType[iB]
    /\ ( not isFirstLeg(iL) \/ iB!=nNz1ModuleBox[ nNodePipe[iL] ] ) )(        %% Avoid checking 1st leg X its box
  if iB!=nNz2ModuleBox[ nNodePipe[iL] ] then 
    exists( k in TCOORDS )( bDisjLegBox_K[iB,iL,k] )
  else
    exists( k in TCOORDS )( bDisjLegBox_K[iB,iL,k] )
    \/ 1==fLastLeg[iL] \/ 0==fExistLeg[iL]
  endif
);
%% Disjointness to other pipes' legs. TODO Need own legs??? BUT THEN over 2 legs.
array[int, int, int] of var bool: bLeftLegLeg_K = array3d( TPIPELEGS_RANGE, TPIPELEGS_RANGE, TCOORDS,
  [ if nNodePipe[i1]==nNodePipe[i2] \/ not isActualLeg(i1) \/ not isActualLeg(i2) \/ i1==i2 then true
    else
      nXLeg2[i1,k] + nDSf_Pi2Pi <= nXLeg1[i2,k]
    endif
    | i1 in TPIPELEGS_RANGE, i2 in TPIPELEGS_RANGE, k in TCOORDS] );
constraint forall( i1, i2 in TPIPELEGS where nNodePipe[i1]<nNodePipe[i2] )(
  exists( k in TCOORDS )( bLeftLegLeg_K[ i1, i2, k ] \/ bLeftLegLeg_K[ i2, i1, k ] )
  \/ 0==fExistLeg[i1] \/ 0==fExistLeg[i2]
);
%% BEING IN A SUPPORT ZONE: FOR EACH BEND'S _BOTTOM_
%% This is also registered for rack preferred levels
array[ int, int ] of var bool: bInSZ = array2d( TPIPENODES, TBOXES,
  [
    if nBoxType[iZ]<3 then false
%    elseif isFirstLeg(iN) then true
    else
      forall( k in TCOORDS )(
        if 3==k then                       %% BOTTOM IN THE ZONE
          nXNd[iN,k]-nRadius[nNodePipe[iN]] >= nXBx[iZ,k]
          /\
          nXNd[iN,k]-nRadius[nNodePipe[iN]] <= nXBx2[iZ,k]
%% SEEM 50% longer:          nXNd[iN,k] in (nXBx[iZ,k]+nRadius[nNodePipe[iN]])..(nXBx2[iZ,k]+nRadius[nNodePipe[iN]])
        else                               %% NODE CENTER IN THE ZONE
          nXNd[iN,k] >= nXBx[iZ,k]
          /\
          nXNd[iN,k] <= nXBx2[iZ,k]
%% SEEM 50% longer:          nXNd[iN,k] in nXBx[iZ,k]..nXBx2[iZ,k]
        endif
      )
    endif
  | iN in TPIPENODES, iZ in TBOXES ]
);
%%% ACTUALLY DEMAND FOR EACH NODE TO BE IN A SUPPORT ZONE
constraint forall( iN in TPIPELEGS where not isFirstLeg(iN) )(
  exists( iZ in TSUPPORTS )( bInSZ[ iN, iZ ] )
);
%%% Node being NOT IN ANY PREFERRED SUPPORT LEVEL
array[int] of var 0..1: fNodeNotInPref = [
  if isFirstLeg(iN) \/ not isActualLeg(iN) then 0
  else
    1 - sum( iZ in T_RACKPREFLEVELS )( bInSZ[ iN, iZ ] )
  endif
  | iN in TPIPENODES ];
%%% Node support cost
array[int] of var int: nNodeCstSp = [
  if isFirstLeg(iN) \/ not isActualLeg(iN) then 0
  else
    fExistLeg[iN] *                             %%% MULTIPLY
      ( fNodeNotInPref[ iN ] * (nCostSupport0 div nOBJCOEFDIVISOR + 1) +
        sum( iZ in T_RACKPREFLEVELS )(
             bInSZ[ iN, iZ ] * (nBoxCostSupport[ iZ ] div nOBJCOEFDIVISOR + 1) ) )
  endif
  | iN in TPIPENODES ];
%%% No leg between disjoint support zones of different modules
%%% constraint forall( iL in  ------------------------------
%%% If required, a pipe has to go thru a rack
%%% 13.12.16   NO THIS LOOKS STRANGE. Better forbid jumping between
%%% modules unless to/from rack (how?)
%constraint forall( iP in TPIPES where 1==fThruRack[iP] )(
%  exists( iNode in TPIPELEGS_BYPIPE[iP], iZ in T_RACKS /*where not isFirstLeg*/ )(
%    bInSZ[ iNode, iZ ]
%  )
%);
  
  
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%% FLEXIBILITY %%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

int: nCoefReductionFactor = 1;                  %% !!!!!!!!!!!!!!!!!!11
%%% Length range for all dimensions
%set of int: sLenRange = 0..max( nLLeg_UB );
%constraint trace( "  sLenRange: \(sLenRange)\n" );
%%% The cubes of possible length values
%array[int] of int: nL3 = array1d( sLenRange, [ (l*l*l) div nCoefReductionFactor | l in sLenRange ] );
%%% Cubed length variables
%array[int, int] of var int: nLLeg3 = array2d( TPIPELEGS_RANGE, TCOORDS,
%  [ if dGCM_Cpp[nNodePipe[iL]]<=0.0 then 0 else nL3[ nLLeg[iL, k] ] endif      %% optional
%    | iL in TPIPELEGS_RANGE, k in TCOORDS
%] );
%%% Sums of cubed lengths for all other dimensions, for each pipe
array[int, int ] of var int: nSumLLeg3Orthog = array2d( TPIPES, TCOORDS,
  [  sum( iL in TPIPELEGS_BYPIPE[iP], k1 in TCOORDS diff {k} )(
    if dGCM_Cpp[ iP ]<=0.0 then 0 else 
      pow( nLLeg[iL, k1], 3 ) /*nLLeg3[iL, k1]*/ endif )
    | iP in TPIPES, k in TCOORDS ] );
constraint let {
   %%% The Kappas
   float: dKappaF = int2float(nLengthUnitMM) / 304.8;               %% feet in the length unit
   float: dKappaI = int2float(nLengthUnitMM) / 25.4;                %% inches in the length unit
} in forall( iP in TPIPES, k in TCOORDS )(
    if dGCM_Cpp[iP]<=0.0 then true
    else
      let {
        %%% Nozzle distance in this dim
        int: nDeltaNz = abs( fix(nXNd[ nPipeLeg1st[iP], k ]) - fix(nXNd[ nPipeLegLast[iP]+1, k ]) );
        %%% The constraint coef
        int: nCoefL = ceil( dGCM_Cpp[iP] * int2float(nDeltaNz) / dKappaF );
        %constraint trace ( "  GCM:  PIPE \(iP):  COORD \(k):  CoefL = \(nCoefL)\n" );
      } in forall( iL in TPIPELEGS_BYPIPE[iP], k1 in TCOORDS diff {k} )(
          ((nCoefL + nCoefReductionFactor - 1) div nCoefReductionFactor) * nLLeg[iL,k1] <= nSumLLeg3Orthog[ iP, k ]
        )
    endif
);


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% SOLVE + OBJECTIVE %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
var 1..10000000: objective;              %% ????? Dividing the coefs by nOBJCOEFDIVISOR - needed for Chuffed.   Add +1 to avoid 0
constraint objective =
  sum( iL in TPIPELEGS )( (nCostPipePerLenUnit[ nNodePipe[iL] ] div nOBJCOEFDIVISOR + 1)
          * sum( k in TCOORDS )( nLLeg[iL,k] ) )
  + sum ( iL in TPIPELEGS where not isFirstLeg(iL) )( (nCostBend[ nNodePipe[iL] ] div nOBJCOEFDIVISOR + 1) * fExistLeg[iL] )
  + sum ( iL in TPIPELEGS where not isFirstLeg(iL) )( nNodeCstSp[iL] )
  ;

annotation ann5_relations_grpAll;
ann5_relations_grpAll = seq_search([
    %    int_search( [ objective ], input_order, indomain_split, complete )
    %    ,
 int_search(
            [ [
                fExistLeg[ iL ],
                nDirLeg[ iL ]
              ][k]
              | iL in TPIPELEGS_RANGE, k in 1..2 ]
            ,
            input_order, indomain_split, complete
        )
        , int_search( array1d( nXNd ), input_order, indomain_split, complete )
        , int_search( array1d( nXLeg1 ), input_order, indomain_split, complete )
        , int_search( array1d( nXLeg2 ), input_order, indomain_split, complete )
        , int_search( array1d( nLLeg ), input_order, indomain_split, complete )
        , int_search( fLastLeg, input_order, indomain_split, complete )
    ])
;

 
solve
    :: ann5_relations_grpAll
  minimize
    objective
    ;

%   output ["objective = \(objective);\n" ++
%           "fExistLeg = \(fExistLeg);\n" ++
%           "nDirLeg = \(nDirLeg);\n" ];
   
%%% Uncomment the output declaration to directly produce drawable data on the scaled sizes
%output [
%  "PARALLELEPIPEDS\n"
%]
%++ [
%  if k<=3 then "\(100*nPosXYZ[ m, k ]),\t"
%  elseif k<=6 then "\(100*nSzWLH[ m, k-3 ]),\t"
%  else "  \(m)\n" endif
%  | m in MODULES, k in 1..7 ]
%++ [ "  OBJ = \(obj)\n" ]
