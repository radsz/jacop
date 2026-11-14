%------------------------------------------------------------------------------%
% 
% Chosen Key Differential Cryptanalysis
%
% Authors: 
%   David Gerault, Marine Minier, Christine Solnon
% Published at CP 2016: 
%   Constraint Programming Models for Chosen Key Differential Cryptanalysis
%
%------------------------------------------------------------------------------%
int: n; % Number of rounds
int: objective; % Max objective value

int: KEY_BITS; % Number of bits in the key
int: BLOCK_BITS=128; % Number of bits in the blocks
int: KC=KEY_BITS div 32; % Number of columns per round of key schedule
int: BC=BLOCK_BITS div 32; % Number of columns per round 
int: NBK=KC + n * BC div KC; % Number of variables to represent the components of the key (cf. paper)

array[0..n-2, 0..BC-1, 0..3] of var 0..1: deltaY; % State before ARK
array[0..n-1, 0..BC-1,0..3] of var 0..1: deltaX; % State after ARK
array[0..n-1, 0..BC-1,0..3] of var 0..1: deltaSR; % State after ShiftRows
array[0..n-1, 0..BC-1,0..3] of var 0..1: deltaK; % Key
array[0..n-1, 0..BC-1,0..3,0..NBK-1] of var 0..1: Kcomp; % The components of the key
array[0..3,0..n-1,0..BC-1,0..n-1,0..BC-1] of var 0..1: eqK; % eqK[i][r1][j1][r2][j2] => The byte values of DeltaK[r1,i,j1] and [r2,i,j2] are equal.
array[0..n-1,0..BC-1] of var 0..4: colX; %   colX[r][j] = The sum for i in 0..3 of DeltaY[r][i][j]
array[0..n-1,0..BC-1] of var 0..4: colSRX; % colSRX[r][j] = The sum for i in 0..3 of SR(DeltaY)[r][i][j]
array[0..n-1,0..BC-1] of var 0..4: colK; %   colK[r][j] = The sum for i in 0..3 of DeltaK[r][i][j]

%The sum to minimize
constraint sum(r in 0..n-1, j in 0..BC-1) (colSRX[r,j]) + sum(J in 0..BC*n -1 where J mod KC == KC-1 )(colK[J div BC, J mod BC])=objective; 
 
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Initialisation of the redundant variables. 
constraint forall (r in 0..n-1, j in 0..BC-1) ( 
                    colX[r,j]=sum(i in 0..3)(deltaX[r,j,i]) /\
                    colK[r,j]=sum(i in 0..3)(deltaK[r,j,i]) /\
                    colSRX[r,j]=sum(i in 0..3)(deltaSR[r,j,i])        
);

constraint initKS(deltaK, Kcomp);
constraint ARK(deltaY, deltaK, deltaX); %Add Round Key
constraint SR(deltaX,deltaSR); % MDS property
constraint MC(colSRX,deltaY); % MDS property
constraint KS(deltaK,Kcomp,eqK); % Key schedule
constraint EQrelations(deltaK,Kcomp,eqK); % If (in byte values) DK[r][i][j] == DK[r2][i][j2] and DK[r2][i][j2] == DK[r3][i][j3] then DK[r][i][j] == DK[r3][i][j3]
constraint linearMC(deltaY, deltaK, deltaX,deltaSR,eqK,colSRX); % Cardinalities before and after MC


% The search heuristic. 
solve :: seq_search([ 
int_search(

          [colK[J div BC, J mod BC] | J in 0..BC*n -1 where J mod KC == KC-1] ++ 
          [colSRX[r,j] | r in 0..n-1, j in 0..BC-1] , smallest, indomain_min, complete) , 
         int_search(   
          array1d(deltaSR)++
          [deltaK[J div BC ,J mod BC,i] | J in 0..BC*n -1, i in 0..3 where J mod KC == KC-1] ++ 
          [colX[J div BC, J mod BC] | J in 0..BC*n -1 where J mod KC==KC-1] ++    
          [deltaY[J div BC ,J mod BC,i] | J in 0..BC*(n-1) -1, i in 0..3 where J mod KC == KC-1] ++
          [deltaK[J div BC,J mod BC,i] | J in 0..BC*n -1, i in 0..3 where J mod KC != KC-1] ++ 
          [colK[J div BC,J mod BC] | J in 0..BC*n -1 where J mod KC != KC-1 ] ++ 
          [colX[J div BC, J mod BC] | J in 0..BC*n -1 where J mod KC!=KC-1] ++  
          [deltaX[r,j,i] | r in 0..n-1,  j in 0..3, i in 0..3]  ++ 
          [deltaY[J div BC ,J mod BC,i ] | J in 0..BC*(n-1) -1, i in 0..3 where J mod KC != KC-1] , smallest
, indomain_max, complete)])
       satisfy;


output [
"deltaX = array3d(0..\(n-1), 0..\(BC-1),0..3,\(deltaX));\n"
++"deltaY = array3d(0..\(n-2), 0..\(BC-1),0..3,\(deltaY));\n"
++"deltaK = array3d(0..\(n-1), 0..\(BC-1),0..3,\(deltaK));\n"
++"deltaSR = array3d(0..\(n-1), 0..\(BC-1),0..3,\(deltaSR));\n"
++"%% objective = \(objective);\n"
];


% output [ show([if r>0 then deltaY[r-1,j,i] else 0 endif | j in 0..BC-1] ) ++ " "++show([deltaK[r,j,i] | j in 0..BC-1]) ++ " "++ show([deltaX[r,j,i]| j in 0..BC-1]) ++ " " ++ show([deltaSR[r,j,i] | j in 0..BC-1] ) ++ " "++ if i mod 3==0 /\ i>0 then "\n\n" else "\n" endif ++ if i == 3 /\ r==n-1 then show(objective) else "" endif | r in 0..n-1, i in 0..3];


% regular xor, except 1 xor 1 can be either 0 or 1.
predicate XOR(var 0..1: a,var 0..1: b,var 0..1: c) =
      a+b+c!=1 
    ;
%xor with equivalence propagation
predicate XOR2(var 0..1: a,var 0..1: b,var 0..1: c, var 0..1: eqab,var 0..1: eqac, var 0..1: eqbc ) =
      a+b+c!=1 /\
      eqab = 1-c /\
      eqac = 1-b /\
      eqbc = 1-a 
   ;

%Add round key
predicate ARK(array[0..n-2,0..3,0..BC-1] of var 0..1: DY, array[0..n-1,0..3,0..BC-1] of var 0..1: DK, array[0..n-1,0..3,0..BC-1] of var 0..1: DX ) =
 forall(r in 1..n-1,j in 0..BC-1, i in 0..3) (
       XOR(DY[r-1,j,i], DK[r,j,i], DX[r,j,i])    
)
;
%Shiftrows
predicate SR(array[0..n-1,0..BC-1,0..3] of var 0..1: DX,array[0..n-1,0..BC-1,0..3] of var 0..1: DSR) =
   forall(r in 0..n-1,j in 0..BC-1, i in 0..3) (
       DSR[r,j,i]=DX[r,((j+i) mod BC),i]
);        

% Mixcolumns
predicate MC(array[0..n-1,0..BC-1] of var 0..4: CSRX,array[0..n-2,0..3,0..BC-1] of var 0..1: DY) =
   forall(r in 0..n-2, j in 0..BC-1) (
          (CSRX[r,j] + sum(i in 0..3)(DY[r,j,i])) in {0,5,6,7,8} 
  ) 
;


%Initialization of the components
predicate initKS(array[0..n-1,0..BC-1,0..3] of var 0..1: DK, array[0..n-1,0..BC-1,0..3, 0..NBK-1] of var 0..1: Kcomp
) =
forall (J in 0..n*BC-1,  i in 0..3) (
let {int: r = J div BC, int: j = J mod BC} in 
  forall (k in 0..NBK-1) (
      if J<KC then    % for the first key schedule round
         if k==J then Kcomp[r,j,i,k]=DK[r,j,i] else Kcomp[r,j,i,k]=0 endif % initialize the components corresponding to the key values
      else if J mod KC == 0 then % else, for SB positions (for AES 128, corresponds to the first column of DK for each round)
       if k==(J div KC)*BC+j then 
         Kcomp[r,j,i,k]= DK[(J-1) div BC, (J+BC-1) mod BC ,(i+1) mod 4]  % New component for the result of SB
       else 
         Kcomp[r,j,i,k]=Kcomp[(J-KC) div BC,(J-KC) mod BC,i,k]  % the rest of the components = the ones of the last column of the previous round
      endif
     else true endif
    endif
  )
)
;

%Key schedule. Some of the constraints for the last column of the key are in KSInit
predicate KS(array[0..n-1,0..3,0..BC-1] of var 0..1: DK, array[0..n-1,0..BC-1,0..3, 0..NBK-1] of var 0..1: Kcomp, array[0..3,0..n-1,0..BC-1,0..n-1,0..BC-1] of var 0..1: EQ 
) =
 
forall (J in KC..n*BC-1,  i in 0..3) (
let {int: r = J div BC, int: j = J mod BC} in 
 
  if (J mod KC) == 0 then 
    XOR(
      DK[(J-KC) div BC, (J-KC) mod BC, i], %a
      DK[(J-1) div BC, (J+BC-1) mod BC, (i+1) mod 4], %b
      DK[r,j,i] %c
) 
  else 
    XOR2(DK[(J-KC) div BC, (J-KC) mod BC,i],   %a
        DK[(J-1) div BC,(J+BC-1) mod BC,i], %b
        DK[r,j,i],                             %c
        EQ[i,(J-1) div BC,(J+BC-1) mod BC,(J-KC) div BC,(J-KC) mod BC], %eqab
        EQ[i,r,j,(J-KC) div BC,(J-KC) mod BC], %eqac
        EQ[i,r,j,(J-1) div BC,(J+BC-1) mod BC],%eqbc
        ) 
        /\
    forall (k in 0..NBK-1) ( % XOR of the components
        Kcomp[r,j,i,k]= bool2int((Kcomp[(J-KC) div BC, (J-KC) mod BC,i,k] * DK[(J-KC) div BC,(J-KC) mod BC,i]) != 
         (Kcomp[(J-1) div BC,  (J+BC-1) mod BC,i,k] * DK [(J-1) div BC,(J+BC-1) mod BC,i]))) 
   endif	
  /\ sum([Kcomp[r,j,i,k] |k in 0..NBK-1]) + DK[r,j,i] != 1  % If only 1 component, binary value =1. If 0, 0. Else, undef

% Not really usefull, does not filter any solution 

 % /\ if sum([Kcomp[r,i,j,k] |k in 0..NBK-1])==1 /\ sum([Kcomp[r,i,j,k] |k in 0..KC-1])==1 then
 %     forall(k in 0..KC-1)(if Kcomp[r,i,j,k]==1 then EQ[i,r,j, k div BC,k mod BC]==1 else true endif) else true endif
)
;


predicate EQrelations(
    array[0..n-1,0..3,0..BC-1] of var 0..1: DK, 
    array[0..n-1,0..BC-1,0..3, 0..NBK-1] of var 0..1: Kcomp, 
    array[0..3,0..n-1,0..BC-1,0..n-1,0..BC-1] of var 0..1: EQ 
) =
    forall(J in 0..n*BC-1,  J2 in J+1..n*BC-1) ( 
        let {
            int: r = J div BC, 
            int: j = J mod BC, 
            int: r2 = J2 div BC, 
            int: j2 = J2 mod BC
        } in 
            forall (i in 0..3) (
                ((EQ[i,r,j,r2,j2]==1) -> (DK[r,j,i]==DK[r2,j2,i])) /\ % EQ(a,b) => A=B
                EQ[i,r,j,r2,j2] = EQ[i,r2,j2,r,j] /\    % symmetry
                ((forall(k in 0..NBK-1) (Kcomp[r,j,i,k]==Kcomp[r2,j2,i,k])) -> (EQ[i,r,j,r2,j2]=1))  /\% Va=Vb => EQ(a,b)
                (DK[r,j,i]+DK[r2,j2,i] + EQ[i,r,j,r2,j2]) != 0 /\ % a+b+EQ(a,b) !=0
                forall (J3 in 0..n*BC-1) ( 
                    let {int: r3 = J3 div BC, int: j3 = J3 mod BC} in
                    EQ[i,r,j,r3,j3] + EQ[i,r,j,r2,j2] + EQ[i,r2,j2,r3,j3] != 2 %transitivity
                )

            )
    );

predicate linearMC(array[0..n-2,0..3,0..BC-1] of var 0..1: DY, array[0..n-1,0..3,0..BC-1] of var 0..1: DK, array[0..n-1,0..3,0..BC-1] of var 0..1: DX, array[0..n-1,0..3,0..BC-1] of var 0..1: DSR, array[0..3,0..n-1,0..BC-1,0..n-1,0..BC-1] of var 0..1: EQ, array[0..n-1,0..BC-1] of var 0..4: CSRX) =

forall(J in BC..n*BC-1,  J2 in J+1..n*BC-1) ( 
let {int: r = J div BC, int: j = J mod BC, int: r2 = J2 div BC, int: j2 = J2 mod BC} in 
     let {
      var bool: DIFF_SX= % SB(A) != SB(B) (bytes). 
      (  exists(i in 0..3) % There is a difference if any of the following is true
        (
             DSR[r-1,j,i] != DSR[r2-1,j2,i] % different bit values
         \/  DY[r-1,j,i]  != DY[r2-1,j2,i]                       % different after MC (since A==b => MC(A) == MC(B)) 
         \/  EQ[i,r,j,r2,j2] + DX[r,j,i] + DX [r2,j2,i] == 0    % MC(SB(A)) xor K1 + MC(SB(B)) xor K2 = 0 and not(EQ(K1, K2))
         \/  ( (EQ[i,r,j,r2,j2] + DK[r,j,i] == 2) /\ (DX[r,j,i] != DX[r2,j2,i]) ) % MC(SB(A)) xor K != MC(SB(B)) xor K
         ) 
     ),
     var 0..4: EQ_SRX= sum (i in 0..3) ( % Lower bound on the equalities between SR(SB(A)) and SR(SB(B))
        bool2int((DSR[r-1,j,i] + DSR[r2-1,j2,i]) == 0)),
     var 0..4: EQ_Y= sum (i in 0..3) ( % Lower bound on the equalities between MC(SB(A)) and MC(SB(B))
        bool2int((EQ[i,r,j,r2,j2] ==1 /\ DX[r,j,i] + DX [r2,j2,i] == 0)
           \/  (DY[r-1,j,i] + DY[r2-1,j2,i])==0 )
      )
    } in
        % If S(A) != S(B) (in bytes) then MDS property
        DIFF_SX -> EQ_SRX+EQ_Y <= 3
)
;
