
int: n; %% number of rows
int: m; %% number of columns

var int: cost;
array[-1..n+2,-1..m+2] of var 0..1: a; %% whether i,j is alive

array[0..n+1, 0..m+1] of var 0..9: s; %% sum of the 8 squares around i,j


constraint forall(i in -1..n+2)( a[i,-1] = 0 /\ a[i,0] = 0 /\ 
                                 a[i,m+1] = 0 /\ a[i, m+2] = 0);

constraint forall(j in -1..m+2)( a[-1, j] = 0 /\ a[0,j] = 0 /\ 
                                 a[n+1,j] = 0 /\ a[n+2,j] = 0);

constraint
    forall(i in 0..n+1, j in 0..m+1)(
    	     s[i,j] = a[i-1,j-1] + a[i-1,j] + a[i-1,j+1]
	            + a[i,j-1]              + a[i,j+1]
		    + a[i+1,j-1] + a[i+1,j] + a[i+1,j+1] /\
	     ((a[i,j] == 1) -> (2 <= s[i,j] /\ s[i,j] <= 3)) /\
	     ((a[i,j] == 0) -> (s[i,j] != 3))
    );

constraint cost = sum(i in 1..n, j in 1..m)(a[i,j]);

solve %% :: int_search(a, in_order, indomain_max, complete)
      maximize cost;


output ["cost = ", show(cost), 
        ";\na = [|\n"] ++
	[ show(a[i,j]) ++  
          if j == m then if i == n then "|];\n" else "|\n" endif
	            else "," endif |
	  	       i in 1..n, j in 1..m ]++
	[ "\n\n%     " ] ++
	[ (if fix(a[i,j]) = 1 then "X" else " " endif) ++ 
          if j == m then "\n%     " else "" endif | 
         i in 1..n, j in 1..m ];
    
