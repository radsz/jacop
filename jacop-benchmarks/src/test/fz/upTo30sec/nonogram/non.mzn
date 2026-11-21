include "globals.mzn";
int: X;
int: Y;

int: maxlen;

array [1..Y,1..maxlen] of int: rows;

array [1..X,1..maxlen] of int: cols;

array[1..2, 1..2, 1..2] of 0..1: nonmul = 
    array3d(1..2, 1..2, 1..2,
        [0, 0, 1, 1,
         1, 0, 0, 1]
    );

array[1..2, 1..2, 1..2] of 0..1: nonadd =
    array3d(1..2, 1..2, 1..2,
        [0, 0, 0, 1,
         1, 0, 0, 1]
    );

% variables
%
array[1..Y, 1..X] of var 1..2: A;

% All variables in a region must be different
% Ordering to ensure each variable is handled exactly once
predicate nonogram_row(
        array[1..Y, 1..X] of var 1..2: A,
        array[int] of 0..1: cons,
        int: row) =
    nonogram([A[row, v] | v in 1..X], cons);

predicate nonogram_col(
        array[1..Y, 1..X] of var 1..2: A,
        array[int] of 0..1: cons,
        int: col) = 
    nonogram([A[v,col] | v in 1..Y], cons);

predicate nonogram(array[int] of var 1..2: A, array [int] of int: cons) = 
    let {
          int: n = if cons[1] = 0 then 0 else max(index_set(cons)) endif,
          array [1..n + 1, 1..2] of int: consarr =
              if cons[1] = 0 then [|1, 0|] 
              else array2d(1..n + 1, 1..2,
                [1, 2] ++
                [    i * nonmul[cons[i - 1] + 1, cons[i] + 1, s] + 
                     nonadd[cons[i - 1] + 1, cons[i] + 1, s] 
                     | i in 2..n, s in 1..2 
                ] ++ 
                [n+1,0]
              )
              endif
     } in (
         regular(A, n + 1, 2, consarr, 1, {n + 1})
     );

constraint forall(i in 1..Y) (
    nonogram_row(A, [rows[i, j] | j in 1..maxlen where rows[i, j] >= 0], i)
);

constraint forall(i in 1..X) (
    nonogram_col(A, [cols[i, j] | j in 1..maxlen where cols[i, j] >= 0], i)
);

solve :: int_search(array1d(1..X*Y,A),input_order,indomain_max,complete) satisfy;

output [
    if fix(A[r, c]) = 1 then " " else "." endif ++ 
    if c = Y then "\n" else " " endif
    | r in 1..X, c in 1..Y
];
