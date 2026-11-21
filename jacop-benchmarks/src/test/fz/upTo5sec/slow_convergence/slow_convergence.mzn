int: n;
array [0..n] of var 0..10*n: y;
array [0..n] of var 0..10*n: x;

constraint
    forall(i in 2..n)(
        y[i-1] - y[i] <= 0 
    );

constraint
    forall(i in 1..n)(
        y[0] - y[i] <= n - i + 1
    );

constraint
    y[n] - x[0] <= 0;


constraint
    forall(i in 1..n-1)(
        forall(j in i+1..n)(
            x[i] - x[j] <= 0
        )
    );

constraint y[0] >= n;

solve satisfy;

output [
    "x = ", show(x), "\n",
    "y = ", show(y), "\n"
];
