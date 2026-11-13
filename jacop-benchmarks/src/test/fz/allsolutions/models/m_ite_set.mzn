array[1..3] of var bool: b;
array[1..2] of var set of 1..3: s;
var set of 1..3: r;
constraint r = if b[1] then s[1] elseif b[2] then s[2] else {1, 3} endif;
constraint card(s[1]) <= 2;
constraint 2 in r \/ b[3];
solve satisfy;
