% The expansion of hook_prob_mdd.mzn: the probability numerator over 4 of each decision.
array[0..1] of var 0..2: x;
var 0..16: p;
var 0..4: num = if x[0] = 0 then (if x[1] in {0, 1} then 3 else 1 endif)
                elseif x[0] = 2 then (if x[1] in {0, 1} then 2 else 0 endif)
                else 0 endif;
constraint p = (16 * num) div 4;
constraint p >= 4;
solve satisfy;
