predicate jacop_count(array[int] of var int: x, int: y, var int: c);

predicate fzn_count_eq(array[int] of var int: x, var int: y, var int: c) =
    c = sum(i in index_set(x)) ( bool2int(x[i] == y) );
%     among_var(c, x, [y]);  %% this is less efficinet, even generating less search nodes... :(
     
predicate fzn_count_eq(array[int] of var int: x, int: y, var int: c) =
    jacop_count(x, y, c);
%     let {
%         set of int: set_y = {y}
%	 }
%     in 
%         among(c, x, set_y);
