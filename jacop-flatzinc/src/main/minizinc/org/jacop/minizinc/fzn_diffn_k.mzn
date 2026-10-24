include "diffn.mzn";
include "geost.mzn";

predicate fzn_diffn_k(array[int,int] of var int: box_posn,
                  array[int,int] of var int: box_size) =
     let {
       set of int: DIMS = index_set_2of2(box_posn);
       set of int: BOXES = index_set_1of2(box_posn)
     } in
     if card(DIMS) = 2 then
       diffn([ box_posn[i,min(DIMS)] | i in BOXES ],
             [ box_posn[i,max(DIMS)] | i in BOXES ],
             [ box_size[i,min(DIMS)] | i in BOXES ],
             [ box_size[i,max(DIMS)] | i in BOXES ] )
     else if is_fixed(box_size) then % all sizes are constants
        let {
          array[BOXES, DIMS] of int: rect_size = array2d(BOXES, DIMS,  [fix(box_size[i,j]) | i in BOXES, j in DIMS]);
          array[BOXES, DIMS] of int: rect_offset = array2d(BOXES, DIMS, [0 | i in BOXES, j in DIMS]);
          array[BOXES] of set of int: shape = [{i} | i in BOXES];
          array[BOXES] of var int: kind = [i | i in BOXES];
        } in
          geost(card(DIMS), rect_size, rect_offset, shape, box_posn, kind)
        else
           forall(b1, b2 in index_set_1of2(box_posn) where b1 < b2)
             (fzn_diffn_nonoverlap_k([ box_posn[b1,j] | j in DIMS ],   
                               [ box_size[b1,j] | j in DIMS ], 
                               [ box_posn[b2,j] | j in DIMS ],   
                               [ box_size[b2,j] | j in DIMS ] ) 
              )
           endif
     endif;

predicate fzn_diffn_nonoverlap_k(array[int] of var int: x1, 
                             array[int] of var int: w1, 
                             array[int] of var int: x2, 
                             array[int] of var int: w2) = 
    exists(j in index_set(x1))
        (x1[j] + w1[j] <= x2[j] \/ x2[j] + w2[j] <= x1[j]);
