predicate jacop_geost(
                      int        : k       ,
    array[int] of int        : rect_size   ,
    array[int] of int        : rect_offset ,
    array[int    ] of set of int : shape   , 
    array[int] of var int    : x           ,
    array[int    ] of var int    : kind
);

% jacop_geost numbers rectangles and shapes from 1: rectangle r is row r of rect_size and
% rect_offset, and kind[o] = s selects shape[s].
function array[int] of set of int: jacop_geost_shapes(array[int,int] of int: rect_size,
                                                      array[int] of set of int: shape) =
    let { int: r0 = min(index_set_1of2(rect_size)) - 1 } in
    [ { r - r0 | r in shape[s] } | s in index_set(shape) ];

function array[int] of var int: jacop_geost_kinds(array[int] of set of int: shape,
                                                  array[int] of var int: kind) =
    let { int: s0 = min(index_set(shape)) - 1 } in
    if s0 = 0 then array1d(kind) else [ kind[o] - s0 | o in index_set(kind) ] endif;

% The native constraint requires every rectangle to have a positive size in every dimension.
test jacop_geost_positive_sizes(array[int,int] of int: rect_size) =
    forall(r in index_set_1of2(rect_size), j in index_set_2of2(rect_size))(rect_size[r,j] > 0);

predicate jacop_geost_decomposition(
                      int        : k           ,
    array[int,int] of int        : rect_size   ,
    array[int,int] of int        : rect_offset ,
    array[int    ] of set of int : shape       ,
    array[int,int] of var int    : x           ,
    array[int    ] of var int    : kind
) =
    let {
      set of int: DIMS = 1..k;
      set of int: OBJECTS = index_set(kind);
    } in
    forall(o1, o2 in OBJECTS where o1 < o2)(
      forall(s1 in dom(kind[o1]) intersect index_set(shape),
             s2 in dom(kind[o2]) intersect index_set(shape))(
        (kind[o1] = s1 /\ kind[o2] = s2) ->
          forall(r1 in shape[s1], r2 in shape[s2])(
            exists(j in DIMS)(
                 x[o1,j] + rect_offset[r1,j] + rect_size[r1,j] <= x[o2,j] + rect_offset[r2,j]
              \/ x[o2,j] + rect_offset[r2,j] + rect_size[r2,j] <= x[o1,j] + rect_offset[r1,j]
            )
          )
      )
    );

predicate fzn_geost(
                      int        : k           ,
    array[int,int] of int        : rect_size   ,
    array[int,int] of int        : rect_offset ,
    array[int    ] of set of int : shape       , 
    array[int,int] of var int    : x           ,
    array[int    ] of var int    : kind
) =
    forall(o in index_set(kind))(kind[o] in index_set(shape))
    /\
    if jacop_geost_positive_sizes(rect_size) then
	jacop_geost(k, array1d(rect_size), array1d(rect_offset), jacop_geost_shapes(rect_size, shape),
                    array1d(x), jacop_geost_kinds(shape, kind))
    else
        jacop_geost_decomposition(k, rect_size, rect_offset, shape, x, kind)
    endif
    ;
