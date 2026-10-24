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

predicate fzn_geost(
                      int        : k           ,
    array[int,int] of int        : rect_size   ,
    array[int,int] of int        : rect_offset ,
    array[int    ] of set of int : shape       , 
    array[int,int] of var int    : x           ,
    array[int    ] of var int    : kind
) =
	jacop_geost(k, array1d(rect_size), array1d(rect_offset), jacop_geost_shapes(rect_size, shape),
                    array1d(x), jacop_geost_kinds(shape, kind))
    ;
