% JaCoP graph constraints (org.jacop.constraints.graph). Nodes are numbered from base, the
% smallest index of ns; from and to hold node numbers.

predicate jacop_reachable(array[int] of int: from, array[int] of int: to, var int: r,
                          array[int] of var bool: ns, array[int] of var bool: es, int: base);
predicate jacop_dreachable(array[int] of int: from, array[int] of int: to, var int: r,
                           array[int] of var bool: ns, array[int] of var bool: es, int: base);
predicate jacop_connected(array[int] of int: from, array[int] of int: to,
                          array[int] of var bool: ns, array[int] of var bool: es, int: base);
predicate jacop_dconnected(array[int] of int: from, array[int] of int: to,
                           array[int] of var bool: ns, array[int] of var bool: es, int: base);
predicate jacop_tree(array[int] of int: from, array[int] of int: to, var int: r,
                     array[int] of var bool: ns, array[int] of var bool: es, int: base);
predicate jacop_dtree(array[int] of int: from, array[int] of int: to, var int: r,
                      array[int] of var bool: ns, array[int] of var bool: es, int: base);
predicate jacop_path(array[int] of int: from, array[int] of int: to, var int: s, var int: t,
                     array[int] of var bool: ns, array[int] of var bool: es, int: base);
predicate jacop_dpath(array[int] of int: from, array[int] of int: to, var int: s, var int: t,
                      array[int] of var bool: ns, array[int] of var bool: es, int: base);
predicate jacop_bounded_path(array[int] of int: from, array[int] of int: to, array[int] of int: w,
                             var int: s, var int: t, array[int] of var bool: ns,
                             array[int] of var bool: es, var int: K, int: base);
predicate jacop_bounded_dpath(array[int] of int: from, array[int] of int: to, array[int] of int: w,
                              var int: s, var int: t, array[int] of var bool: ns,
                              array[int] of var bool: es, var int: K, int: base);
predicate jacop_steiner(array[int] of int: from, array[int] of int: to, array[int] of int: w,
                        array[int] of var bool: ns, array[int] of var bool: es, var int: K,
                        int: base);
predicate jacop_dsteiner(array[int] of int: from, array[int] of int: to, array[int] of int: w,
                         var int: r, array[int] of var bool: ns, array[int] of var bool: es,
                         var int: K, int: base);
predicate jacop_wst(int: N, array[int] of int: from, array[int] of int: to, array[int] of int: w,
                    array[int] of var bool: es, var int: K);
predicate jacop_dwst(int: N, array[int] of int: from, array[int] of int: to, array[int] of int: w,
                     var int: r, array[int] of var bool: es, var int: K);
