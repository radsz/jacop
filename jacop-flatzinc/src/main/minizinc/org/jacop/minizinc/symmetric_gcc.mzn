/** @doc Constrains the 0/1 matrix x of a many-to-many assignment: row i has row_count[i] ones and
  column j has col_count[j] ones (symmetric_gcc of the Global Constraint Catalog, with the
  assignment as a 0/1 matrix instead of set variables). JaCoP's SymmetricGCC constraint uses the
  flow network of Kocjan and Kreuger, "Filtering methods for symmetric cardinality constraint",
  CPAIOR 2004: the matrix is domain consistent and the counts bounds consistent. The predicate is
  specific to JaCoP; the row and column sums are kept for the linear relaxation.
*/
predicate symmetric_gcc(array[int, int] of var 0..1: x, array[int] of var int: row_count,
                        array[int] of var int: col_count) =
    assert(index_set(row_count) = index_set_1of2(x),
           "symmetric_gcc: row_count must have the index set of the rows of x") /\
    assert(index_set(col_count) = index_set_2of2(x),
           "symmetric_gcc: col_count must have the index set of the columns of x") /\
    forall(i in index_set_1of2(x))(sum(j in index_set_2of2(x))(x[i, j]) = row_count[i]) /\
    forall(j in index_set_2of2(x))(sum(i in index_set_1of2(x))(x[i, j]) = col_count[j]) /\
    jacop_symmetric_gcc(array1d(x), card(index_set_2of2(x)), row_count, col_count);

/** @doc The same with the assignment as Boolean variables. */
predicate symmetric_gcc(array[int, int] of var bool: x, array[int] of var int: row_count,
                        array[int] of var int: col_count) =
    symmetric_gcc(array2d(index_set_1of2(x), index_set_2of2(x), [bool2int(b) | b in x]),
                  row_count, col_count);

predicate jacop_symmetric_gcc(array[int] of var int: x, int: columns,
                              array[int] of var int: row_count, array[int] of var int: col_count);
