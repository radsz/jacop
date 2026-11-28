include "global_cardinality.mzn";

/** @doc Constrains value values[k] to occur row_count[r, k] times in row r of x and
  col_count[c, k] times in column c (colored_matrix of the Global Constraint Catalog, the
  cardinality matrix of Régin and Gomes, CP 2004). Rostering models have it: persons by days, with
  the shifts as values. JaCoP's CardinalityMatrix constraint links the rows and the columns with one
  flow per value; the cardinality constraints of the rows and columns are posted as well, as Régin
  and Gomes do. The predicate is specific to JaCoP.
*/
predicate cardinality_matrix(array[int, int] of var int: x, array[int] of int: values,
                             array[int, int] of var int: row_count,
                             array[int, int] of var int: col_count) =
    assert(index_set_1of2(row_count) = index_set_1of2(x) /\ index_set_2of2(row_count) = index_set(values),
           "cardinality_matrix: row_count must have a row of x per row and a value per column") /\
    assert(index_set_1of2(col_count) = index_set_2of2(x) /\ index_set_2of2(col_count) = index_set(values),
           "cardinality_matrix: col_count must have a column of x per row and a value per column") /\
    forall(r in index_set_1of2(x))(
      global_cardinality([x[r, c] | c in index_set_2of2(x)], values,
                         [row_count[r, k] | k in index_set(values)])) /\
    forall(c in index_set_2of2(x))(
      global_cardinality([x[r, c] | r in index_set_1of2(x)], values,
                         [col_count[c, k] | k in index_set(values)])) /\
    jacop_cardinality_matrix(array1d(x), card(index_set_2of2(x)), values,
                             array1d(row_count), array1d(col_count));

predicate jacop_cardinality_matrix(array[int] of var int: x, int: columns, array[int] of int: values,
                                   array[int] of var int: row_count, array[int] of var int: col_count);
