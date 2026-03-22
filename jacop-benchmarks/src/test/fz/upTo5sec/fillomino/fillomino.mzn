% vim: ft=zinc ts=4 sw=4 et

int: rows;
int: cols;
set of int: row = 1..rows;
set of int: col = 1..cols;
array [row, col] of 0..9: puzzle;

set of int: id = 1..(rows * cols);
set of int: Time = 1..min(9, rows + cols);
array [id] of var 0..(rows * cols): size;
                                        % size[a] size of area a.
array [row, col] of var id: area;
                                        % area[r, c] is the area owning (r, c).
array [row, col] of var Time: when;
                                        % when[r, c] is when (r, c) is fixed.
array [row, col] of var 1..9: what;
                                        % what[r, c] is the number at (r, c).

array [row, col] of int: same_in_range =
    array2d(row, col, [ sum([ bool2int(puzzle[rr, cc] = puzzle[r, c])
          | rr in row, cc in col
            where after(r, c, rr, cc)
            /\    abs(rr - r) + abs(cc - c) < puzzle[r, c]
          ])
    | r in row, c in col
    ]);

% Initialise the problem.
constraint
    forall (r in row, c in col where puzzle[r, c] != 0) (
        let { int: s = puzzle[r, c] } in
            what[r, c] = s
        % Optimisation: fix unambiguous "roots" at time 1.
        /\  if   same_in_range[r, c] = 0
            then when[r, c] = 1 /\ area[r, c] = (r - 1) * cols + c
            else true
            endif
    );

% Each cell contains the number corresponding to the size of its area.
constraint
    forall (r in row, c in col) (
        what[r, c] = size[area[r, c]]
    );

% Each area's size is the number of cells in that area.
constraint
    forall (a in id) (
        size[a] = sum (r in row, c in col) (bool2int(area[r, c] = a))
    );

% Each cell is either the "root" of an area or is an extension of a
% neighbouring cell.
constraint
    forall (r in row, c in col) (
        (   when[r, c] = 1
        /\  area[r, c] = (r - 1) * cols + c
        )
    \/  (   1 < when[r, c]
        /\  (   joins(r, c, r - 1, c)
            \/  joins(r, c, r + 1, c)
            \/  joins(r, c, r, c - 1)
            \/  joins(r, c, r, c + 1)
            )
        )
    );

predicate joins(row: r, col: c, int: rr, int: cc) =
    if ok(rr, cc) then
        when[r, c] = 1 + when[rr, cc]
    /\  area[r, c] = area[rr, cc]
    /\  what[r, c] = what[rr, cc]
    else
        false
    endif;

% Optimisation: the "when" label is actually the distance of a cell in an
% area from the area "root".  This distance cannot be larger than the size
% of the area.
constraint
    forall (r in row, c in col) (
        when[r, c] <= size[area[r, c]]
    );

% (r, c) is ok if it is on the board.
test ok(int: r, int: c) = r in row /\ c in col;

% (rr, cc) is after (r, c) if it is below it or to the right.
test after(int: r, int: c, int: rr, int: cc) =
    (   rr > r
    \/  (   rr = r
        /\  cc > c
        )
    );

% Neighbouring areas must have different sizes.
constraint
    forall (r in row, c in col where c > 1) (
        let { var id: a = area[r, c - 1], var id: b = area[r, c] } in
        (a != b) = (size[a] != size[b])
    );

constraint
    forall (r in row, c in col where r > 1) (
        let { var id: a = area[r - 1, c], var id: b = area[r, c] } in
        (a != b) = (size[a] != size[b])
    );

% Any solution will do.  Try labelling by area.
solve
    :: seq_search([
        int_search([area[r, c] | r in row, c in col],
            input_order, indomain_min, complete),
        int_search(array1d(1..rows*cols, when), first_fail, indomain_min, complete)
    ])
    satisfy;

output [
    "what = array2d(", show(row), ", ", show(col), ", ", show(what), ");\n",
    "when = array2d(", show(row), ", ", show(col), ", ", show(when), ");\n",
    "area = array2d(", show(row), ", ", show(col), ", ", show(area), ");\n"
];
