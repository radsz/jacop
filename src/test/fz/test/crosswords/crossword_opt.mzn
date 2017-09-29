%------------------------------------------------------------------------------%
% Crossword puzzle (optimisation version)
%
% A grid is given and it needs to be filled in with words from the dictionary.
% However, words are seeked that give the crossword the most value.
%------------------------------------------------------------------------------%
% Parameters related to the grid

int: width;     % Width of the grid
int: height;    % Height of the grid

set of int: ROW = 1..height;    % Set of rows
set of int: COL = 1..width;     % Set of columns

array[ROW,COL] of bool: grid;   % false - "black" cell (no letters)
                                % true - cell requiring a letter

%------------------------------------------------------------------------------%
% Parameters related to the dictionary

    % Alphabet
    %
enum LETTER =              {a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p, q,r,s,t,u,v,w,x,y, z};
array[int] of int: value = [1,3,3,2,1,4,2,4,1,8,5,1,3,1,1,3,10,1,1,1,1,4,4,8,4,10];
    
    % Words of length 1
    %
int: words1;
set of int: WORDS1 = 1..words1;
array[WORDS1, 1..1] of LETTER: dict1;

    % Words of length 2
    %
int: words2;
set of int: WORDS2 = 1..words2;
array[WORDS2, 1..2] of LETTER: dict2;

    % Words of length 3
    %
int: words3;
set of int: WORDS3 = 1..words3;
array[WORDS3, 1..3] of LETTER: dict3;

    % Words of length 4
    %
int: words4;
set of int: WORDS4 = 1..words4;
array[WORDS4, 1..4] of LETTER: dict4;

    % Words of length 5
    %
int: words5;
set of int: WORDS5 = 1..words5;
array[WORDS5, 1..5] of LETTER: dict5;

    % Words of length 6
    %
int: words6;
set of int: WORDS6 = 1..words6;
array[WORDS6, 1..6] of LETTER: dict6;

    % Words of length 7
    %
int: words7;
set of int: WORDS7 = 1..words7;
array[WORDS7, 1..7] of LETTER: dict7;

    % Words of length 8
    %
int: words8;
set of int: WORDS8 = 1..words8;
array[WORDS8, 1..8] of LETTER: dict8;

    % Words of length 9
    %
int: words9;
set of int: WORDS9 = 1..words9;
array[WORDS9, 1..9] of LETTER: dict9;

    % Words of length 10
    %
int: words10;
set of int: WORDS10 = 1..words10;
array[WORDS10, 1..10] of LETTER: dict10;

    % Words of length 11
    %
int: words11;
set of int: WORDS11 = 1..words11;
array[WORDS11, 1..11] of LETTER: dict11;

    % Words of length 12
    %
int: words12;
set of int: WORDS12 = 1..words12;
array[WORDS12, 1..12] of LETTER: dict12;

    % Words of length 13
    %
int: words13;
set of int: WORDS13 = 1..words13;
array[WORDS13, 1..13] of LETTER: dict13;

    % Words of length 14
    %
int: words14;
set of int: WORDS14 = 1..words14;
array[WORDS14, 1..14] of LETTER: dict14;

    % Words of length 15
    %
int: words15;
set of int: WORDS15 = 1..words15;
array[WORDS15, 1..15] of LETTER: dict15;

    % Words of length 16
    %
int: words16;
set of int: WORDS16 = 1..words16;
array[WORDS16, 1..16] of LETTER: dict16;

    % Words of length 17
    %
int: words17;
set of int: WORDS17 = 1..words17;
array[WORDS17, 1..17] of LETTER: dict17;

    % Words of length 18
    %
int: words18;
set of int: WORDS18 = 1..words18;
array[WORDS18, 1..18] of LETTER: dict18;

    % Words of length 19
    %
int: words19;
set of int: WORDS19 = 1..words19;
array[WORDS19, 1..19] of LETTER: dict19;

    % Words of length 20
    %
int: words20;
set of int: WORDS20 = 1..words20;
array[WORDS20, 1..20] of LETTER: dict20;

    % Words of length 21
    %
int: words21;
set of int: WORDS21 = 1..words21;
array[WORDS21, 1..21] of LETTER: dict21;

    % Words of length 22
    %
int: words22;
set of int: WORDS22 = 1..words22;
array[WORDS22, 1..22] of LETTER: dict22;

int: words23; array[int,int] of LETTER: dict23;
int: words24; array[int,int] of LETTER: dict24;
int: words25; array[int,int] of LETTER: dict25;
int: words26; array[int,int] of LETTER: dict26;
int: words27; array[int,int] of LETTER: dict27;
int: words28; array[int,int] of LETTER: dict28;
int: words29; array[int,int] of LETTER: dict29;
int: words30; array[int,int] of LETTER: dict30;
int: words31; array[int,int] of LETTER: dict31;
int: words32; array[int,int] of LETTER: dict32;
int: words33; array[int,int] of LETTER: dict33;
int: words34; array[int,int] of LETTER: dict34;
int: words35; array[int,int] of LETTER: dict35;
int: words36; array[int,int] of LETTER: dict36;
int: words37; array[int,int] of LETTER: dict37;
int: words38; array[int,int] of LETTER: dict38;
int: words39; array[int,int] of LETTER: dict39;
int: words40; array[int,int] of LETTER: dict40;
int: words41; array[int,int] of LETTER: dict41;
int: words42; array[int,int] of LETTER: dict42;
int: words43; array[int,int] of LETTER: dict43;
int: words44; array[int,int] of LETTER: dict44;
int: words45; array[int,int] of LETTER: dict45;

int: max_words = max([
    words2,words3,words4,words5,words6,words7,words8,words9,
    words10,words11,words12,words13,words14,words15,words16,words17,words18,words19,
    words20,words21,words22,words23,words24,words25,words26,words27,words28,words29,
    words30,words31,words32,words33,words34,words35,words36,words37,words38,words39,
    words40,words41,words42,words43,words44,words45
]);
set of int: WORD = 1..max_words;             
 

int: number_of_clues;
set of int: CLUE = 1..number_of_clues;

array[CLUE] of ROW: startrow;
array[CLUE] of COL: startcol;
array[CLUE] of bool: down;
array[CLUE] of int: leng;

%------------------------------------------------------------------------------%
% Variables

array[ROW,COL] of var LETTER: xx;   % Variables for the letter for each cell
array[CLUE] of var WORD: ww;        % Variables for the word for each clue
var min(value) * (height*width) .. max(value) * (height * width): objective;

%------------------------------------------------------------------------------%
% Includes

include "alldifferent.mzn";

%------------------------------------------------------------------------------%
% Predicates

predicate table_row(array [int] of var int: x, array [int,int] of int: t, var int: row) =
    forall(i in index_set(x))(
        x[i] = t[row, i]
    );
                 
%------------------------------------------------------------------------------%
% Constraints

    % Objective
    %
constraint objective = sum(r in ROW, c in COL)( value[ xx[r,c] ] );

    % A word only can appear once
    %
constraint forall(l in 2..22)(
    alldifferent(c in CLUE where leng[c] = l)(ww[c])
);

    % Pre-assign "black" cells with the letter 'a'
    %
constraint forall(r in ROW, c in COL)(
    not grid[r,c] -> xx[r,c] = a
);

    % Word constraints
    %
constraint forall(clue in CLUE)(
    let { 
        int: r = startrow[clue]; 
        int: c = startcol[clue]; 
    } in (
        if down[clue] then
           %% vertical word starting at (r,c)
           let {int: len = leng[clue]; 
                array[int] of var LETTER: clueword = [ xx[i,c] | i in r..r+len-1 ];
               } in
           if len = 1 then table_row(clueword, dict1, ww[clue])
           elseif len =  2 then table_row(clueword, dict2, ww[clue])
           elseif len =  3 then table_row(clueword, dict3, ww[clue])
           elseif len =  4 then table_row(clueword, dict4, ww[clue])
           elseif len =  5 then table_row(clueword, dict5, ww[clue])
           elseif len =  6 then table_row(clueword, dict6, ww[clue])
           elseif len =  7 then table_row(clueword, dict7, ww[clue])
           elseif len =  8 then table_row(clueword, dict8, ww[clue])
           elseif len =  9 then table_row(clueword, dict9, ww[clue])
           elseif len = 10 then table_row(clueword, dict10, ww[clue])
           elseif len = 11 then table_row(clueword, dict11, ww[clue])
           elseif len = 12 then table_row(clueword, dict12, ww[clue])
           elseif len = 13 then table_row(clueword, dict13, ww[clue])
           elseif len = 14 then table_row(clueword, dict14, ww[clue])
           elseif len = 15 then table_row(clueword, dict15, ww[clue])
           elseif len = 16 then table_row(clueword, dict16, ww[clue])
           elseif len = 17 then table_row(clueword, dict17, ww[clue])
           elseif len = 18 then table_row(clueword, dict18, ww[clue])
           elseif len = 19 then table_row(clueword, dict19, ww[clue])
           elseif len = 20 then table_row(clueword, dict20, ww[clue])
           elseif len = 21 then table_row(clueword, dict21, ww[clue])
           elseif len = 22 then table_row(clueword, dict22, ww[clue])
           else 
              assert(len > 22, "word length too long \(len) > 22\n")
           endif
        else 
           %% horizontal word starting at (r,c)
           let {int: len = leng[clue]; 
                array[int] of var LETTER: clueword = [ xx[r,i] | i in c..c+len-1 ];
                } in 
           if len = 1 then table_row(clueword, dict1, ww[clue])
           elseif len = 2 then table_row(clueword, dict2, ww[clue])
           elseif len = 3 then table_row(clueword, dict3, ww[clue])
           elseif len = 4 then table_row(clueword, dict4, ww[clue])
           elseif len = 5 then table_row(clueword, dict5, ww[clue])
           elseif len = 6 then table_row(clueword, dict6, ww[clue])
           elseif len = 7 then table_row(clueword, dict7, ww[clue])
           elseif len = 8 then table_row(clueword, dict8, ww[clue])
           elseif len = 9 then table_row(clueword, dict9, ww[clue])
           elseif len = 10 then table_row(clueword, dict10, ww[clue])
           elseif len = 11 then table_row(clueword, dict11, ww[clue])
           elseif len = 12 then table_row(clueword, dict12, ww[clue])
           elseif len = 13 then table_row(clueword, dict13, ww[clue])
           elseif len = 14 then table_row(clueword, dict14, ww[clue])
           elseif len = 15 then table_row(clueword, dict15, ww[clue])
           elseif len = 16 then table_row(clueword, dict16, ww[clue])
           elseif len = 17 then table_row(clueword, dict17, ww[clue])
           elseif len = 18 then table_row(clueword, dict18, ww[clue])
           elseif len = 19 then table_row(clueword, dict19, ww[clue])
           elseif len = 20 then table_row(clueword, dict20, ww[clue])
           elseif len = 21 then table_row(clueword, dict21, ww[clue])
           elseif len = 22 then table_row(clueword, dict22, ww[clue])
           else
              assert(len > 22, "word length too long \(len) > 22\n")
           endif
        endif
    )
);     

%------------------------------------------------------------------------------%
% Search and solve item

ann: searchLetter1 = int_search(array1d(xx), first_fail, indomain_split, complete);
ann: searchLetter2 = int_search(array1d(xx), first_fail, indomain_min, complete);

ann: searchWord1 = int_search(ww, first_fail, indomain_split, complete);
ann: searchWord2 = int_search(ww, first_fail, indomain_min, complete);

ann: search = searchLetter1;

solve 
    :: search
    maximize objective;

%------------------------------------------------------------------------------%
% Output item

output [ 
    if c = 1 then "% " else "" endif 
++  if grid[r,c] then show(xx[r,c]) else "#" endif 
++  if c = width then "\n" else "" endif
| r in ROW, c in COL 
] ++ [ 
    "ww = \(ww);\n",
    "objective = \(objective);\n",
] ;
