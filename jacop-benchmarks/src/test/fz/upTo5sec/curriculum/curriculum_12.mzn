% curriculum_12.mzn
% vim: ft=zinc ts=4 sw=4 et tw=0
% Ralph Becket <rafe@csse.unimelb.edu.au>
% Wed Oct 31 11:43:32 EST 2007
%
% Adapted from 
% http://www.dcs.st-and.ac.uk/~ianm/CSPLib/prob/prob030/bacp12.dat

include "curriculum.mzn.model";

n_courses = 66;
n_periods = 12;
load_per_period_lb = 10;
load_per_period_ub = 24;
courses_per_period_lb = 2;
courses_per_period_ub = 10;

int: dew100 = 1;
int: fis100 = 2;
int: hcw310 = 3;
int: iwg101 = 4;
int: mat111 = 5;
int: mat121 = 6;
int: dew101 = 7;
int: fis110 = 8;
int: iwi131 = 9;
int: mat112 = 10;
int: mat122 = 11;
int: dewxx0 = 12;
int: fis120 = 13;
int: hcw311 = 14;
int: hxwxx1 = 15;
int: ili142 = 16;
int: mat113 = 17;
int: mat123 = 18;
int: fis130 = 19;
int: ili134 = 20;
int: ili151 = 21;
int: iwm185 = 22;
int: mat124 = 23;
int: fis140 = 24;
int: hxwxx2 = 25;
int: ile260 = 26;
int: ili260 = 27;
int: iwn170 = 28;
int: qui104 = 29;
int: ili231 = 30;
int: ili243 = 31;
int: ili252 = 32;
int: ili273 = 33;
int: mat210 = 34;
int: mat260 = 35;
int: ild208 = 36;
int: ili221 = 37;
int: ili274 = 38;
int: ili281 = 39;
int: iwn270 = 40;
int: mat270 = 41;
int: hrw150 = 42;
int: ili238 = 43;
int: ili242 = 44;
int: ili275 = 45;
int: ili355 = 46;
int: hrw110 = 47;
int: ici393 = 48;
int: ili237 = 49;
int: ili334 = 50;
int: ili363 = 51;
int: iwn261 = 52;
int: hrw100 = 53;
int: ici382 = 54;
int: ili331 = 55;
int: ili362 = 56;
int: ili381 = 57;
int: iln230 = 58;
int: ici313 = 59;
int: ici315 = 60;
int: ici332 = 61;
int: ici344 = 62;
int: icn336 = 63;
int: iwi365 = 64;
int: ici314 = 65;
int: ici367 = 66;

course_load = [
    1, 3, 1, 2, 4,
    4, 1, 5, 3, 4,
    4, 1, 4, 1, 1,
    4, 4, 4, 4, 4,
    3, 3, 4, 4, 1,
    3, 3, 3, 3, 3,
    4, 4, 3, 4, 4,
    3, 4, 3, 3, 3,
    4, 2, 4, 3, 3,
    4, 2, 4, 4, 4,
    3, 3, 2, 4, 4,
    3, 3, 3, 2, 2,
    3, 4, 3, 3, 2,
    2
];

constraint prerequisite(dew101, dew100);
constraint prerequisite(fis110, fis100);
constraint prerequisite(fis110, mat121);
constraint prerequisite(mat112, mat111);
constraint prerequisite(mat122, mat111);
constraint prerequisite(mat122, mat121);
constraint prerequisite(dewxx0, dew101);
constraint prerequisite(fis120, fis110);
constraint prerequisite(fis120, mat122);
constraint prerequisite(hcw311, hcw310);
constraint prerequisite(ili142, iwi131);
constraint prerequisite(mat113, mat112);
constraint prerequisite(mat113, mat122);
constraint prerequisite(mat123, mat112);
constraint prerequisite(mat123, mat122);
constraint prerequisite(fis130, fis110);
constraint prerequisite(fis130, mat122);
constraint prerequisite(ili134, iwi131);
constraint prerequisite(ili151, mat112);
constraint prerequisite(mat124, mat113);
constraint prerequisite(mat124, mat123);
constraint prerequisite(fis140, fis120);
constraint prerequisite(fis140, fis130);
constraint prerequisite(ile260, fis120);
constraint prerequisite(ile260, mat124);
constraint prerequisite(ili231, iwi131);
constraint prerequisite(ili252, iwi131);
constraint prerequisite(ili273, ili260);
constraint prerequisite(mat210, mat113);
constraint prerequisite(mat260, iwi131);
constraint prerequisite(mat260, mat113);
constraint prerequisite(mat260, mat123);
constraint prerequisite(ili221, ili134);
constraint prerequisite(ili221, ili231);
constraint prerequisite(ili221, mat260);
constraint prerequisite(ili274, ili273);
constraint prerequisite(ili281, mat260);
constraint prerequisite(mat270, iwi131);
constraint prerequisite(mat270, mat113);
constraint prerequisite(mat270, mat123);
constraint prerequisite(ili238, ili134);
constraint prerequisite(ili242, ili142);
constraint prerequisite(ili275, ili274);
constraint prerequisite(ili355, ili221);
constraint prerequisite(hrw110, hrw150);
constraint prerequisite(ici393, mat210);
constraint prerequisite(ici393, mat260);
constraint prerequisite(ili237, ili231);
constraint prerequisite(ili237, ili252);
constraint prerequisite(ili334, ili238);
constraint prerequisite(ili363, ili273);
constraint prerequisite(hrw100, hrw110);
constraint prerequisite(ici382, ili334);
constraint prerequisite(ili331, ili238);
constraint prerequisite(ili331, ili274);
constraint prerequisite(ili362, ili363);
constraint prerequisite(ili381, ili281);
constraint prerequisite(ili381, mat210);
constraint prerequisite(iln230, iwn170);
constraint prerequisite(ici313, ili331);
constraint prerequisite(ici332, ici393);
constraint prerequisite(ici332, ili331);
constraint prerequisite(ici344, ili243);
constraint prerequisite(icn336, ici393);
constraint prerequisite(ici314, ici313);

