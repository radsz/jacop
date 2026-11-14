% curriculum_8.mzn
% vim: ft=zinc ts=4 sw=4 et tw=0
% Ralph Becket <rafe@csse.unimelb.edu.au>
% Wed Oct 31 11:43:32 EST 2007
%
% Adapted from 
% http://www.dcs.st-and.ac.uk/~ianm/CSPLib/prob/prob030/bacp8.dat

include "curriculum.mzn.model";

n_courses = 46;
n_periods = 8;
load_per_period_lb = 10;
load_per_period_ub = 24;
courses_per_period_lb = 2;
courses_per_period_ub = 10;

int: dew100 = 1;
int: fis100 = 2;
int: hcw310 = 3;
int: iwg101 = 4;
int: mat190 = 5;
int: mat192 = 6;
int: dew101 = 7;
int: fis101 = 8;
int: iwi131 = 9;
int: mat191 = 10;
int: mat193 = 11;
int: fis102 = 12;
int: hxwxx1 = 13;
int: iei134 = 14;
int: iei141 = 15;
int: mat194 = 16;
int: dewxx0 = 17;
int: hcw311 = 18;
int: iei132 = 19;
int: iei133 = 20;
int: iei142 = 21;
int: iei162 = 22;
int: iwn170 = 23;
int: mat195 = 24;
int: hxwxx2 = 25;
int: iei231 = 26;
int: iei241 = 27;
int: iei271 = 28;
int: iei281 = 29;
int: iwn261 = 30;
int: hfw120 = 31;
int: iei233 = 32;
int: iei238 = 33;
int: iei261 = 34;
int: iei272 = 35;
int: iei273 = 36;
int: iei161 = 37;
int: iei232 = 38;
int: iei262 = 39;
int: iei274 = 40;
int: iwi365 = 41;
int: iwn270 = 42;
int: hrw130 = 43;
int: iei218 = 44;
int: iei219 = 45;
int: iei248 = 46;

course_load = [
    1,  3,  1,  2,  4, 
    4,  1,  5,  3,  4, 
    4,  5,  1,  3,  3, 
    4,  1,  1,  3,  3, 
    3,  3,  3,  3,  1, 
    4,  4,  3,  3,  3, 
    2,  4,  3,  3,  3, 
    3,  3,  3,  3,  3, 
    3,  3,  2,  3,  3, 
    3
];

constraint prerequisite(dew101, dew100);
constraint prerequisite(fis101, fis100);
constraint prerequisite(fis101, mat192);
constraint prerequisite(mat191, mat190);
constraint prerequisite(mat193, mat190);
constraint prerequisite(mat193, mat192);
constraint prerequisite(fis102, fis101);
constraint prerequisite(fis102, mat193);
constraint prerequisite(iei134, iwi131);
constraint prerequisite(iei141, iwi131);
constraint prerequisite(mat194, mat191 );
constraint prerequisite(mat194, mat193);
constraint prerequisite(dewxx0, dew101);
constraint prerequisite(hcw311, hcw310);
constraint prerequisite(iei132, iei134);
constraint prerequisite(iei133, iei134);
constraint prerequisite(iei142, iei141);
constraint prerequisite(mat195, mat194);
constraint prerequisite(iei231, iei134);
constraint prerequisite(iei241, iei142);
constraint prerequisite(iei271, iei162);
constraint prerequisite(iei281, mat195);
constraint prerequisite(iei233, iei231);
constraint prerequisite(iei238, iei231);
constraint prerequisite(iei261, iwn261);
constraint prerequisite(iei272, iei271);
constraint prerequisite(iei273, iei271);
constraint prerequisite(iei273, iei271);
constraint prerequisite(iei161, iwn261);
constraint prerequisite(iei161, iwn261);
constraint prerequisite(iei232, iei273);
constraint prerequisite(iei232, iei273);
constraint prerequisite(iei262, iwn261);
constraint prerequisite(iei274, iei273);
constraint prerequisite(iei274, iei273);
constraint prerequisite(iei219, iei232);
constraint prerequisite(iei248, iei233);
constraint prerequisite(iei248, iei233);

