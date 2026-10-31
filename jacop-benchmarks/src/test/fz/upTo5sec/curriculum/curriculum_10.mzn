% curriculum_10.mzn
% vim: ft=zinc ts=4 sw=4 et tw=0
% Ralph Becket <rafe@csse.unimelb.edu.au>
% Wed Oct 31 11:43:32 EST 2007
%
% Adapted from 
% http://www.dcs.st-and.ac.uk/~ianm/CSPLib/prob/prob030/bacp10.dat

include "curriculum.mzn.model";

n_courses = 42;
n_periods = 10;
load_per_period_lb = 10;
load_per_period_ub = 24;
courses_per_period_lb = 2;
courses_per_period_ub = 10;

int: dew100 = 1;
int: fis100 = 2;
int: hrwxx1 = 3;
int: iwg101 = 4;
int: mat021 = 5;
int: qui010 = 6;
int: dew101 = 7;
int: fis110 = 8;
int: hrwxx2 = 9;
int: iwi131 = 10;
int: mat022 = 11;
int: dewxx0 = 12;
int: fis120 = 13;
int: hcw310 = 14;
int: hrwxx3 = 15;
int: ili134 = 16;
int: ili151 = 17;
int: mat023 = 18;
int: hcw311 = 19;
int: ili135 = 20;
int: ili153 = 21;
int: ili260 = 22;
int: iwn261 = 23;
int: mat024 = 24;
int: fis130 = 25;
int: ili239 = 26;
int: ili245 = 27;
int: ili253 = 28;
int: fis140 = 29;
int: ili236 = 30;
int: ili243 = 31;
int: ili270 = 32;
int: ili280 = 33;
int: ici344 = 34;
int: ili263 = 35;
int: ili332 = 36;
int: ili355 = 37;
int: iwn170 = 38;
int: icdxx1 = 39;
int: ili362 = 40;
int: iwn270 = 41;
int: icdxx2 = 42;

course_load = [
    1, 3, 2, 2, 5, 
    3, 1, 5, 2, 3, 
    5, 1, 4, 1, 2, 
    4, 3, 4, 1, 4, 
    3, 3, 3, 4, 4, 
    4, 4, 4, 4, 4, 
    4, 3, 4, 4, 3, 
    4, 4, 3, 3, 3, 
    3, 3 
];

constraint prerequisite(dew101, dew100);
constraint prerequisite(fis110, fis100);
constraint prerequisite(fis110, mat021);
constraint prerequisite(mat022, mat021);
constraint prerequisite(dewxx0, dew101);
constraint prerequisite(fis120, fis110);
constraint prerequisite(fis120, mat022);
constraint prerequisite(ili134, iwi131);
constraint prerequisite(ili151, iwi131);
constraint prerequisite(mat023, mat022);
constraint prerequisite(hcw311, hcw310);
constraint prerequisite(ili135, ili134);
constraint prerequisite(ili153, ili134);
constraint prerequisite(ili153, ili151);
constraint prerequisite(mat024, mat023);
constraint prerequisite(fis130, fis110);
constraint prerequisite(fis130, mat022);
constraint prerequisite(ili239, ili135);
constraint prerequisite(ili245, ili153);
constraint prerequisite(ili253, ili153);
constraint prerequisite(fis140, fis120);
constraint prerequisite(fis140, fis130);
constraint prerequisite(ili236, ili239);
constraint prerequisite(ili243, ili245);
constraint prerequisite(ili270, ili260);
constraint prerequisite(ili270, iwn261);
constraint prerequisite(ili280, mat024);
constraint prerequisite(ici344, ili243);
constraint prerequisite(ili263, ili260);
constraint prerequisite(ili263, iwn261);
constraint prerequisite(ili332, ili236);
constraint prerequisite(ili355, ili153);
constraint prerequisite(ili355, ili280);
constraint prerequisite(ili362, ili263);

