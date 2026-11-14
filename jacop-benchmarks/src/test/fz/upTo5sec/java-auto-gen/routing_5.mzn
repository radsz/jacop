include "globals.mzn";
array[1..10] of int: valuesToOrder_2 = [36,39,42,45,48,51,54,57,60,63];
array[1..10] of var 1..10: chooseOrderIndex_2;
array[1..10] of var {36,39,42,45,48,51,54,57,60,63}: chooseOrderVal_2;
constraint alldifferent (chooseOrderIndex_2);
constraint forall (i in 1..10) (valuesToOrder_2[chooseOrderIndex_2[i]] = chooseOrderVal_2[i]);
var {36,39,42,45,48,51,54,57,60,63}: listget_814; %optimise.state.ListGet@32e
constraint listget_814 = chooseOrderVal_2[1];

var {36,39,42,45,48,51,54,57,60,63}: stop_826; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_826;
constraint stop_826 = [listget_814, 63][istop_826];

var 1..10: locationID_832; %ref ref (Literal: 0 [0]).stop -21.locationID -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).stop -21.locationID -7
var 1..10: ilocationID_832;
constraint [36, 39, 42, 45, 48, 51, 54, 57, 60, 63, stop_826][ilocationID_832] = stop_826;
constraint ((stop_826 = 36)) -> ilocationID_832 >= 1;
constraint ((stop_826 = 39)) -> ilocationID_832 >= 2;
constraint ((stop_826 = 42)) -> ilocationID_832 >= 3;
constraint ((stop_826 = 45)) -> ilocationID_832 >= 4;
constraint ((stop_826 = 48)) -> ilocationID_832 >= 5;
constraint ((stop_826 = 51)) -> ilocationID_832 >= 6;
constraint ((stop_826 = 54)) -> ilocationID_832 >= 7;
constraint ((stop_826 = 57)) -> ilocationID_832 >= 8;
constraint ((stop_826 = 60)) -> ilocationID_832 >= 9;
constraint ((stop_826 = 63)) -> ilocationID_832 >= 10;
constraint locationID_832 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10][ilocationID_832];

var 1..10: ret_getLocation_836; %ref (Literal: 0 [0]).ret_getLocation -22
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getLocation -22
var 1..1: iret_getLocation_836;
constraint ret_getLocation_836 = [locationID_832, 10][iret_getLocation_836];

var 1..10: nextLocation_843; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_843;
constraint nextLocation_843 = [ret_getLocation_836, 10][inextLocation_843];

var 1..10: location2_855; %ref (Literal: 0 [0]).location2 -25
% doing constraints for lookup query: ref (Literal: 0 [0]).location2 -25
var 1..1: ilocation2_855;
constraint location2_855 = [nextLocation_843, 10][ilocation2_855];

var 1..10: unnamed_858; %ref (Literal: 0 [0]).unnamed -28
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -28
var 1..1: iunnamed_858;
constraint unnamed_858 = [location2_855, 10][iunnamed_858];

var {2,5,7,11,12,14,18,19}: mapget_859; %optimise.state.MapGet@35b
% doing constraints for lookup query: optimise.state.MapGet@35b
var 1..10: imapget_859;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_858][imapget_859] = unnamed_858;
constraint ((unnamed_858 = 1)) -> imapget_859 >= 1;
constraint ((unnamed_858 = 2)) -> imapget_859 >= 2;
constraint ((unnamed_858 = 3)) -> imapget_859 >= 3;
constraint ((unnamed_858 = 4)) -> imapget_859 >= 4;
constraint ((unnamed_858 = 5)) -> imapget_859 >= 5;
constraint ((unnamed_858 = 6)) -> imapget_859 >= 6;
constraint ((unnamed_858 = 7)) -> imapget_859 >= 7;
constraint ((unnamed_858 = 8)) -> imapget_859 >= 8;
constraint ((unnamed_858 = 9)) -> imapget_859 >= 9;
constraint ((unnamed_858 = 10)) -> imapget_859 >= 10;
constraint mapget_859 = [5, 19, 18, 19, 12, 2, 7, 2, 14, 11, 19][imapget_859];

var {2,5,7,11,12,14,18,19}: ret_travelTime_863; %ref (Literal: 0 [0]).ret_travelTime -26
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_travelTime -26
var 1..1: iret_travelTime_863;
constraint ret_travelTime_863 = [mapget_859, 19][iret_travelTime_863];

var {2,5,7,11,12,14,18,19}: Add_864 = ret_travelTime_863;

var 1..10: nextLocation_866; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_866;
constraint nextLocation_866 = [ret_getLocation_836, 10][inextLocation_866];

var {36,39,42,45,48,51,54,57,60,63}: listget_879; %optimise.state.ListGet@36f
constraint listget_879 = chooseOrderVal_2[2];

var {36,39,42,45,48,51,54,57,60,63}: stop_891; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_891;
constraint stop_891 = [listget_879, 63][istop_891];

var 1..10: locationID_897; %ref ref (Literal: 0 [0]).stop -21.locationID -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).stop -21.locationID -7
var 1..10: ilocationID_897;
constraint [36, 39, 42, 45, 48, 51, 54, 57, 60, 63, stop_891][ilocationID_897] = stop_891;
constraint ((stop_891 = 36)) -> ilocationID_897 >= 1;
constraint ((stop_891 = 39)) -> ilocationID_897 >= 2;
constraint ((stop_891 = 42)) -> ilocationID_897 >= 3;
constraint ((stop_891 = 45)) -> ilocationID_897 >= 4;
constraint ((stop_891 = 48)) -> ilocationID_897 >= 5;
constraint ((stop_891 = 51)) -> ilocationID_897 >= 6;
constraint ((stop_891 = 54)) -> ilocationID_897 >= 7;
constraint ((stop_891 = 57)) -> ilocationID_897 >= 8;
constraint ((stop_891 = 60)) -> ilocationID_897 >= 9;
constraint ((stop_891 = 63)) -> ilocationID_897 >= 10;
constraint locationID_897 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10][ilocationID_897];

var 1..10: ret_getLocation_901; %ref (Literal: 0 [0]).ret_getLocation -22
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getLocation -22
var 1..1: iret_getLocation_901;
constraint ret_getLocation_901 = [locationID_897, 10][iret_getLocation_901];

var {2,5,7,11,12,14,18,19}: currentTime_904; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_904;
constraint currentTime_904 = [Add_864, 19][icurrentTime_904];

var 1..10: currentLocation_905; %ref (Literal: 0 [0]).currentLocation -19
% doing constraints for lookup query: ref (Literal: 0 [0]).currentLocation -19
var 1..1: icurrentLocation_905;
constraint currentLocation_905 = [nextLocation_866, 10][icurrentLocation_905];

var 1..10: nextLocation_908; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_908;
constraint nextLocation_908 = [ret_getLocation_901, 10][inextLocation_908];

var 1..10: location1_915; %ref (Literal: 0 [0]).location1 -24
% doing constraints for lookup query: ref (Literal: 0 [0]).location1 -24
var 1..1: ilocation1_915;
constraint location1_915 = [currentLocation_905, 10][ilocation1_915];

var 1..10: unnamed_918; %ref (Literal: 0 [0]).unnamed -27
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -27
var 1..1: iunnamed_918;
constraint unnamed_918 = [location1_915, 10][iunnamed_918];

var {20,24,25,27,28,29,30,32,33,34}: mapget_919; %optimise.state.MapGet@397
% doing constraints for lookup query: optimise.state.MapGet@397
var 1..10: imapget_919;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_918][imapget_919] = unnamed_918;
constraint ((unnamed_918 = 1)) -> imapget_919 >= 1;
constraint ((unnamed_918 = 2)) -> imapget_919 >= 2;
constraint ((unnamed_918 = 3)) -> imapget_919 >= 3;
constraint ((unnamed_918 = 4)) -> imapget_919 >= 4;
constraint ((unnamed_918 = 5)) -> imapget_919 >= 5;
constraint ((unnamed_918 = 6)) -> imapget_919 >= 6;
constraint ((unnamed_918 = 7)) -> imapget_919 >= 7;
constraint ((unnamed_918 = 8)) -> imapget_919 >= 8;
constraint ((unnamed_918 = 9)) -> imapget_919 >= 9;
constraint ((unnamed_918 = 10)) -> imapget_919 >= 10;
constraint mapget_919 = [20, 24, 25, 27, 28, 29, 30, 32, 33, 34, 34][imapget_919];

var 1..10: location2_920; %ref (Literal: 0 [0]).location2 -25
% doing constraints for lookup query: ref (Literal: 0 [0]).location2 -25
var 1..1: ilocation2_920;
constraint location2_920 = [nextLocation_908, 10][ilocation2_920];

var 1..10: unnamed_923; %ref (Literal: 0 [0]).unnamed -28
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -28
var 1..1: iunnamed_923;
constraint unnamed_923 = [location2_920, 10][iunnamed_923];

var 0..20: mapget_924; %optimise.state.MapGet@39c
% doing constraints for lookup query: optimise.state.MapGet@39c
var 1..100: imapget_924;
constraint [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, mapget_919][imapget_924] = mapget_919;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_923][imapget_924] = unnamed_923;
constraint (((mapget_919 = 20) /\ (unnamed_923 = 1))) -> imapget_924 >= 1;
constraint (((mapget_919 = 20) /\ (unnamed_923 = 2))) -> imapget_924 >= 2;
constraint (((mapget_919 = 20) /\ (unnamed_923 = 3))) -> imapget_924 >= 3;
constraint (((mapget_919 = 20) /\ (unnamed_923 = 4))) -> imapget_924 >= 4;
constraint (((mapget_919 = 20) /\ (unnamed_923 = 5))) -> imapget_924 >= 5;
constraint (((mapget_919 = 20) /\ (unnamed_923 = 6))) -> imapget_924 >= 6;
constraint (((mapget_919 = 20) /\ (unnamed_923 = 7))) -> imapget_924 >= 7;
constraint (((mapget_919 = 20) /\ (unnamed_923 = 8))) -> imapget_924 >= 8;
constraint (((mapget_919 = 20) /\ (unnamed_923 = 9))) -> imapget_924 >= 9;
constraint (((mapget_919 = 20) /\ (unnamed_923 = 10))) -> imapget_924 >= 10;
constraint (((mapget_919 = 24) /\ (unnamed_923 = 1))) -> imapget_924 >= 11;
constraint (((mapget_919 = 24) /\ (unnamed_923 = 2))) -> imapget_924 >= 12;
constraint (((mapget_919 = 24) /\ (unnamed_923 = 3))) -> imapget_924 >= 13;
constraint (((mapget_919 = 24) /\ (unnamed_923 = 4))) -> imapget_924 >= 14;
constraint (((mapget_919 = 24) /\ (unnamed_923 = 5))) -> imapget_924 >= 15;
constraint (((mapget_919 = 24) /\ (unnamed_923 = 6))) -> imapget_924 >= 16;
constraint (((mapget_919 = 24) /\ (unnamed_923 = 7))) -> imapget_924 >= 17;
constraint (((mapget_919 = 24) /\ (unnamed_923 = 8))) -> imapget_924 >= 18;
constraint (((mapget_919 = 24) /\ (unnamed_923 = 9))) -> imapget_924 >= 19;
constraint (((mapget_919 = 24) /\ (unnamed_923 = 10))) -> imapget_924 >= 20;
constraint (((mapget_919 = 25) /\ (unnamed_923 = 1))) -> imapget_924 >= 21;
constraint (((mapget_919 = 25) /\ (unnamed_923 = 2))) -> imapget_924 >= 22;
constraint (((mapget_919 = 25) /\ (unnamed_923 = 3))) -> imapget_924 >= 23;
constraint (((mapget_919 = 25) /\ (unnamed_923 = 4))) -> imapget_924 >= 24;
constraint (((mapget_919 = 25) /\ (unnamed_923 = 5))) -> imapget_924 >= 25;
constraint (((mapget_919 = 25) /\ (unnamed_923 = 6))) -> imapget_924 >= 26;
constraint (((mapget_919 = 25) /\ (unnamed_923 = 7))) -> imapget_924 >= 27;
constraint (((mapget_919 = 25) /\ (unnamed_923 = 8))) -> imapget_924 >= 28;
constraint (((mapget_919 = 25) /\ (unnamed_923 = 9))) -> imapget_924 >= 29;
constraint (((mapget_919 = 25) /\ (unnamed_923 = 10))) -> imapget_924 >= 30;
constraint (((mapget_919 = 27) /\ (unnamed_923 = 1))) -> imapget_924 >= 31;
constraint (((mapget_919 = 27) /\ (unnamed_923 = 2))) -> imapget_924 >= 32;
constraint (((mapget_919 = 27) /\ (unnamed_923 = 3))) -> imapget_924 >= 33;
constraint (((mapget_919 = 27) /\ (unnamed_923 = 4))) -> imapget_924 >= 34;
constraint (((mapget_919 = 27) /\ (unnamed_923 = 5))) -> imapget_924 >= 35;
constraint (((mapget_919 = 27) /\ (unnamed_923 = 6))) -> imapget_924 >= 36;
constraint (((mapget_919 = 27) /\ (unnamed_923 = 7))) -> imapget_924 >= 37;
constraint (((mapget_919 = 27) /\ (unnamed_923 = 8))) -> imapget_924 >= 38;
constraint (((mapget_919 = 27) /\ (unnamed_923 = 9))) -> imapget_924 >= 39;
constraint (((mapget_919 = 27) /\ (unnamed_923 = 10))) -> imapget_924 >= 40;
constraint (((mapget_919 = 28) /\ (unnamed_923 = 1))) -> imapget_924 >= 41;
constraint (((mapget_919 = 28) /\ (unnamed_923 = 2))) -> imapget_924 >= 42;
constraint (((mapget_919 = 28) /\ (unnamed_923 = 3))) -> imapget_924 >= 43;
constraint (((mapget_919 = 28) /\ (unnamed_923 = 4))) -> imapget_924 >= 44;
constraint (((mapget_919 = 28) /\ (unnamed_923 = 5))) -> imapget_924 >= 45;
constraint (((mapget_919 = 28) /\ (unnamed_923 = 6))) -> imapget_924 >= 46;
constraint (((mapget_919 = 28) /\ (unnamed_923 = 7))) -> imapget_924 >= 47;
constraint (((mapget_919 = 28) /\ (unnamed_923 = 8))) -> imapget_924 >= 48;
constraint (((mapget_919 = 28) /\ (unnamed_923 = 9))) -> imapget_924 >= 49;
constraint (((mapget_919 = 28) /\ (unnamed_923 = 10))) -> imapget_924 >= 50;
constraint (((mapget_919 = 29) /\ (unnamed_923 = 1))) -> imapget_924 >= 51;
constraint (((mapget_919 = 29) /\ (unnamed_923 = 2))) -> imapget_924 >= 52;
constraint (((mapget_919 = 29) /\ (unnamed_923 = 3))) -> imapget_924 >= 53;
constraint (((mapget_919 = 29) /\ (unnamed_923 = 4))) -> imapget_924 >= 54;
constraint (((mapget_919 = 29) /\ (unnamed_923 = 5))) -> imapget_924 >= 55;
constraint (((mapget_919 = 29) /\ (unnamed_923 = 6))) -> imapget_924 >= 56;
constraint (((mapget_919 = 29) /\ (unnamed_923 = 7))) -> imapget_924 >= 57;
constraint (((mapget_919 = 29) /\ (unnamed_923 = 8))) -> imapget_924 >= 58;
constraint (((mapget_919 = 29) /\ (unnamed_923 = 9))) -> imapget_924 >= 59;
constraint (((mapget_919 = 29) /\ (unnamed_923 = 10))) -> imapget_924 >= 60;
constraint (((mapget_919 = 30) /\ (unnamed_923 = 1))) -> imapget_924 >= 61;
constraint (((mapget_919 = 30) /\ (unnamed_923 = 2))) -> imapget_924 >= 62;
constraint (((mapget_919 = 30) /\ (unnamed_923 = 3))) -> imapget_924 >= 63;
constraint (((mapget_919 = 30) /\ (unnamed_923 = 4))) -> imapget_924 >= 64;
constraint (((mapget_919 = 30) /\ (unnamed_923 = 5))) -> imapget_924 >= 65;
constraint (((mapget_919 = 30) /\ (unnamed_923 = 6))) -> imapget_924 >= 66;
constraint (((mapget_919 = 30) /\ (unnamed_923 = 7))) -> imapget_924 >= 67;
constraint (((mapget_919 = 30) /\ (unnamed_923 = 8))) -> imapget_924 >= 68;
constraint (((mapget_919 = 30) /\ (unnamed_923 = 9))) -> imapget_924 >= 69;
constraint (((mapget_919 = 30) /\ (unnamed_923 = 10))) -> imapget_924 >= 70;
constraint (((mapget_919 = 32) /\ (unnamed_923 = 1))) -> imapget_924 >= 71;
constraint (((mapget_919 = 32) /\ (unnamed_923 = 2))) -> imapget_924 >= 72;
constraint (((mapget_919 = 32) /\ (unnamed_923 = 3))) -> imapget_924 >= 73;
constraint (((mapget_919 = 32) /\ (unnamed_923 = 4))) -> imapget_924 >= 74;
constraint (((mapget_919 = 32) /\ (unnamed_923 = 5))) -> imapget_924 >= 75;
constraint (((mapget_919 = 32) /\ (unnamed_923 = 6))) -> imapget_924 >= 76;
constraint (((mapget_919 = 32) /\ (unnamed_923 = 7))) -> imapget_924 >= 77;
constraint (((mapget_919 = 32) /\ (unnamed_923 = 8))) -> imapget_924 >= 78;
constraint (((mapget_919 = 32) /\ (unnamed_923 = 9))) -> imapget_924 >= 79;
constraint (((mapget_919 = 32) /\ (unnamed_923 = 10))) -> imapget_924 >= 80;
constraint (((mapget_919 = 33) /\ (unnamed_923 = 1))) -> imapget_924 >= 81;
constraint (((mapget_919 = 33) /\ (unnamed_923 = 2))) -> imapget_924 >= 82;
constraint (((mapget_919 = 33) /\ (unnamed_923 = 3))) -> imapget_924 >= 83;
constraint (((mapget_919 = 33) /\ (unnamed_923 = 4))) -> imapget_924 >= 84;
constraint (((mapget_919 = 33) /\ (unnamed_923 = 5))) -> imapget_924 >= 85;
constraint (((mapget_919 = 33) /\ (unnamed_923 = 6))) -> imapget_924 >= 86;
constraint (((mapget_919 = 33) /\ (unnamed_923 = 7))) -> imapget_924 >= 87;
constraint (((mapget_919 = 33) /\ (unnamed_923 = 8))) -> imapget_924 >= 88;
constraint (((mapget_919 = 33) /\ (unnamed_923 = 9))) -> imapget_924 >= 89;
constraint (((mapget_919 = 33) /\ (unnamed_923 = 10))) -> imapget_924 >= 90;
constraint (((mapget_919 = 34) /\ (unnamed_923 = 1))) -> imapget_924 >= 91;
constraint (((mapget_919 = 34) /\ (unnamed_923 = 2))) -> imapget_924 >= 92;
constraint (((mapget_919 = 34) /\ (unnamed_923 = 3))) -> imapget_924 >= 93;
constraint (((mapget_919 = 34) /\ (unnamed_923 = 4))) -> imapget_924 >= 94;
constraint (((mapget_919 = 34) /\ (unnamed_923 = 5))) -> imapget_924 >= 95;
constraint (((mapget_919 = 34) /\ (unnamed_923 = 6))) -> imapget_924 >= 96;
constraint (((mapget_919 = 34) /\ (unnamed_923 = 7))) -> imapget_924 >= 97;
constraint (((mapget_919 = 34) /\ (unnamed_923 = 8))) -> imapget_924 >= 98;
constraint (((mapget_919 = 34) /\ (unnamed_923 = 9))) -> imapget_924 >= 99;
constraint (((mapget_919 = 34) /\ (unnamed_923 = 10))) -> imapget_924 >= 100;
constraint mapget_924 = [0, 15, 16, 16, 6, 8, 8, 3, 4, 17, 15, 0, 11, 18, 10, 12, 18, 4, 11, 7, 16, 11, 0, 13, 13, 12, 8, 1, 14, 5, 16, 18, 13, 0, 12, 16, 6, 5, 15, 12, 6, 10, 13, 12, 0, 2, 8, 19, 9, 5, 8, 12, 12, 16, 2, 0, 11, 14, 16, 8, 8, 18, 8, 6, 8, 11, 0, 11, 20, 19, 3, 4, 1, 5, 19, 14, 11, 0, 7, 2, 4, 11, 14, 15, 9, 16, 20, 7, 0, 12, 17, 7, 5, 12, 5, 8, 19, 2, 12, 0, 20][imapget_924];

var 0..20: ret_travelTime_928; %ref (Literal: 0 [0]).ret_travelTime -26
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_travelTime -26
var 1..1: iret_travelTime_928;
constraint ret_travelTime_928 = [mapget_924, 20][iret_travelTime_928];

var 2..39: Add_929 = (currentTime_904 + ret_travelTime_928);

var 1..10: nextLocation_931; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_931;
constraint nextLocation_931 = [ret_getLocation_901, 10][inextLocation_931];

var {36,39,42,45,48,51,54,57,60,63}: listget_944; %optimise.state.ListGet@3b0
constraint listget_944 = chooseOrderVal_2[3];

var {36,39,42,45,48,51,54,57,60,63}: stop_956; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_956;
constraint stop_956 = [listget_944, 63][istop_956];

var 1..10: locationID_962; %ref ref (Literal: 0 [0]).stop -21.locationID -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).stop -21.locationID -7
var 1..10: ilocationID_962;
constraint [36, 39, 42, 45, 48, 51, 54, 57, 60, 63, stop_956][ilocationID_962] = stop_956;
constraint ((stop_956 = 36)) -> ilocationID_962 >= 1;
constraint ((stop_956 = 39)) -> ilocationID_962 >= 2;
constraint ((stop_956 = 42)) -> ilocationID_962 >= 3;
constraint ((stop_956 = 45)) -> ilocationID_962 >= 4;
constraint ((stop_956 = 48)) -> ilocationID_962 >= 5;
constraint ((stop_956 = 51)) -> ilocationID_962 >= 6;
constraint ((stop_956 = 54)) -> ilocationID_962 >= 7;
constraint ((stop_956 = 57)) -> ilocationID_962 >= 8;
constraint ((stop_956 = 60)) -> ilocationID_962 >= 9;
constraint ((stop_956 = 63)) -> ilocationID_962 >= 10;
constraint locationID_962 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10][ilocationID_962];

var 1..10: ret_getLocation_966; %ref (Literal: 0 [0]).ret_getLocation -22
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getLocation -22
var 1..1: iret_getLocation_966;
constraint ret_getLocation_966 = [locationID_962, 10][iret_getLocation_966];

var 2..39: currentTime_969; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_969;
constraint currentTime_969 = [Add_929, 39][icurrentTime_969];

var 1..10: currentLocation_970; %ref (Literal: 0 [0]).currentLocation -19
% doing constraints for lookup query: ref (Literal: 0 [0]).currentLocation -19
var 1..1: icurrentLocation_970;
constraint currentLocation_970 = [nextLocation_931, 10][icurrentLocation_970];

var 1..10: nextLocation_973; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_973;
constraint nextLocation_973 = [ret_getLocation_966, 10][inextLocation_973];

var 1..10: location1_980; %ref (Literal: 0 [0]).location1 -24
% doing constraints for lookup query: ref (Literal: 0 [0]).location1 -24
var 1..1: ilocation1_980;
constraint location1_980 = [currentLocation_970, 10][ilocation1_980];

var 1..10: unnamed_983; %ref (Literal: 0 [0]).unnamed -27
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -27
var 1..1: iunnamed_983;
constraint unnamed_983 = [location1_980, 10][iunnamed_983];

var {20,24,25,27,28,29,30,32,33,34}: mapget_984; %optimise.state.MapGet@3d8
% doing constraints for lookup query: optimise.state.MapGet@3d8
var 1..10: imapget_984;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_983][imapget_984] = unnamed_983;
constraint ((unnamed_983 = 1)) -> imapget_984 >= 1;
constraint ((unnamed_983 = 2)) -> imapget_984 >= 2;
constraint ((unnamed_983 = 3)) -> imapget_984 >= 3;
constraint ((unnamed_983 = 4)) -> imapget_984 >= 4;
constraint ((unnamed_983 = 5)) -> imapget_984 >= 5;
constraint ((unnamed_983 = 6)) -> imapget_984 >= 6;
constraint ((unnamed_983 = 7)) -> imapget_984 >= 7;
constraint ((unnamed_983 = 8)) -> imapget_984 >= 8;
constraint ((unnamed_983 = 9)) -> imapget_984 >= 9;
constraint ((unnamed_983 = 10)) -> imapget_984 >= 10;
constraint mapget_984 = [20, 24, 25, 27, 28, 29, 30, 32, 33, 34, 34][imapget_984];

var 1..10: location2_985; %ref (Literal: 0 [0]).location2 -25
% doing constraints for lookup query: ref (Literal: 0 [0]).location2 -25
var 1..1: ilocation2_985;
constraint location2_985 = [nextLocation_973, 10][ilocation2_985];

var 1..10: unnamed_988; %ref (Literal: 0 [0]).unnamed -28
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -28
var 1..1: iunnamed_988;
constraint unnamed_988 = [location2_985, 10][iunnamed_988];

var 0..20: mapget_989; %optimise.state.MapGet@3dd
% doing constraints for lookup query: optimise.state.MapGet@3dd
var 1..100: imapget_989;
constraint [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, mapget_984][imapget_989] = mapget_984;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_988][imapget_989] = unnamed_988;
constraint (((mapget_984 = 20) /\ (unnamed_988 = 1))) -> imapget_989 >= 1;
constraint (((mapget_984 = 20) /\ (unnamed_988 = 2))) -> imapget_989 >= 2;
constraint (((mapget_984 = 20) /\ (unnamed_988 = 3))) -> imapget_989 >= 3;
constraint (((mapget_984 = 20) /\ (unnamed_988 = 4))) -> imapget_989 >= 4;
constraint (((mapget_984 = 20) /\ (unnamed_988 = 5))) -> imapget_989 >= 5;
constraint (((mapget_984 = 20) /\ (unnamed_988 = 6))) -> imapget_989 >= 6;
constraint (((mapget_984 = 20) /\ (unnamed_988 = 7))) -> imapget_989 >= 7;
constraint (((mapget_984 = 20) /\ (unnamed_988 = 8))) -> imapget_989 >= 8;
constraint (((mapget_984 = 20) /\ (unnamed_988 = 9))) -> imapget_989 >= 9;
constraint (((mapget_984 = 20) /\ (unnamed_988 = 10))) -> imapget_989 >= 10;
constraint (((mapget_984 = 24) /\ (unnamed_988 = 1))) -> imapget_989 >= 11;
constraint (((mapget_984 = 24) /\ (unnamed_988 = 2))) -> imapget_989 >= 12;
constraint (((mapget_984 = 24) /\ (unnamed_988 = 3))) -> imapget_989 >= 13;
constraint (((mapget_984 = 24) /\ (unnamed_988 = 4))) -> imapget_989 >= 14;
constraint (((mapget_984 = 24) /\ (unnamed_988 = 5))) -> imapget_989 >= 15;
constraint (((mapget_984 = 24) /\ (unnamed_988 = 6))) -> imapget_989 >= 16;
constraint (((mapget_984 = 24) /\ (unnamed_988 = 7))) -> imapget_989 >= 17;
constraint (((mapget_984 = 24) /\ (unnamed_988 = 8))) -> imapget_989 >= 18;
constraint (((mapget_984 = 24) /\ (unnamed_988 = 9))) -> imapget_989 >= 19;
constraint (((mapget_984 = 24) /\ (unnamed_988 = 10))) -> imapget_989 >= 20;
constraint (((mapget_984 = 25) /\ (unnamed_988 = 1))) -> imapget_989 >= 21;
constraint (((mapget_984 = 25) /\ (unnamed_988 = 2))) -> imapget_989 >= 22;
constraint (((mapget_984 = 25) /\ (unnamed_988 = 3))) -> imapget_989 >= 23;
constraint (((mapget_984 = 25) /\ (unnamed_988 = 4))) -> imapget_989 >= 24;
constraint (((mapget_984 = 25) /\ (unnamed_988 = 5))) -> imapget_989 >= 25;
constraint (((mapget_984 = 25) /\ (unnamed_988 = 6))) -> imapget_989 >= 26;
constraint (((mapget_984 = 25) /\ (unnamed_988 = 7))) -> imapget_989 >= 27;
constraint (((mapget_984 = 25) /\ (unnamed_988 = 8))) -> imapget_989 >= 28;
constraint (((mapget_984 = 25) /\ (unnamed_988 = 9))) -> imapget_989 >= 29;
constraint (((mapget_984 = 25) /\ (unnamed_988 = 10))) -> imapget_989 >= 30;
constraint (((mapget_984 = 27) /\ (unnamed_988 = 1))) -> imapget_989 >= 31;
constraint (((mapget_984 = 27) /\ (unnamed_988 = 2))) -> imapget_989 >= 32;
constraint (((mapget_984 = 27) /\ (unnamed_988 = 3))) -> imapget_989 >= 33;
constraint (((mapget_984 = 27) /\ (unnamed_988 = 4))) -> imapget_989 >= 34;
constraint (((mapget_984 = 27) /\ (unnamed_988 = 5))) -> imapget_989 >= 35;
constraint (((mapget_984 = 27) /\ (unnamed_988 = 6))) -> imapget_989 >= 36;
constraint (((mapget_984 = 27) /\ (unnamed_988 = 7))) -> imapget_989 >= 37;
constraint (((mapget_984 = 27) /\ (unnamed_988 = 8))) -> imapget_989 >= 38;
constraint (((mapget_984 = 27) /\ (unnamed_988 = 9))) -> imapget_989 >= 39;
constraint (((mapget_984 = 27) /\ (unnamed_988 = 10))) -> imapget_989 >= 40;
constraint (((mapget_984 = 28) /\ (unnamed_988 = 1))) -> imapget_989 >= 41;
constraint (((mapget_984 = 28) /\ (unnamed_988 = 2))) -> imapget_989 >= 42;
constraint (((mapget_984 = 28) /\ (unnamed_988 = 3))) -> imapget_989 >= 43;
constraint (((mapget_984 = 28) /\ (unnamed_988 = 4))) -> imapget_989 >= 44;
constraint (((mapget_984 = 28) /\ (unnamed_988 = 5))) -> imapget_989 >= 45;
constraint (((mapget_984 = 28) /\ (unnamed_988 = 6))) -> imapget_989 >= 46;
constraint (((mapget_984 = 28) /\ (unnamed_988 = 7))) -> imapget_989 >= 47;
constraint (((mapget_984 = 28) /\ (unnamed_988 = 8))) -> imapget_989 >= 48;
constraint (((mapget_984 = 28) /\ (unnamed_988 = 9))) -> imapget_989 >= 49;
constraint (((mapget_984 = 28) /\ (unnamed_988 = 10))) -> imapget_989 >= 50;
constraint (((mapget_984 = 29) /\ (unnamed_988 = 1))) -> imapget_989 >= 51;
constraint (((mapget_984 = 29) /\ (unnamed_988 = 2))) -> imapget_989 >= 52;
constraint (((mapget_984 = 29) /\ (unnamed_988 = 3))) -> imapget_989 >= 53;
constraint (((mapget_984 = 29) /\ (unnamed_988 = 4))) -> imapget_989 >= 54;
constraint (((mapget_984 = 29) /\ (unnamed_988 = 5))) -> imapget_989 >= 55;
constraint (((mapget_984 = 29) /\ (unnamed_988 = 6))) -> imapget_989 >= 56;
constraint (((mapget_984 = 29) /\ (unnamed_988 = 7))) -> imapget_989 >= 57;
constraint (((mapget_984 = 29) /\ (unnamed_988 = 8))) -> imapget_989 >= 58;
constraint (((mapget_984 = 29) /\ (unnamed_988 = 9))) -> imapget_989 >= 59;
constraint (((mapget_984 = 29) /\ (unnamed_988 = 10))) -> imapget_989 >= 60;
constraint (((mapget_984 = 30) /\ (unnamed_988 = 1))) -> imapget_989 >= 61;
constraint (((mapget_984 = 30) /\ (unnamed_988 = 2))) -> imapget_989 >= 62;
constraint (((mapget_984 = 30) /\ (unnamed_988 = 3))) -> imapget_989 >= 63;
constraint (((mapget_984 = 30) /\ (unnamed_988 = 4))) -> imapget_989 >= 64;
constraint (((mapget_984 = 30) /\ (unnamed_988 = 5))) -> imapget_989 >= 65;
constraint (((mapget_984 = 30) /\ (unnamed_988 = 6))) -> imapget_989 >= 66;
constraint (((mapget_984 = 30) /\ (unnamed_988 = 7))) -> imapget_989 >= 67;
constraint (((mapget_984 = 30) /\ (unnamed_988 = 8))) -> imapget_989 >= 68;
constraint (((mapget_984 = 30) /\ (unnamed_988 = 9))) -> imapget_989 >= 69;
constraint (((mapget_984 = 30) /\ (unnamed_988 = 10))) -> imapget_989 >= 70;
constraint (((mapget_984 = 32) /\ (unnamed_988 = 1))) -> imapget_989 >= 71;
constraint (((mapget_984 = 32) /\ (unnamed_988 = 2))) -> imapget_989 >= 72;
constraint (((mapget_984 = 32) /\ (unnamed_988 = 3))) -> imapget_989 >= 73;
constraint (((mapget_984 = 32) /\ (unnamed_988 = 4))) -> imapget_989 >= 74;
constraint (((mapget_984 = 32) /\ (unnamed_988 = 5))) -> imapget_989 >= 75;
constraint (((mapget_984 = 32) /\ (unnamed_988 = 6))) -> imapget_989 >= 76;
constraint (((mapget_984 = 32) /\ (unnamed_988 = 7))) -> imapget_989 >= 77;
constraint (((mapget_984 = 32) /\ (unnamed_988 = 8))) -> imapget_989 >= 78;
constraint (((mapget_984 = 32) /\ (unnamed_988 = 9))) -> imapget_989 >= 79;
constraint (((mapget_984 = 32) /\ (unnamed_988 = 10))) -> imapget_989 >= 80;
constraint (((mapget_984 = 33) /\ (unnamed_988 = 1))) -> imapget_989 >= 81;
constraint (((mapget_984 = 33) /\ (unnamed_988 = 2))) -> imapget_989 >= 82;
constraint (((mapget_984 = 33) /\ (unnamed_988 = 3))) -> imapget_989 >= 83;
constraint (((mapget_984 = 33) /\ (unnamed_988 = 4))) -> imapget_989 >= 84;
constraint (((mapget_984 = 33) /\ (unnamed_988 = 5))) -> imapget_989 >= 85;
constraint (((mapget_984 = 33) /\ (unnamed_988 = 6))) -> imapget_989 >= 86;
constraint (((mapget_984 = 33) /\ (unnamed_988 = 7))) -> imapget_989 >= 87;
constraint (((mapget_984 = 33) /\ (unnamed_988 = 8))) -> imapget_989 >= 88;
constraint (((mapget_984 = 33) /\ (unnamed_988 = 9))) -> imapget_989 >= 89;
constraint (((mapget_984 = 33) /\ (unnamed_988 = 10))) -> imapget_989 >= 90;
constraint (((mapget_984 = 34) /\ (unnamed_988 = 1))) -> imapget_989 >= 91;
constraint (((mapget_984 = 34) /\ (unnamed_988 = 2))) -> imapget_989 >= 92;
constraint (((mapget_984 = 34) /\ (unnamed_988 = 3))) -> imapget_989 >= 93;
constraint (((mapget_984 = 34) /\ (unnamed_988 = 4))) -> imapget_989 >= 94;
constraint (((mapget_984 = 34) /\ (unnamed_988 = 5))) -> imapget_989 >= 95;
constraint (((mapget_984 = 34) /\ (unnamed_988 = 6))) -> imapget_989 >= 96;
constraint (((mapget_984 = 34) /\ (unnamed_988 = 7))) -> imapget_989 >= 97;
constraint (((mapget_984 = 34) /\ (unnamed_988 = 8))) -> imapget_989 >= 98;
constraint (((mapget_984 = 34) /\ (unnamed_988 = 9))) -> imapget_989 >= 99;
constraint (((mapget_984 = 34) /\ (unnamed_988 = 10))) -> imapget_989 >= 100;
constraint mapget_989 = [0, 15, 16, 16, 6, 8, 8, 3, 4, 17, 15, 0, 11, 18, 10, 12, 18, 4, 11, 7, 16, 11, 0, 13, 13, 12, 8, 1, 14, 5, 16, 18, 13, 0, 12, 16, 6, 5, 15, 12, 6, 10, 13, 12, 0, 2, 8, 19, 9, 5, 8, 12, 12, 16, 2, 0, 11, 14, 16, 8, 8, 18, 8, 6, 8, 11, 0, 11, 20, 19, 3, 4, 1, 5, 19, 14, 11, 0, 7, 2, 4, 11, 14, 15, 9, 16, 20, 7, 0, 12, 17, 7, 5, 12, 5, 8, 19, 2, 12, 0, 20][imapget_989];

var 0..20: ret_travelTime_993; %ref (Literal: 0 [0]).ret_travelTime -26
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_travelTime -26
var 1..1: iret_travelTime_993;
constraint ret_travelTime_993 = [mapget_989, 20][iret_travelTime_993];

var 2..59: Add_994 = (currentTime_969 + ret_travelTime_993);

var 1..10: nextLocation_996; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_996;
constraint nextLocation_996 = [ret_getLocation_966, 10][inextLocation_996];

var {36,39,42,45,48,51,54,57,60,63}: listget_1009; %optimise.state.ListGet@3f1
constraint listget_1009 = chooseOrderVal_2[4];

var {36,39,42,45,48,51,54,57,60,63}: stop_1021; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_1021;
constraint stop_1021 = [listget_1009, 63][istop_1021];

var 1..10: locationID_1027; %ref ref (Literal: 0 [0]).stop -21.locationID -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).stop -21.locationID -7
var 1..10: ilocationID_1027;
constraint [36, 39, 42, 45, 48, 51, 54, 57, 60, 63, stop_1021][ilocationID_1027] = stop_1021;
constraint ((stop_1021 = 36)) -> ilocationID_1027 >= 1;
constraint ((stop_1021 = 39)) -> ilocationID_1027 >= 2;
constraint ((stop_1021 = 42)) -> ilocationID_1027 >= 3;
constraint ((stop_1021 = 45)) -> ilocationID_1027 >= 4;
constraint ((stop_1021 = 48)) -> ilocationID_1027 >= 5;
constraint ((stop_1021 = 51)) -> ilocationID_1027 >= 6;
constraint ((stop_1021 = 54)) -> ilocationID_1027 >= 7;
constraint ((stop_1021 = 57)) -> ilocationID_1027 >= 8;
constraint ((stop_1021 = 60)) -> ilocationID_1027 >= 9;
constraint ((stop_1021 = 63)) -> ilocationID_1027 >= 10;
constraint locationID_1027 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10][ilocationID_1027];

var 1..10: ret_getLocation_1031; %ref (Literal: 0 [0]).ret_getLocation -22
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getLocation -22
var 1..1: iret_getLocation_1031;
constraint ret_getLocation_1031 = [locationID_1027, 10][iret_getLocation_1031];

var 2..59: currentTime_1034; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_1034;
constraint currentTime_1034 = [Add_994, 59][icurrentTime_1034];

var 1..10: currentLocation_1035; %ref (Literal: 0 [0]).currentLocation -19
% doing constraints for lookup query: ref (Literal: 0 [0]).currentLocation -19
var 1..1: icurrentLocation_1035;
constraint currentLocation_1035 = [nextLocation_996, 10][icurrentLocation_1035];

var 1..10: nextLocation_1038; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_1038;
constraint nextLocation_1038 = [ret_getLocation_1031, 10][inextLocation_1038];

var 1..10: location1_1045; %ref (Literal: 0 [0]).location1 -24
% doing constraints for lookup query: ref (Literal: 0 [0]).location1 -24
var 1..1: ilocation1_1045;
constraint location1_1045 = [currentLocation_1035, 10][ilocation1_1045];

var 1..10: unnamed_1048; %ref (Literal: 0 [0]).unnamed -27
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -27
var 1..1: iunnamed_1048;
constraint unnamed_1048 = [location1_1045, 10][iunnamed_1048];

var {20,24,25,27,28,29,30,32,33,34}: mapget_1049; %optimise.state.MapGet@419
% doing constraints for lookup query: optimise.state.MapGet@419
var 1..10: imapget_1049;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_1048][imapget_1049] = unnamed_1048;
constraint ((unnamed_1048 = 1)) -> imapget_1049 >= 1;
constraint ((unnamed_1048 = 2)) -> imapget_1049 >= 2;
constraint ((unnamed_1048 = 3)) -> imapget_1049 >= 3;
constraint ((unnamed_1048 = 4)) -> imapget_1049 >= 4;
constraint ((unnamed_1048 = 5)) -> imapget_1049 >= 5;
constraint ((unnamed_1048 = 6)) -> imapget_1049 >= 6;
constraint ((unnamed_1048 = 7)) -> imapget_1049 >= 7;
constraint ((unnamed_1048 = 8)) -> imapget_1049 >= 8;
constraint ((unnamed_1048 = 9)) -> imapget_1049 >= 9;
constraint ((unnamed_1048 = 10)) -> imapget_1049 >= 10;
constraint mapget_1049 = [20, 24, 25, 27, 28, 29, 30, 32, 33, 34, 34][imapget_1049];

var 1..10: location2_1050; %ref (Literal: 0 [0]).location2 -25
% doing constraints for lookup query: ref (Literal: 0 [0]).location2 -25
var 1..1: ilocation2_1050;
constraint location2_1050 = [nextLocation_1038, 10][ilocation2_1050];

var 1..10: unnamed_1053; %ref (Literal: 0 [0]).unnamed -28
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -28
var 1..1: iunnamed_1053;
constraint unnamed_1053 = [location2_1050, 10][iunnamed_1053];

var 0..20: mapget_1054; %optimise.state.MapGet@41e
% doing constraints for lookup query: optimise.state.MapGet@41e
var 1..100: imapget_1054;
constraint [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, mapget_1049][imapget_1054] = mapget_1049;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_1053][imapget_1054] = unnamed_1053;
constraint (((mapget_1049 = 20) /\ (unnamed_1053 = 1))) -> imapget_1054 >= 1;
constraint (((mapget_1049 = 20) /\ (unnamed_1053 = 2))) -> imapget_1054 >= 2;
constraint (((mapget_1049 = 20) /\ (unnamed_1053 = 3))) -> imapget_1054 >= 3;
constraint (((mapget_1049 = 20) /\ (unnamed_1053 = 4))) -> imapget_1054 >= 4;
constraint (((mapget_1049 = 20) /\ (unnamed_1053 = 5))) -> imapget_1054 >= 5;
constraint (((mapget_1049 = 20) /\ (unnamed_1053 = 6))) -> imapget_1054 >= 6;
constraint (((mapget_1049 = 20) /\ (unnamed_1053 = 7))) -> imapget_1054 >= 7;
constraint (((mapget_1049 = 20) /\ (unnamed_1053 = 8))) -> imapget_1054 >= 8;
constraint (((mapget_1049 = 20) /\ (unnamed_1053 = 9))) -> imapget_1054 >= 9;
constraint (((mapget_1049 = 20) /\ (unnamed_1053 = 10))) -> imapget_1054 >= 10;
constraint (((mapget_1049 = 24) /\ (unnamed_1053 = 1))) -> imapget_1054 >= 11;
constraint (((mapget_1049 = 24) /\ (unnamed_1053 = 2))) -> imapget_1054 >= 12;
constraint (((mapget_1049 = 24) /\ (unnamed_1053 = 3))) -> imapget_1054 >= 13;
constraint (((mapget_1049 = 24) /\ (unnamed_1053 = 4))) -> imapget_1054 >= 14;
constraint (((mapget_1049 = 24) /\ (unnamed_1053 = 5))) -> imapget_1054 >= 15;
constraint (((mapget_1049 = 24) /\ (unnamed_1053 = 6))) -> imapget_1054 >= 16;
constraint (((mapget_1049 = 24) /\ (unnamed_1053 = 7))) -> imapget_1054 >= 17;
constraint (((mapget_1049 = 24) /\ (unnamed_1053 = 8))) -> imapget_1054 >= 18;
constraint (((mapget_1049 = 24) /\ (unnamed_1053 = 9))) -> imapget_1054 >= 19;
constraint (((mapget_1049 = 24) /\ (unnamed_1053 = 10))) -> imapget_1054 >= 20;
constraint (((mapget_1049 = 25) /\ (unnamed_1053 = 1))) -> imapget_1054 >= 21;
constraint (((mapget_1049 = 25) /\ (unnamed_1053 = 2))) -> imapget_1054 >= 22;
constraint (((mapget_1049 = 25) /\ (unnamed_1053 = 3))) -> imapget_1054 >= 23;
constraint (((mapget_1049 = 25) /\ (unnamed_1053 = 4))) -> imapget_1054 >= 24;
constraint (((mapget_1049 = 25) /\ (unnamed_1053 = 5))) -> imapget_1054 >= 25;
constraint (((mapget_1049 = 25) /\ (unnamed_1053 = 6))) -> imapget_1054 >= 26;
constraint (((mapget_1049 = 25) /\ (unnamed_1053 = 7))) -> imapget_1054 >= 27;
constraint (((mapget_1049 = 25) /\ (unnamed_1053 = 8))) -> imapget_1054 >= 28;
constraint (((mapget_1049 = 25) /\ (unnamed_1053 = 9))) -> imapget_1054 >= 29;
constraint (((mapget_1049 = 25) /\ (unnamed_1053 = 10))) -> imapget_1054 >= 30;
constraint (((mapget_1049 = 27) /\ (unnamed_1053 = 1))) -> imapget_1054 >= 31;
constraint (((mapget_1049 = 27) /\ (unnamed_1053 = 2))) -> imapget_1054 >= 32;
constraint (((mapget_1049 = 27) /\ (unnamed_1053 = 3))) -> imapget_1054 >= 33;
constraint (((mapget_1049 = 27) /\ (unnamed_1053 = 4))) -> imapget_1054 >= 34;
constraint (((mapget_1049 = 27) /\ (unnamed_1053 = 5))) -> imapget_1054 >= 35;
constraint (((mapget_1049 = 27) /\ (unnamed_1053 = 6))) -> imapget_1054 >= 36;
constraint (((mapget_1049 = 27) /\ (unnamed_1053 = 7))) -> imapget_1054 >= 37;
constraint (((mapget_1049 = 27) /\ (unnamed_1053 = 8))) -> imapget_1054 >= 38;
constraint (((mapget_1049 = 27) /\ (unnamed_1053 = 9))) -> imapget_1054 >= 39;
constraint (((mapget_1049 = 27) /\ (unnamed_1053 = 10))) -> imapget_1054 >= 40;
constraint (((mapget_1049 = 28) /\ (unnamed_1053 = 1))) -> imapget_1054 >= 41;
constraint (((mapget_1049 = 28) /\ (unnamed_1053 = 2))) -> imapget_1054 >= 42;
constraint (((mapget_1049 = 28) /\ (unnamed_1053 = 3))) -> imapget_1054 >= 43;
constraint (((mapget_1049 = 28) /\ (unnamed_1053 = 4))) -> imapget_1054 >= 44;
constraint (((mapget_1049 = 28) /\ (unnamed_1053 = 5))) -> imapget_1054 >= 45;
constraint (((mapget_1049 = 28) /\ (unnamed_1053 = 6))) -> imapget_1054 >= 46;
constraint (((mapget_1049 = 28) /\ (unnamed_1053 = 7))) -> imapget_1054 >= 47;
constraint (((mapget_1049 = 28) /\ (unnamed_1053 = 8))) -> imapget_1054 >= 48;
constraint (((mapget_1049 = 28) /\ (unnamed_1053 = 9))) -> imapget_1054 >= 49;
constraint (((mapget_1049 = 28) /\ (unnamed_1053 = 10))) -> imapget_1054 >= 50;
constraint (((mapget_1049 = 29) /\ (unnamed_1053 = 1))) -> imapget_1054 >= 51;
constraint (((mapget_1049 = 29) /\ (unnamed_1053 = 2))) -> imapget_1054 >= 52;
constraint (((mapget_1049 = 29) /\ (unnamed_1053 = 3))) -> imapget_1054 >= 53;
constraint (((mapget_1049 = 29) /\ (unnamed_1053 = 4))) -> imapget_1054 >= 54;
constraint (((mapget_1049 = 29) /\ (unnamed_1053 = 5))) -> imapget_1054 >= 55;
constraint (((mapget_1049 = 29) /\ (unnamed_1053 = 6))) -> imapget_1054 >= 56;
constraint (((mapget_1049 = 29) /\ (unnamed_1053 = 7))) -> imapget_1054 >= 57;
constraint (((mapget_1049 = 29) /\ (unnamed_1053 = 8))) -> imapget_1054 >= 58;
constraint (((mapget_1049 = 29) /\ (unnamed_1053 = 9))) -> imapget_1054 >= 59;
constraint (((mapget_1049 = 29) /\ (unnamed_1053 = 10))) -> imapget_1054 >= 60;
constraint (((mapget_1049 = 30) /\ (unnamed_1053 = 1))) -> imapget_1054 >= 61;
constraint (((mapget_1049 = 30) /\ (unnamed_1053 = 2))) -> imapget_1054 >= 62;
constraint (((mapget_1049 = 30) /\ (unnamed_1053 = 3))) -> imapget_1054 >= 63;
constraint (((mapget_1049 = 30) /\ (unnamed_1053 = 4))) -> imapget_1054 >= 64;
constraint (((mapget_1049 = 30) /\ (unnamed_1053 = 5))) -> imapget_1054 >= 65;
constraint (((mapget_1049 = 30) /\ (unnamed_1053 = 6))) -> imapget_1054 >= 66;
constraint (((mapget_1049 = 30) /\ (unnamed_1053 = 7))) -> imapget_1054 >= 67;
constraint (((mapget_1049 = 30) /\ (unnamed_1053 = 8))) -> imapget_1054 >= 68;
constraint (((mapget_1049 = 30) /\ (unnamed_1053 = 9))) -> imapget_1054 >= 69;
constraint (((mapget_1049 = 30) /\ (unnamed_1053 = 10))) -> imapget_1054 >= 70;
constraint (((mapget_1049 = 32) /\ (unnamed_1053 = 1))) -> imapget_1054 >= 71;
constraint (((mapget_1049 = 32) /\ (unnamed_1053 = 2))) -> imapget_1054 >= 72;
constraint (((mapget_1049 = 32) /\ (unnamed_1053 = 3))) -> imapget_1054 >= 73;
constraint (((mapget_1049 = 32) /\ (unnamed_1053 = 4))) -> imapget_1054 >= 74;
constraint (((mapget_1049 = 32) /\ (unnamed_1053 = 5))) -> imapget_1054 >= 75;
constraint (((mapget_1049 = 32) /\ (unnamed_1053 = 6))) -> imapget_1054 >= 76;
constraint (((mapget_1049 = 32) /\ (unnamed_1053 = 7))) -> imapget_1054 >= 77;
constraint (((mapget_1049 = 32) /\ (unnamed_1053 = 8))) -> imapget_1054 >= 78;
constraint (((mapget_1049 = 32) /\ (unnamed_1053 = 9))) -> imapget_1054 >= 79;
constraint (((mapget_1049 = 32) /\ (unnamed_1053 = 10))) -> imapget_1054 >= 80;
constraint (((mapget_1049 = 33) /\ (unnamed_1053 = 1))) -> imapget_1054 >= 81;
constraint (((mapget_1049 = 33) /\ (unnamed_1053 = 2))) -> imapget_1054 >= 82;
constraint (((mapget_1049 = 33) /\ (unnamed_1053 = 3))) -> imapget_1054 >= 83;
constraint (((mapget_1049 = 33) /\ (unnamed_1053 = 4))) -> imapget_1054 >= 84;
constraint (((mapget_1049 = 33) /\ (unnamed_1053 = 5))) -> imapget_1054 >= 85;
constraint (((mapget_1049 = 33) /\ (unnamed_1053 = 6))) -> imapget_1054 >= 86;
constraint (((mapget_1049 = 33) /\ (unnamed_1053 = 7))) -> imapget_1054 >= 87;
constraint (((mapget_1049 = 33) /\ (unnamed_1053 = 8))) -> imapget_1054 >= 88;
constraint (((mapget_1049 = 33) /\ (unnamed_1053 = 9))) -> imapget_1054 >= 89;
constraint (((mapget_1049 = 33) /\ (unnamed_1053 = 10))) -> imapget_1054 >= 90;
constraint (((mapget_1049 = 34) /\ (unnamed_1053 = 1))) -> imapget_1054 >= 91;
constraint (((mapget_1049 = 34) /\ (unnamed_1053 = 2))) -> imapget_1054 >= 92;
constraint (((mapget_1049 = 34) /\ (unnamed_1053 = 3))) -> imapget_1054 >= 93;
constraint (((mapget_1049 = 34) /\ (unnamed_1053 = 4))) -> imapget_1054 >= 94;
constraint (((mapget_1049 = 34) /\ (unnamed_1053 = 5))) -> imapget_1054 >= 95;
constraint (((mapget_1049 = 34) /\ (unnamed_1053 = 6))) -> imapget_1054 >= 96;
constraint (((mapget_1049 = 34) /\ (unnamed_1053 = 7))) -> imapget_1054 >= 97;
constraint (((mapget_1049 = 34) /\ (unnamed_1053 = 8))) -> imapget_1054 >= 98;
constraint (((mapget_1049 = 34) /\ (unnamed_1053 = 9))) -> imapget_1054 >= 99;
constraint (((mapget_1049 = 34) /\ (unnamed_1053 = 10))) -> imapget_1054 >= 100;
constraint mapget_1054 = [0, 15, 16, 16, 6, 8, 8, 3, 4, 17, 15, 0, 11, 18, 10, 12, 18, 4, 11, 7, 16, 11, 0, 13, 13, 12, 8, 1, 14, 5, 16, 18, 13, 0, 12, 16, 6, 5, 15, 12, 6, 10, 13, 12, 0, 2, 8, 19, 9, 5, 8, 12, 12, 16, 2, 0, 11, 14, 16, 8, 8, 18, 8, 6, 8, 11, 0, 11, 20, 19, 3, 4, 1, 5, 19, 14, 11, 0, 7, 2, 4, 11, 14, 15, 9, 16, 20, 7, 0, 12, 17, 7, 5, 12, 5, 8, 19, 2, 12, 0, 20][imapget_1054];

var 0..20: ret_travelTime_1058; %ref (Literal: 0 [0]).ret_travelTime -26
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_travelTime -26
var 1..1: iret_travelTime_1058;
constraint ret_travelTime_1058 = [mapget_1054, 20][iret_travelTime_1058];

var 2..79: Add_1059 = (currentTime_1034 + ret_travelTime_1058);

var 1..10: nextLocation_1061; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_1061;
constraint nextLocation_1061 = [ret_getLocation_1031, 10][inextLocation_1061];

var {36,39,42,45,48,51,54,57,60,63}: listget_1074; %optimise.state.ListGet@432
constraint listget_1074 = chooseOrderVal_2[5];

var {36,39,42,45,48,51,54,57,60,63}: stop_1086; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_1086;
constraint stop_1086 = [listget_1074, 63][istop_1086];

var 1..10: locationID_1092; %ref ref (Literal: 0 [0]).stop -21.locationID -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).stop -21.locationID -7
var 1..10: ilocationID_1092;
constraint [36, 39, 42, 45, 48, 51, 54, 57, 60, 63, stop_1086][ilocationID_1092] = stop_1086;
constraint ((stop_1086 = 36)) -> ilocationID_1092 >= 1;
constraint ((stop_1086 = 39)) -> ilocationID_1092 >= 2;
constraint ((stop_1086 = 42)) -> ilocationID_1092 >= 3;
constraint ((stop_1086 = 45)) -> ilocationID_1092 >= 4;
constraint ((stop_1086 = 48)) -> ilocationID_1092 >= 5;
constraint ((stop_1086 = 51)) -> ilocationID_1092 >= 6;
constraint ((stop_1086 = 54)) -> ilocationID_1092 >= 7;
constraint ((stop_1086 = 57)) -> ilocationID_1092 >= 8;
constraint ((stop_1086 = 60)) -> ilocationID_1092 >= 9;
constraint ((stop_1086 = 63)) -> ilocationID_1092 >= 10;
constraint locationID_1092 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10][ilocationID_1092];

var 1..10: ret_getLocation_1096; %ref (Literal: 0 [0]).ret_getLocation -22
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getLocation -22
var 1..1: iret_getLocation_1096;
constraint ret_getLocation_1096 = [locationID_1092, 10][iret_getLocation_1096];

var 2..79: currentTime_1099; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_1099;
constraint currentTime_1099 = [Add_1059, 79][icurrentTime_1099];

var 1..10: currentLocation_1100; %ref (Literal: 0 [0]).currentLocation -19
% doing constraints for lookup query: ref (Literal: 0 [0]).currentLocation -19
var 1..1: icurrentLocation_1100;
constraint currentLocation_1100 = [nextLocation_1061, 10][icurrentLocation_1100];

var 1..10: nextLocation_1103; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_1103;
constraint nextLocation_1103 = [ret_getLocation_1096, 10][inextLocation_1103];

var 1..10: location1_1110; %ref (Literal: 0 [0]).location1 -24
% doing constraints for lookup query: ref (Literal: 0 [0]).location1 -24
var 1..1: ilocation1_1110;
constraint location1_1110 = [currentLocation_1100, 10][ilocation1_1110];

var 1..10: unnamed_1113; %ref (Literal: 0 [0]).unnamed -27
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -27
var 1..1: iunnamed_1113;
constraint unnamed_1113 = [location1_1110, 10][iunnamed_1113];

var {20,24,25,27,28,29,30,32,33,34}: mapget_1114; %optimise.state.MapGet@45a
% doing constraints for lookup query: optimise.state.MapGet@45a
var 1..10: imapget_1114;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_1113][imapget_1114] = unnamed_1113;
constraint ((unnamed_1113 = 1)) -> imapget_1114 >= 1;
constraint ((unnamed_1113 = 2)) -> imapget_1114 >= 2;
constraint ((unnamed_1113 = 3)) -> imapget_1114 >= 3;
constraint ((unnamed_1113 = 4)) -> imapget_1114 >= 4;
constraint ((unnamed_1113 = 5)) -> imapget_1114 >= 5;
constraint ((unnamed_1113 = 6)) -> imapget_1114 >= 6;
constraint ((unnamed_1113 = 7)) -> imapget_1114 >= 7;
constraint ((unnamed_1113 = 8)) -> imapget_1114 >= 8;
constraint ((unnamed_1113 = 9)) -> imapget_1114 >= 9;
constraint ((unnamed_1113 = 10)) -> imapget_1114 >= 10;
constraint mapget_1114 = [20, 24, 25, 27, 28, 29, 30, 32, 33, 34, 34][imapget_1114];

var 1..10: location2_1115; %ref (Literal: 0 [0]).location2 -25
% doing constraints for lookup query: ref (Literal: 0 [0]).location2 -25
var 1..1: ilocation2_1115;
constraint location2_1115 = [nextLocation_1103, 10][ilocation2_1115];

var 1..10: unnamed_1118; %ref (Literal: 0 [0]).unnamed -28
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -28
var 1..1: iunnamed_1118;
constraint unnamed_1118 = [location2_1115, 10][iunnamed_1118];

var 0..20: mapget_1119; %optimise.state.MapGet@45f
% doing constraints for lookup query: optimise.state.MapGet@45f
var 1..100: imapget_1119;
constraint [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, mapget_1114][imapget_1119] = mapget_1114;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_1118][imapget_1119] = unnamed_1118;
constraint (((mapget_1114 = 20) /\ (unnamed_1118 = 1))) -> imapget_1119 >= 1;
constraint (((mapget_1114 = 20) /\ (unnamed_1118 = 2))) -> imapget_1119 >= 2;
constraint (((mapget_1114 = 20) /\ (unnamed_1118 = 3))) -> imapget_1119 >= 3;
constraint (((mapget_1114 = 20) /\ (unnamed_1118 = 4))) -> imapget_1119 >= 4;
constraint (((mapget_1114 = 20) /\ (unnamed_1118 = 5))) -> imapget_1119 >= 5;
constraint (((mapget_1114 = 20) /\ (unnamed_1118 = 6))) -> imapget_1119 >= 6;
constraint (((mapget_1114 = 20) /\ (unnamed_1118 = 7))) -> imapget_1119 >= 7;
constraint (((mapget_1114 = 20) /\ (unnamed_1118 = 8))) -> imapget_1119 >= 8;
constraint (((mapget_1114 = 20) /\ (unnamed_1118 = 9))) -> imapget_1119 >= 9;
constraint (((mapget_1114 = 20) /\ (unnamed_1118 = 10))) -> imapget_1119 >= 10;
constraint (((mapget_1114 = 24) /\ (unnamed_1118 = 1))) -> imapget_1119 >= 11;
constraint (((mapget_1114 = 24) /\ (unnamed_1118 = 2))) -> imapget_1119 >= 12;
constraint (((mapget_1114 = 24) /\ (unnamed_1118 = 3))) -> imapget_1119 >= 13;
constraint (((mapget_1114 = 24) /\ (unnamed_1118 = 4))) -> imapget_1119 >= 14;
constraint (((mapget_1114 = 24) /\ (unnamed_1118 = 5))) -> imapget_1119 >= 15;
constraint (((mapget_1114 = 24) /\ (unnamed_1118 = 6))) -> imapget_1119 >= 16;
constraint (((mapget_1114 = 24) /\ (unnamed_1118 = 7))) -> imapget_1119 >= 17;
constraint (((mapget_1114 = 24) /\ (unnamed_1118 = 8))) -> imapget_1119 >= 18;
constraint (((mapget_1114 = 24) /\ (unnamed_1118 = 9))) -> imapget_1119 >= 19;
constraint (((mapget_1114 = 24) /\ (unnamed_1118 = 10))) -> imapget_1119 >= 20;
constraint (((mapget_1114 = 25) /\ (unnamed_1118 = 1))) -> imapget_1119 >= 21;
constraint (((mapget_1114 = 25) /\ (unnamed_1118 = 2))) -> imapget_1119 >= 22;
constraint (((mapget_1114 = 25) /\ (unnamed_1118 = 3))) -> imapget_1119 >= 23;
constraint (((mapget_1114 = 25) /\ (unnamed_1118 = 4))) -> imapget_1119 >= 24;
constraint (((mapget_1114 = 25) /\ (unnamed_1118 = 5))) -> imapget_1119 >= 25;
constraint (((mapget_1114 = 25) /\ (unnamed_1118 = 6))) -> imapget_1119 >= 26;
constraint (((mapget_1114 = 25) /\ (unnamed_1118 = 7))) -> imapget_1119 >= 27;
constraint (((mapget_1114 = 25) /\ (unnamed_1118 = 8))) -> imapget_1119 >= 28;
constraint (((mapget_1114 = 25) /\ (unnamed_1118 = 9))) -> imapget_1119 >= 29;
constraint (((mapget_1114 = 25) /\ (unnamed_1118 = 10))) -> imapget_1119 >= 30;
constraint (((mapget_1114 = 27) /\ (unnamed_1118 = 1))) -> imapget_1119 >= 31;
constraint (((mapget_1114 = 27) /\ (unnamed_1118 = 2))) -> imapget_1119 >= 32;
constraint (((mapget_1114 = 27) /\ (unnamed_1118 = 3))) -> imapget_1119 >= 33;
constraint (((mapget_1114 = 27) /\ (unnamed_1118 = 4))) -> imapget_1119 >= 34;
constraint (((mapget_1114 = 27) /\ (unnamed_1118 = 5))) -> imapget_1119 >= 35;
constraint (((mapget_1114 = 27) /\ (unnamed_1118 = 6))) -> imapget_1119 >= 36;
constraint (((mapget_1114 = 27) /\ (unnamed_1118 = 7))) -> imapget_1119 >= 37;
constraint (((mapget_1114 = 27) /\ (unnamed_1118 = 8))) -> imapget_1119 >= 38;
constraint (((mapget_1114 = 27) /\ (unnamed_1118 = 9))) -> imapget_1119 >= 39;
constraint (((mapget_1114 = 27) /\ (unnamed_1118 = 10))) -> imapget_1119 >= 40;
constraint (((mapget_1114 = 28) /\ (unnamed_1118 = 1))) -> imapget_1119 >= 41;
constraint (((mapget_1114 = 28) /\ (unnamed_1118 = 2))) -> imapget_1119 >= 42;
constraint (((mapget_1114 = 28) /\ (unnamed_1118 = 3))) -> imapget_1119 >= 43;
constraint (((mapget_1114 = 28) /\ (unnamed_1118 = 4))) -> imapget_1119 >= 44;
constraint (((mapget_1114 = 28) /\ (unnamed_1118 = 5))) -> imapget_1119 >= 45;
constraint (((mapget_1114 = 28) /\ (unnamed_1118 = 6))) -> imapget_1119 >= 46;
constraint (((mapget_1114 = 28) /\ (unnamed_1118 = 7))) -> imapget_1119 >= 47;
constraint (((mapget_1114 = 28) /\ (unnamed_1118 = 8))) -> imapget_1119 >= 48;
constraint (((mapget_1114 = 28) /\ (unnamed_1118 = 9))) -> imapget_1119 >= 49;
constraint (((mapget_1114 = 28) /\ (unnamed_1118 = 10))) -> imapget_1119 >= 50;
constraint (((mapget_1114 = 29) /\ (unnamed_1118 = 1))) -> imapget_1119 >= 51;
constraint (((mapget_1114 = 29) /\ (unnamed_1118 = 2))) -> imapget_1119 >= 52;
constraint (((mapget_1114 = 29) /\ (unnamed_1118 = 3))) -> imapget_1119 >= 53;
constraint (((mapget_1114 = 29) /\ (unnamed_1118 = 4))) -> imapget_1119 >= 54;
constraint (((mapget_1114 = 29) /\ (unnamed_1118 = 5))) -> imapget_1119 >= 55;
constraint (((mapget_1114 = 29) /\ (unnamed_1118 = 6))) -> imapget_1119 >= 56;
constraint (((mapget_1114 = 29) /\ (unnamed_1118 = 7))) -> imapget_1119 >= 57;
constraint (((mapget_1114 = 29) /\ (unnamed_1118 = 8))) -> imapget_1119 >= 58;
constraint (((mapget_1114 = 29) /\ (unnamed_1118 = 9))) -> imapget_1119 >= 59;
constraint (((mapget_1114 = 29) /\ (unnamed_1118 = 10))) -> imapget_1119 >= 60;
constraint (((mapget_1114 = 30) /\ (unnamed_1118 = 1))) -> imapget_1119 >= 61;
constraint (((mapget_1114 = 30) /\ (unnamed_1118 = 2))) -> imapget_1119 >= 62;
constraint (((mapget_1114 = 30) /\ (unnamed_1118 = 3))) -> imapget_1119 >= 63;
constraint (((mapget_1114 = 30) /\ (unnamed_1118 = 4))) -> imapget_1119 >= 64;
constraint (((mapget_1114 = 30) /\ (unnamed_1118 = 5))) -> imapget_1119 >= 65;
constraint (((mapget_1114 = 30) /\ (unnamed_1118 = 6))) -> imapget_1119 >= 66;
constraint (((mapget_1114 = 30) /\ (unnamed_1118 = 7))) -> imapget_1119 >= 67;
constraint (((mapget_1114 = 30) /\ (unnamed_1118 = 8))) -> imapget_1119 >= 68;
constraint (((mapget_1114 = 30) /\ (unnamed_1118 = 9))) -> imapget_1119 >= 69;
constraint (((mapget_1114 = 30) /\ (unnamed_1118 = 10))) -> imapget_1119 >= 70;
constraint (((mapget_1114 = 32) /\ (unnamed_1118 = 1))) -> imapget_1119 >= 71;
constraint (((mapget_1114 = 32) /\ (unnamed_1118 = 2))) -> imapget_1119 >= 72;
constraint (((mapget_1114 = 32) /\ (unnamed_1118 = 3))) -> imapget_1119 >= 73;
constraint (((mapget_1114 = 32) /\ (unnamed_1118 = 4))) -> imapget_1119 >= 74;
constraint (((mapget_1114 = 32) /\ (unnamed_1118 = 5))) -> imapget_1119 >= 75;
constraint (((mapget_1114 = 32) /\ (unnamed_1118 = 6))) -> imapget_1119 >= 76;
constraint (((mapget_1114 = 32) /\ (unnamed_1118 = 7))) -> imapget_1119 >= 77;
constraint (((mapget_1114 = 32) /\ (unnamed_1118 = 8))) -> imapget_1119 >= 78;
constraint (((mapget_1114 = 32) /\ (unnamed_1118 = 9))) -> imapget_1119 >= 79;
constraint (((mapget_1114 = 32) /\ (unnamed_1118 = 10))) -> imapget_1119 >= 80;
constraint (((mapget_1114 = 33) /\ (unnamed_1118 = 1))) -> imapget_1119 >= 81;
constraint (((mapget_1114 = 33) /\ (unnamed_1118 = 2))) -> imapget_1119 >= 82;
constraint (((mapget_1114 = 33) /\ (unnamed_1118 = 3))) -> imapget_1119 >= 83;
constraint (((mapget_1114 = 33) /\ (unnamed_1118 = 4))) -> imapget_1119 >= 84;
constraint (((mapget_1114 = 33) /\ (unnamed_1118 = 5))) -> imapget_1119 >= 85;
constraint (((mapget_1114 = 33) /\ (unnamed_1118 = 6))) -> imapget_1119 >= 86;
constraint (((mapget_1114 = 33) /\ (unnamed_1118 = 7))) -> imapget_1119 >= 87;
constraint (((mapget_1114 = 33) /\ (unnamed_1118 = 8))) -> imapget_1119 >= 88;
constraint (((mapget_1114 = 33) /\ (unnamed_1118 = 9))) -> imapget_1119 >= 89;
constraint (((mapget_1114 = 33) /\ (unnamed_1118 = 10))) -> imapget_1119 >= 90;
constraint (((mapget_1114 = 34) /\ (unnamed_1118 = 1))) -> imapget_1119 >= 91;
constraint (((mapget_1114 = 34) /\ (unnamed_1118 = 2))) -> imapget_1119 >= 92;
constraint (((mapget_1114 = 34) /\ (unnamed_1118 = 3))) -> imapget_1119 >= 93;
constraint (((mapget_1114 = 34) /\ (unnamed_1118 = 4))) -> imapget_1119 >= 94;
constraint (((mapget_1114 = 34) /\ (unnamed_1118 = 5))) -> imapget_1119 >= 95;
constraint (((mapget_1114 = 34) /\ (unnamed_1118 = 6))) -> imapget_1119 >= 96;
constraint (((mapget_1114 = 34) /\ (unnamed_1118 = 7))) -> imapget_1119 >= 97;
constraint (((mapget_1114 = 34) /\ (unnamed_1118 = 8))) -> imapget_1119 >= 98;
constraint (((mapget_1114 = 34) /\ (unnamed_1118 = 9))) -> imapget_1119 >= 99;
constraint (((mapget_1114 = 34) /\ (unnamed_1118 = 10))) -> imapget_1119 >= 100;
constraint mapget_1119 = [0, 15, 16, 16, 6, 8, 8, 3, 4, 17, 15, 0, 11, 18, 10, 12, 18, 4, 11, 7, 16, 11, 0, 13, 13, 12, 8, 1, 14, 5, 16, 18, 13, 0, 12, 16, 6, 5, 15, 12, 6, 10, 13, 12, 0, 2, 8, 19, 9, 5, 8, 12, 12, 16, 2, 0, 11, 14, 16, 8, 8, 18, 8, 6, 8, 11, 0, 11, 20, 19, 3, 4, 1, 5, 19, 14, 11, 0, 7, 2, 4, 11, 14, 15, 9, 16, 20, 7, 0, 12, 17, 7, 5, 12, 5, 8, 19, 2, 12, 0, 20][imapget_1119];

var 0..20: ret_travelTime_1123; %ref (Literal: 0 [0]).ret_travelTime -26
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_travelTime -26
var 1..1: iret_travelTime_1123;
constraint ret_travelTime_1123 = [mapget_1119, 20][iret_travelTime_1123];

var 2..99: Add_1124 = (currentTime_1099 + ret_travelTime_1123);

var 1..10: nextLocation_1126; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_1126;
constraint nextLocation_1126 = [ret_getLocation_1096, 10][inextLocation_1126];

var {36,39,42,45,48,51,54,57,60,63}: listget_1139; %optimise.state.ListGet@473
constraint listget_1139 = chooseOrderVal_2[6];

var {36,39,42,45,48,51,54,57,60,63}: stop_1151; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_1151;
constraint stop_1151 = [listget_1139, 63][istop_1151];

var 1..10: locationID_1157; %ref ref (Literal: 0 [0]).stop -21.locationID -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).stop -21.locationID -7
var 1..10: ilocationID_1157;
constraint [36, 39, 42, 45, 48, 51, 54, 57, 60, 63, stop_1151][ilocationID_1157] = stop_1151;
constraint ((stop_1151 = 36)) -> ilocationID_1157 >= 1;
constraint ((stop_1151 = 39)) -> ilocationID_1157 >= 2;
constraint ((stop_1151 = 42)) -> ilocationID_1157 >= 3;
constraint ((stop_1151 = 45)) -> ilocationID_1157 >= 4;
constraint ((stop_1151 = 48)) -> ilocationID_1157 >= 5;
constraint ((stop_1151 = 51)) -> ilocationID_1157 >= 6;
constraint ((stop_1151 = 54)) -> ilocationID_1157 >= 7;
constraint ((stop_1151 = 57)) -> ilocationID_1157 >= 8;
constraint ((stop_1151 = 60)) -> ilocationID_1157 >= 9;
constraint ((stop_1151 = 63)) -> ilocationID_1157 >= 10;
constraint locationID_1157 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10][ilocationID_1157];

var 1..10: ret_getLocation_1161; %ref (Literal: 0 [0]).ret_getLocation -22
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getLocation -22
var 1..1: iret_getLocation_1161;
constraint ret_getLocation_1161 = [locationID_1157, 10][iret_getLocation_1161];

var 2..99: currentTime_1164; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_1164;
constraint currentTime_1164 = [Add_1124, 99][icurrentTime_1164];

var 1..10: currentLocation_1165; %ref (Literal: 0 [0]).currentLocation -19
% doing constraints for lookup query: ref (Literal: 0 [0]).currentLocation -19
var 1..1: icurrentLocation_1165;
constraint currentLocation_1165 = [nextLocation_1126, 10][icurrentLocation_1165];

var 1..10: nextLocation_1168; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_1168;
constraint nextLocation_1168 = [ret_getLocation_1161, 10][inextLocation_1168];

var 1..10: location1_1175; %ref (Literal: 0 [0]).location1 -24
% doing constraints for lookup query: ref (Literal: 0 [0]).location1 -24
var 1..1: ilocation1_1175;
constraint location1_1175 = [currentLocation_1165, 10][ilocation1_1175];

var 1..10: unnamed_1178; %ref (Literal: 0 [0]).unnamed -27
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -27
var 1..1: iunnamed_1178;
constraint unnamed_1178 = [location1_1175, 10][iunnamed_1178];

var {20,24,25,27,28,29,30,32,33,34}: mapget_1179; %optimise.state.MapGet@49b
% doing constraints for lookup query: optimise.state.MapGet@49b
var 1..10: imapget_1179;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_1178][imapget_1179] = unnamed_1178;
constraint ((unnamed_1178 = 1)) -> imapget_1179 >= 1;
constraint ((unnamed_1178 = 2)) -> imapget_1179 >= 2;
constraint ((unnamed_1178 = 3)) -> imapget_1179 >= 3;
constraint ((unnamed_1178 = 4)) -> imapget_1179 >= 4;
constraint ((unnamed_1178 = 5)) -> imapget_1179 >= 5;
constraint ((unnamed_1178 = 6)) -> imapget_1179 >= 6;
constraint ((unnamed_1178 = 7)) -> imapget_1179 >= 7;
constraint ((unnamed_1178 = 8)) -> imapget_1179 >= 8;
constraint ((unnamed_1178 = 9)) -> imapget_1179 >= 9;
constraint ((unnamed_1178 = 10)) -> imapget_1179 >= 10;
constraint mapget_1179 = [20, 24, 25, 27, 28, 29, 30, 32, 33, 34, 34][imapget_1179];

var 1..10: location2_1180; %ref (Literal: 0 [0]).location2 -25
% doing constraints for lookup query: ref (Literal: 0 [0]).location2 -25
var 1..1: ilocation2_1180;
constraint location2_1180 = [nextLocation_1168, 10][ilocation2_1180];

var 1..10: unnamed_1183; %ref (Literal: 0 [0]).unnamed -28
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -28
var 1..1: iunnamed_1183;
constraint unnamed_1183 = [location2_1180, 10][iunnamed_1183];

var 0..20: mapget_1184; %optimise.state.MapGet@4a0
% doing constraints for lookup query: optimise.state.MapGet@4a0
var 1..100: imapget_1184;
constraint [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, mapget_1179][imapget_1184] = mapget_1179;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_1183][imapget_1184] = unnamed_1183;
constraint (((mapget_1179 = 20) /\ (unnamed_1183 = 1))) -> imapget_1184 >= 1;
constraint (((mapget_1179 = 20) /\ (unnamed_1183 = 2))) -> imapget_1184 >= 2;
constraint (((mapget_1179 = 20) /\ (unnamed_1183 = 3))) -> imapget_1184 >= 3;
constraint (((mapget_1179 = 20) /\ (unnamed_1183 = 4))) -> imapget_1184 >= 4;
constraint (((mapget_1179 = 20) /\ (unnamed_1183 = 5))) -> imapget_1184 >= 5;
constraint (((mapget_1179 = 20) /\ (unnamed_1183 = 6))) -> imapget_1184 >= 6;
constraint (((mapget_1179 = 20) /\ (unnamed_1183 = 7))) -> imapget_1184 >= 7;
constraint (((mapget_1179 = 20) /\ (unnamed_1183 = 8))) -> imapget_1184 >= 8;
constraint (((mapget_1179 = 20) /\ (unnamed_1183 = 9))) -> imapget_1184 >= 9;
constraint (((mapget_1179 = 20) /\ (unnamed_1183 = 10))) -> imapget_1184 >= 10;
constraint (((mapget_1179 = 24) /\ (unnamed_1183 = 1))) -> imapget_1184 >= 11;
constraint (((mapget_1179 = 24) /\ (unnamed_1183 = 2))) -> imapget_1184 >= 12;
constraint (((mapget_1179 = 24) /\ (unnamed_1183 = 3))) -> imapget_1184 >= 13;
constraint (((mapget_1179 = 24) /\ (unnamed_1183 = 4))) -> imapget_1184 >= 14;
constraint (((mapget_1179 = 24) /\ (unnamed_1183 = 5))) -> imapget_1184 >= 15;
constraint (((mapget_1179 = 24) /\ (unnamed_1183 = 6))) -> imapget_1184 >= 16;
constraint (((mapget_1179 = 24) /\ (unnamed_1183 = 7))) -> imapget_1184 >= 17;
constraint (((mapget_1179 = 24) /\ (unnamed_1183 = 8))) -> imapget_1184 >= 18;
constraint (((mapget_1179 = 24) /\ (unnamed_1183 = 9))) -> imapget_1184 >= 19;
constraint (((mapget_1179 = 24) /\ (unnamed_1183 = 10))) -> imapget_1184 >= 20;
constraint (((mapget_1179 = 25) /\ (unnamed_1183 = 1))) -> imapget_1184 >= 21;
constraint (((mapget_1179 = 25) /\ (unnamed_1183 = 2))) -> imapget_1184 >= 22;
constraint (((mapget_1179 = 25) /\ (unnamed_1183 = 3))) -> imapget_1184 >= 23;
constraint (((mapget_1179 = 25) /\ (unnamed_1183 = 4))) -> imapget_1184 >= 24;
constraint (((mapget_1179 = 25) /\ (unnamed_1183 = 5))) -> imapget_1184 >= 25;
constraint (((mapget_1179 = 25) /\ (unnamed_1183 = 6))) -> imapget_1184 >= 26;
constraint (((mapget_1179 = 25) /\ (unnamed_1183 = 7))) -> imapget_1184 >= 27;
constraint (((mapget_1179 = 25) /\ (unnamed_1183 = 8))) -> imapget_1184 >= 28;
constraint (((mapget_1179 = 25) /\ (unnamed_1183 = 9))) -> imapget_1184 >= 29;
constraint (((mapget_1179 = 25) /\ (unnamed_1183 = 10))) -> imapget_1184 >= 30;
constraint (((mapget_1179 = 27) /\ (unnamed_1183 = 1))) -> imapget_1184 >= 31;
constraint (((mapget_1179 = 27) /\ (unnamed_1183 = 2))) -> imapget_1184 >= 32;
constraint (((mapget_1179 = 27) /\ (unnamed_1183 = 3))) -> imapget_1184 >= 33;
constraint (((mapget_1179 = 27) /\ (unnamed_1183 = 4))) -> imapget_1184 >= 34;
constraint (((mapget_1179 = 27) /\ (unnamed_1183 = 5))) -> imapget_1184 >= 35;
constraint (((mapget_1179 = 27) /\ (unnamed_1183 = 6))) -> imapget_1184 >= 36;
constraint (((mapget_1179 = 27) /\ (unnamed_1183 = 7))) -> imapget_1184 >= 37;
constraint (((mapget_1179 = 27) /\ (unnamed_1183 = 8))) -> imapget_1184 >= 38;
constraint (((mapget_1179 = 27) /\ (unnamed_1183 = 9))) -> imapget_1184 >= 39;
constraint (((mapget_1179 = 27) /\ (unnamed_1183 = 10))) -> imapget_1184 >= 40;
constraint (((mapget_1179 = 28) /\ (unnamed_1183 = 1))) -> imapget_1184 >= 41;
constraint (((mapget_1179 = 28) /\ (unnamed_1183 = 2))) -> imapget_1184 >= 42;
constraint (((mapget_1179 = 28) /\ (unnamed_1183 = 3))) -> imapget_1184 >= 43;
constraint (((mapget_1179 = 28) /\ (unnamed_1183 = 4))) -> imapget_1184 >= 44;
constraint (((mapget_1179 = 28) /\ (unnamed_1183 = 5))) -> imapget_1184 >= 45;
constraint (((mapget_1179 = 28) /\ (unnamed_1183 = 6))) -> imapget_1184 >= 46;
constraint (((mapget_1179 = 28) /\ (unnamed_1183 = 7))) -> imapget_1184 >= 47;
constraint (((mapget_1179 = 28) /\ (unnamed_1183 = 8))) -> imapget_1184 >= 48;
constraint (((mapget_1179 = 28) /\ (unnamed_1183 = 9))) -> imapget_1184 >= 49;
constraint (((mapget_1179 = 28) /\ (unnamed_1183 = 10))) -> imapget_1184 >= 50;
constraint (((mapget_1179 = 29) /\ (unnamed_1183 = 1))) -> imapget_1184 >= 51;
constraint (((mapget_1179 = 29) /\ (unnamed_1183 = 2))) -> imapget_1184 >= 52;
constraint (((mapget_1179 = 29) /\ (unnamed_1183 = 3))) -> imapget_1184 >= 53;
constraint (((mapget_1179 = 29) /\ (unnamed_1183 = 4))) -> imapget_1184 >= 54;
constraint (((mapget_1179 = 29) /\ (unnamed_1183 = 5))) -> imapget_1184 >= 55;
constraint (((mapget_1179 = 29) /\ (unnamed_1183 = 6))) -> imapget_1184 >= 56;
constraint (((mapget_1179 = 29) /\ (unnamed_1183 = 7))) -> imapget_1184 >= 57;
constraint (((mapget_1179 = 29) /\ (unnamed_1183 = 8))) -> imapget_1184 >= 58;
constraint (((mapget_1179 = 29) /\ (unnamed_1183 = 9))) -> imapget_1184 >= 59;
constraint (((mapget_1179 = 29) /\ (unnamed_1183 = 10))) -> imapget_1184 >= 60;
constraint (((mapget_1179 = 30) /\ (unnamed_1183 = 1))) -> imapget_1184 >= 61;
constraint (((mapget_1179 = 30) /\ (unnamed_1183 = 2))) -> imapget_1184 >= 62;
constraint (((mapget_1179 = 30) /\ (unnamed_1183 = 3))) -> imapget_1184 >= 63;
constraint (((mapget_1179 = 30) /\ (unnamed_1183 = 4))) -> imapget_1184 >= 64;
constraint (((mapget_1179 = 30) /\ (unnamed_1183 = 5))) -> imapget_1184 >= 65;
constraint (((mapget_1179 = 30) /\ (unnamed_1183 = 6))) -> imapget_1184 >= 66;
constraint (((mapget_1179 = 30) /\ (unnamed_1183 = 7))) -> imapget_1184 >= 67;
constraint (((mapget_1179 = 30) /\ (unnamed_1183 = 8))) -> imapget_1184 >= 68;
constraint (((mapget_1179 = 30) /\ (unnamed_1183 = 9))) -> imapget_1184 >= 69;
constraint (((mapget_1179 = 30) /\ (unnamed_1183 = 10))) -> imapget_1184 >= 70;
constraint (((mapget_1179 = 32) /\ (unnamed_1183 = 1))) -> imapget_1184 >= 71;
constraint (((mapget_1179 = 32) /\ (unnamed_1183 = 2))) -> imapget_1184 >= 72;
constraint (((mapget_1179 = 32) /\ (unnamed_1183 = 3))) -> imapget_1184 >= 73;
constraint (((mapget_1179 = 32) /\ (unnamed_1183 = 4))) -> imapget_1184 >= 74;
constraint (((mapget_1179 = 32) /\ (unnamed_1183 = 5))) -> imapget_1184 >= 75;
constraint (((mapget_1179 = 32) /\ (unnamed_1183 = 6))) -> imapget_1184 >= 76;
constraint (((mapget_1179 = 32) /\ (unnamed_1183 = 7))) -> imapget_1184 >= 77;
constraint (((mapget_1179 = 32) /\ (unnamed_1183 = 8))) -> imapget_1184 >= 78;
constraint (((mapget_1179 = 32) /\ (unnamed_1183 = 9))) -> imapget_1184 >= 79;
constraint (((mapget_1179 = 32) /\ (unnamed_1183 = 10))) -> imapget_1184 >= 80;
constraint (((mapget_1179 = 33) /\ (unnamed_1183 = 1))) -> imapget_1184 >= 81;
constraint (((mapget_1179 = 33) /\ (unnamed_1183 = 2))) -> imapget_1184 >= 82;
constraint (((mapget_1179 = 33) /\ (unnamed_1183 = 3))) -> imapget_1184 >= 83;
constraint (((mapget_1179 = 33) /\ (unnamed_1183 = 4))) -> imapget_1184 >= 84;
constraint (((mapget_1179 = 33) /\ (unnamed_1183 = 5))) -> imapget_1184 >= 85;
constraint (((mapget_1179 = 33) /\ (unnamed_1183 = 6))) -> imapget_1184 >= 86;
constraint (((mapget_1179 = 33) /\ (unnamed_1183 = 7))) -> imapget_1184 >= 87;
constraint (((mapget_1179 = 33) /\ (unnamed_1183 = 8))) -> imapget_1184 >= 88;
constraint (((mapget_1179 = 33) /\ (unnamed_1183 = 9))) -> imapget_1184 >= 89;
constraint (((mapget_1179 = 33) /\ (unnamed_1183 = 10))) -> imapget_1184 >= 90;
constraint (((mapget_1179 = 34) /\ (unnamed_1183 = 1))) -> imapget_1184 >= 91;
constraint (((mapget_1179 = 34) /\ (unnamed_1183 = 2))) -> imapget_1184 >= 92;
constraint (((mapget_1179 = 34) /\ (unnamed_1183 = 3))) -> imapget_1184 >= 93;
constraint (((mapget_1179 = 34) /\ (unnamed_1183 = 4))) -> imapget_1184 >= 94;
constraint (((mapget_1179 = 34) /\ (unnamed_1183 = 5))) -> imapget_1184 >= 95;
constraint (((mapget_1179 = 34) /\ (unnamed_1183 = 6))) -> imapget_1184 >= 96;
constraint (((mapget_1179 = 34) /\ (unnamed_1183 = 7))) -> imapget_1184 >= 97;
constraint (((mapget_1179 = 34) /\ (unnamed_1183 = 8))) -> imapget_1184 >= 98;
constraint (((mapget_1179 = 34) /\ (unnamed_1183 = 9))) -> imapget_1184 >= 99;
constraint (((mapget_1179 = 34) /\ (unnamed_1183 = 10))) -> imapget_1184 >= 100;
constraint mapget_1184 = [0, 15, 16, 16, 6, 8, 8, 3, 4, 17, 15, 0, 11, 18, 10, 12, 18, 4, 11, 7, 16, 11, 0, 13, 13, 12, 8, 1, 14, 5, 16, 18, 13, 0, 12, 16, 6, 5, 15, 12, 6, 10, 13, 12, 0, 2, 8, 19, 9, 5, 8, 12, 12, 16, 2, 0, 11, 14, 16, 8, 8, 18, 8, 6, 8, 11, 0, 11, 20, 19, 3, 4, 1, 5, 19, 14, 11, 0, 7, 2, 4, 11, 14, 15, 9, 16, 20, 7, 0, 12, 17, 7, 5, 12, 5, 8, 19, 2, 12, 0, 20][imapget_1184];

var 0..20: ret_travelTime_1188; %ref (Literal: 0 [0]).ret_travelTime -26
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_travelTime -26
var 1..1: iret_travelTime_1188;
constraint ret_travelTime_1188 = [mapget_1184, 20][iret_travelTime_1188];

var 2..119: Add_1189 = (currentTime_1164 + ret_travelTime_1188);

var 1..10: nextLocation_1191; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_1191;
constraint nextLocation_1191 = [ret_getLocation_1161, 10][inextLocation_1191];

var {36,39,42,45,48,51,54,57,60,63}: listget_1204; %optimise.state.ListGet@4b4
constraint listget_1204 = chooseOrderVal_2[7];

var {36,39,42,45,48,51,54,57,60,63}: stop_1216; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_1216;
constraint stop_1216 = [listget_1204, 63][istop_1216];

var 1..10: locationID_1222; %ref ref (Literal: 0 [0]).stop -21.locationID -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).stop -21.locationID -7
var 1..10: ilocationID_1222;
constraint [36, 39, 42, 45, 48, 51, 54, 57, 60, 63, stop_1216][ilocationID_1222] = stop_1216;
constraint ((stop_1216 = 36)) -> ilocationID_1222 >= 1;
constraint ((stop_1216 = 39)) -> ilocationID_1222 >= 2;
constraint ((stop_1216 = 42)) -> ilocationID_1222 >= 3;
constraint ((stop_1216 = 45)) -> ilocationID_1222 >= 4;
constraint ((stop_1216 = 48)) -> ilocationID_1222 >= 5;
constraint ((stop_1216 = 51)) -> ilocationID_1222 >= 6;
constraint ((stop_1216 = 54)) -> ilocationID_1222 >= 7;
constraint ((stop_1216 = 57)) -> ilocationID_1222 >= 8;
constraint ((stop_1216 = 60)) -> ilocationID_1222 >= 9;
constraint ((stop_1216 = 63)) -> ilocationID_1222 >= 10;
constraint locationID_1222 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10][ilocationID_1222];

var 1..10: ret_getLocation_1226; %ref (Literal: 0 [0]).ret_getLocation -22
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getLocation -22
var 1..1: iret_getLocation_1226;
constraint ret_getLocation_1226 = [locationID_1222, 10][iret_getLocation_1226];

var 2..119: currentTime_1229; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_1229;
constraint currentTime_1229 = [Add_1189, 119][icurrentTime_1229];

var 1..10: currentLocation_1230; %ref (Literal: 0 [0]).currentLocation -19
% doing constraints for lookup query: ref (Literal: 0 [0]).currentLocation -19
var 1..1: icurrentLocation_1230;
constraint currentLocation_1230 = [nextLocation_1191, 10][icurrentLocation_1230];

var 1..10: nextLocation_1233; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_1233;
constraint nextLocation_1233 = [ret_getLocation_1226, 10][inextLocation_1233];

var 1..10: location1_1240; %ref (Literal: 0 [0]).location1 -24
% doing constraints for lookup query: ref (Literal: 0 [0]).location1 -24
var 1..1: ilocation1_1240;
constraint location1_1240 = [currentLocation_1230, 10][ilocation1_1240];

var 1..10: unnamed_1243; %ref (Literal: 0 [0]).unnamed -27
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -27
var 1..1: iunnamed_1243;
constraint unnamed_1243 = [location1_1240, 10][iunnamed_1243];

var {20,24,25,27,28,29,30,32,33,34}: mapget_1244; %optimise.state.MapGet@4dc
% doing constraints for lookup query: optimise.state.MapGet@4dc
var 1..10: imapget_1244;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_1243][imapget_1244] = unnamed_1243;
constraint ((unnamed_1243 = 1)) -> imapget_1244 >= 1;
constraint ((unnamed_1243 = 2)) -> imapget_1244 >= 2;
constraint ((unnamed_1243 = 3)) -> imapget_1244 >= 3;
constraint ((unnamed_1243 = 4)) -> imapget_1244 >= 4;
constraint ((unnamed_1243 = 5)) -> imapget_1244 >= 5;
constraint ((unnamed_1243 = 6)) -> imapget_1244 >= 6;
constraint ((unnamed_1243 = 7)) -> imapget_1244 >= 7;
constraint ((unnamed_1243 = 8)) -> imapget_1244 >= 8;
constraint ((unnamed_1243 = 9)) -> imapget_1244 >= 9;
constraint ((unnamed_1243 = 10)) -> imapget_1244 >= 10;
constraint mapget_1244 = [20, 24, 25, 27, 28, 29, 30, 32, 33, 34, 34][imapget_1244];

var 1..10: location2_1245; %ref (Literal: 0 [0]).location2 -25
% doing constraints for lookup query: ref (Literal: 0 [0]).location2 -25
var 1..1: ilocation2_1245;
constraint location2_1245 = [nextLocation_1233, 10][ilocation2_1245];

var 1..10: unnamed_1248; %ref (Literal: 0 [0]).unnamed -28
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -28
var 1..1: iunnamed_1248;
constraint unnamed_1248 = [location2_1245, 10][iunnamed_1248];

var 0..20: mapget_1249; %optimise.state.MapGet@4e1
% doing constraints for lookup query: optimise.state.MapGet@4e1
var 1..100: imapget_1249;
constraint [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, mapget_1244][imapget_1249] = mapget_1244;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_1248][imapget_1249] = unnamed_1248;
constraint (((mapget_1244 = 20) /\ (unnamed_1248 = 1))) -> imapget_1249 >= 1;
constraint (((mapget_1244 = 20) /\ (unnamed_1248 = 2))) -> imapget_1249 >= 2;
constraint (((mapget_1244 = 20) /\ (unnamed_1248 = 3))) -> imapget_1249 >= 3;
constraint (((mapget_1244 = 20) /\ (unnamed_1248 = 4))) -> imapget_1249 >= 4;
constraint (((mapget_1244 = 20) /\ (unnamed_1248 = 5))) -> imapget_1249 >= 5;
constraint (((mapget_1244 = 20) /\ (unnamed_1248 = 6))) -> imapget_1249 >= 6;
constraint (((mapget_1244 = 20) /\ (unnamed_1248 = 7))) -> imapget_1249 >= 7;
constraint (((mapget_1244 = 20) /\ (unnamed_1248 = 8))) -> imapget_1249 >= 8;
constraint (((mapget_1244 = 20) /\ (unnamed_1248 = 9))) -> imapget_1249 >= 9;
constraint (((mapget_1244 = 20) /\ (unnamed_1248 = 10))) -> imapget_1249 >= 10;
constraint (((mapget_1244 = 24) /\ (unnamed_1248 = 1))) -> imapget_1249 >= 11;
constraint (((mapget_1244 = 24) /\ (unnamed_1248 = 2))) -> imapget_1249 >= 12;
constraint (((mapget_1244 = 24) /\ (unnamed_1248 = 3))) -> imapget_1249 >= 13;
constraint (((mapget_1244 = 24) /\ (unnamed_1248 = 4))) -> imapget_1249 >= 14;
constraint (((mapget_1244 = 24) /\ (unnamed_1248 = 5))) -> imapget_1249 >= 15;
constraint (((mapget_1244 = 24) /\ (unnamed_1248 = 6))) -> imapget_1249 >= 16;
constraint (((mapget_1244 = 24) /\ (unnamed_1248 = 7))) -> imapget_1249 >= 17;
constraint (((mapget_1244 = 24) /\ (unnamed_1248 = 8))) -> imapget_1249 >= 18;
constraint (((mapget_1244 = 24) /\ (unnamed_1248 = 9))) -> imapget_1249 >= 19;
constraint (((mapget_1244 = 24) /\ (unnamed_1248 = 10))) -> imapget_1249 >= 20;
constraint (((mapget_1244 = 25) /\ (unnamed_1248 = 1))) -> imapget_1249 >= 21;
constraint (((mapget_1244 = 25) /\ (unnamed_1248 = 2))) -> imapget_1249 >= 22;
constraint (((mapget_1244 = 25) /\ (unnamed_1248 = 3))) -> imapget_1249 >= 23;
constraint (((mapget_1244 = 25) /\ (unnamed_1248 = 4))) -> imapget_1249 >= 24;
constraint (((mapget_1244 = 25) /\ (unnamed_1248 = 5))) -> imapget_1249 >= 25;
constraint (((mapget_1244 = 25) /\ (unnamed_1248 = 6))) -> imapget_1249 >= 26;
constraint (((mapget_1244 = 25) /\ (unnamed_1248 = 7))) -> imapget_1249 >= 27;
constraint (((mapget_1244 = 25) /\ (unnamed_1248 = 8))) -> imapget_1249 >= 28;
constraint (((mapget_1244 = 25) /\ (unnamed_1248 = 9))) -> imapget_1249 >= 29;
constraint (((mapget_1244 = 25) /\ (unnamed_1248 = 10))) -> imapget_1249 >= 30;
constraint (((mapget_1244 = 27) /\ (unnamed_1248 = 1))) -> imapget_1249 >= 31;
constraint (((mapget_1244 = 27) /\ (unnamed_1248 = 2))) -> imapget_1249 >= 32;
constraint (((mapget_1244 = 27) /\ (unnamed_1248 = 3))) -> imapget_1249 >= 33;
constraint (((mapget_1244 = 27) /\ (unnamed_1248 = 4))) -> imapget_1249 >= 34;
constraint (((mapget_1244 = 27) /\ (unnamed_1248 = 5))) -> imapget_1249 >= 35;
constraint (((mapget_1244 = 27) /\ (unnamed_1248 = 6))) -> imapget_1249 >= 36;
constraint (((mapget_1244 = 27) /\ (unnamed_1248 = 7))) -> imapget_1249 >= 37;
constraint (((mapget_1244 = 27) /\ (unnamed_1248 = 8))) -> imapget_1249 >= 38;
constraint (((mapget_1244 = 27) /\ (unnamed_1248 = 9))) -> imapget_1249 >= 39;
constraint (((mapget_1244 = 27) /\ (unnamed_1248 = 10))) -> imapget_1249 >= 40;
constraint (((mapget_1244 = 28) /\ (unnamed_1248 = 1))) -> imapget_1249 >= 41;
constraint (((mapget_1244 = 28) /\ (unnamed_1248 = 2))) -> imapget_1249 >= 42;
constraint (((mapget_1244 = 28) /\ (unnamed_1248 = 3))) -> imapget_1249 >= 43;
constraint (((mapget_1244 = 28) /\ (unnamed_1248 = 4))) -> imapget_1249 >= 44;
constraint (((mapget_1244 = 28) /\ (unnamed_1248 = 5))) -> imapget_1249 >= 45;
constraint (((mapget_1244 = 28) /\ (unnamed_1248 = 6))) -> imapget_1249 >= 46;
constraint (((mapget_1244 = 28) /\ (unnamed_1248 = 7))) -> imapget_1249 >= 47;
constraint (((mapget_1244 = 28) /\ (unnamed_1248 = 8))) -> imapget_1249 >= 48;
constraint (((mapget_1244 = 28) /\ (unnamed_1248 = 9))) -> imapget_1249 >= 49;
constraint (((mapget_1244 = 28) /\ (unnamed_1248 = 10))) -> imapget_1249 >= 50;
constraint (((mapget_1244 = 29) /\ (unnamed_1248 = 1))) -> imapget_1249 >= 51;
constraint (((mapget_1244 = 29) /\ (unnamed_1248 = 2))) -> imapget_1249 >= 52;
constraint (((mapget_1244 = 29) /\ (unnamed_1248 = 3))) -> imapget_1249 >= 53;
constraint (((mapget_1244 = 29) /\ (unnamed_1248 = 4))) -> imapget_1249 >= 54;
constraint (((mapget_1244 = 29) /\ (unnamed_1248 = 5))) -> imapget_1249 >= 55;
constraint (((mapget_1244 = 29) /\ (unnamed_1248 = 6))) -> imapget_1249 >= 56;
constraint (((mapget_1244 = 29) /\ (unnamed_1248 = 7))) -> imapget_1249 >= 57;
constraint (((mapget_1244 = 29) /\ (unnamed_1248 = 8))) -> imapget_1249 >= 58;
constraint (((mapget_1244 = 29) /\ (unnamed_1248 = 9))) -> imapget_1249 >= 59;
constraint (((mapget_1244 = 29) /\ (unnamed_1248 = 10))) -> imapget_1249 >= 60;
constraint (((mapget_1244 = 30) /\ (unnamed_1248 = 1))) -> imapget_1249 >= 61;
constraint (((mapget_1244 = 30) /\ (unnamed_1248 = 2))) -> imapget_1249 >= 62;
constraint (((mapget_1244 = 30) /\ (unnamed_1248 = 3))) -> imapget_1249 >= 63;
constraint (((mapget_1244 = 30) /\ (unnamed_1248 = 4))) -> imapget_1249 >= 64;
constraint (((mapget_1244 = 30) /\ (unnamed_1248 = 5))) -> imapget_1249 >= 65;
constraint (((mapget_1244 = 30) /\ (unnamed_1248 = 6))) -> imapget_1249 >= 66;
constraint (((mapget_1244 = 30) /\ (unnamed_1248 = 7))) -> imapget_1249 >= 67;
constraint (((mapget_1244 = 30) /\ (unnamed_1248 = 8))) -> imapget_1249 >= 68;
constraint (((mapget_1244 = 30) /\ (unnamed_1248 = 9))) -> imapget_1249 >= 69;
constraint (((mapget_1244 = 30) /\ (unnamed_1248 = 10))) -> imapget_1249 >= 70;
constraint (((mapget_1244 = 32) /\ (unnamed_1248 = 1))) -> imapget_1249 >= 71;
constraint (((mapget_1244 = 32) /\ (unnamed_1248 = 2))) -> imapget_1249 >= 72;
constraint (((mapget_1244 = 32) /\ (unnamed_1248 = 3))) -> imapget_1249 >= 73;
constraint (((mapget_1244 = 32) /\ (unnamed_1248 = 4))) -> imapget_1249 >= 74;
constraint (((mapget_1244 = 32) /\ (unnamed_1248 = 5))) -> imapget_1249 >= 75;
constraint (((mapget_1244 = 32) /\ (unnamed_1248 = 6))) -> imapget_1249 >= 76;
constraint (((mapget_1244 = 32) /\ (unnamed_1248 = 7))) -> imapget_1249 >= 77;
constraint (((mapget_1244 = 32) /\ (unnamed_1248 = 8))) -> imapget_1249 >= 78;
constraint (((mapget_1244 = 32) /\ (unnamed_1248 = 9))) -> imapget_1249 >= 79;
constraint (((mapget_1244 = 32) /\ (unnamed_1248 = 10))) -> imapget_1249 >= 80;
constraint (((mapget_1244 = 33) /\ (unnamed_1248 = 1))) -> imapget_1249 >= 81;
constraint (((mapget_1244 = 33) /\ (unnamed_1248 = 2))) -> imapget_1249 >= 82;
constraint (((mapget_1244 = 33) /\ (unnamed_1248 = 3))) -> imapget_1249 >= 83;
constraint (((mapget_1244 = 33) /\ (unnamed_1248 = 4))) -> imapget_1249 >= 84;
constraint (((mapget_1244 = 33) /\ (unnamed_1248 = 5))) -> imapget_1249 >= 85;
constraint (((mapget_1244 = 33) /\ (unnamed_1248 = 6))) -> imapget_1249 >= 86;
constraint (((mapget_1244 = 33) /\ (unnamed_1248 = 7))) -> imapget_1249 >= 87;
constraint (((mapget_1244 = 33) /\ (unnamed_1248 = 8))) -> imapget_1249 >= 88;
constraint (((mapget_1244 = 33) /\ (unnamed_1248 = 9))) -> imapget_1249 >= 89;
constraint (((mapget_1244 = 33) /\ (unnamed_1248 = 10))) -> imapget_1249 >= 90;
constraint (((mapget_1244 = 34) /\ (unnamed_1248 = 1))) -> imapget_1249 >= 91;
constraint (((mapget_1244 = 34) /\ (unnamed_1248 = 2))) -> imapget_1249 >= 92;
constraint (((mapget_1244 = 34) /\ (unnamed_1248 = 3))) -> imapget_1249 >= 93;
constraint (((mapget_1244 = 34) /\ (unnamed_1248 = 4))) -> imapget_1249 >= 94;
constraint (((mapget_1244 = 34) /\ (unnamed_1248 = 5))) -> imapget_1249 >= 95;
constraint (((mapget_1244 = 34) /\ (unnamed_1248 = 6))) -> imapget_1249 >= 96;
constraint (((mapget_1244 = 34) /\ (unnamed_1248 = 7))) -> imapget_1249 >= 97;
constraint (((mapget_1244 = 34) /\ (unnamed_1248 = 8))) -> imapget_1249 >= 98;
constraint (((mapget_1244 = 34) /\ (unnamed_1248 = 9))) -> imapget_1249 >= 99;
constraint (((mapget_1244 = 34) /\ (unnamed_1248 = 10))) -> imapget_1249 >= 100;
constraint mapget_1249 = [0, 15, 16, 16, 6, 8, 8, 3, 4, 17, 15, 0, 11, 18, 10, 12, 18, 4, 11, 7, 16, 11, 0, 13, 13, 12, 8, 1, 14, 5, 16, 18, 13, 0, 12, 16, 6, 5, 15, 12, 6, 10, 13, 12, 0, 2, 8, 19, 9, 5, 8, 12, 12, 16, 2, 0, 11, 14, 16, 8, 8, 18, 8, 6, 8, 11, 0, 11, 20, 19, 3, 4, 1, 5, 19, 14, 11, 0, 7, 2, 4, 11, 14, 15, 9, 16, 20, 7, 0, 12, 17, 7, 5, 12, 5, 8, 19, 2, 12, 0, 20][imapget_1249];

var 0..20: ret_travelTime_1253; %ref (Literal: 0 [0]).ret_travelTime -26
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_travelTime -26
var 1..1: iret_travelTime_1253;
constraint ret_travelTime_1253 = [mapget_1249, 20][iret_travelTime_1253];

var 2..139: Add_1254 = (currentTime_1229 + ret_travelTime_1253);

var 1..10: nextLocation_1256; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_1256;
constraint nextLocation_1256 = [ret_getLocation_1226, 10][inextLocation_1256];

var {36,39,42,45,48,51,54,57,60,63}: listget_1269; %optimise.state.ListGet@4f5
constraint listget_1269 = chooseOrderVal_2[8];

var {36,39,42,45,48,51,54,57,60,63}: stop_1281; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_1281;
constraint stop_1281 = [listget_1269, 63][istop_1281];

var 1..10: locationID_1287; %ref ref (Literal: 0 [0]).stop -21.locationID -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).stop -21.locationID -7
var 1..10: ilocationID_1287;
constraint [36, 39, 42, 45, 48, 51, 54, 57, 60, 63, stop_1281][ilocationID_1287] = stop_1281;
constraint ((stop_1281 = 36)) -> ilocationID_1287 >= 1;
constraint ((stop_1281 = 39)) -> ilocationID_1287 >= 2;
constraint ((stop_1281 = 42)) -> ilocationID_1287 >= 3;
constraint ((stop_1281 = 45)) -> ilocationID_1287 >= 4;
constraint ((stop_1281 = 48)) -> ilocationID_1287 >= 5;
constraint ((stop_1281 = 51)) -> ilocationID_1287 >= 6;
constraint ((stop_1281 = 54)) -> ilocationID_1287 >= 7;
constraint ((stop_1281 = 57)) -> ilocationID_1287 >= 8;
constraint ((stop_1281 = 60)) -> ilocationID_1287 >= 9;
constraint ((stop_1281 = 63)) -> ilocationID_1287 >= 10;
constraint locationID_1287 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10][ilocationID_1287];

var 1..10: ret_getLocation_1291; %ref (Literal: 0 [0]).ret_getLocation -22
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getLocation -22
var 1..1: iret_getLocation_1291;
constraint ret_getLocation_1291 = [locationID_1287, 10][iret_getLocation_1291];

var 2..139: currentTime_1294; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_1294;
constraint currentTime_1294 = [Add_1254, 139][icurrentTime_1294];

var 1..10: currentLocation_1295; %ref (Literal: 0 [0]).currentLocation -19
% doing constraints for lookup query: ref (Literal: 0 [0]).currentLocation -19
var 1..1: icurrentLocation_1295;
constraint currentLocation_1295 = [nextLocation_1256, 10][icurrentLocation_1295];

var 1..10: nextLocation_1298; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_1298;
constraint nextLocation_1298 = [ret_getLocation_1291, 10][inextLocation_1298];

var 1..10: location1_1305; %ref (Literal: 0 [0]).location1 -24
% doing constraints for lookup query: ref (Literal: 0 [0]).location1 -24
var 1..1: ilocation1_1305;
constraint location1_1305 = [currentLocation_1295, 10][ilocation1_1305];

var 1..10: unnamed_1308; %ref (Literal: 0 [0]).unnamed -27
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -27
var 1..1: iunnamed_1308;
constraint unnamed_1308 = [location1_1305, 10][iunnamed_1308];

var {20,24,25,27,28,29,30,32,33,34}: mapget_1309; %optimise.state.MapGet@51d
% doing constraints for lookup query: optimise.state.MapGet@51d
var 1..10: imapget_1309;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_1308][imapget_1309] = unnamed_1308;
constraint ((unnamed_1308 = 1)) -> imapget_1309 >= 1;
constraint ((unnamed_1308 = 2)) -> imapget_1309 >= 2;
constraint ((unnamed_1308 = 3)) -> imapget_1309 >= 3;
constraint ((unnamed_1308 = 4)) -> imapget_1309 >= 4;
constraint ((unnamed_1308 = 5)) -> imapget_1309 >= 5;
constraint ((unnamed_1308 = 6)) -> imapget_1309 >= 6;
constraint ((unnamed_1308 = 7)) -> imapget_1309 >= 7;
constraint ((unnamed_1308 = 8)) -> imapget_1309 >= 8;
constraint ((unnamed_1308 = 9)) -> imapget_1309 >= 9;
constraint ((unnamed_1308 = 10)) -> imapget_1309 >= 10;
constraint mapget_1309 = [20, 24, 25, 27, 28, 29, 30, 32, 33, 34, 34][imapget_1309];

var 1..10: location2_1310; %ref (Literal: 0 [0]).location2 -25
% doing constraints for lookup query: ref (Literal: 0 [0]).location2 -25
var 1..1: ilocation2_1310;
constraint location2_1310 = [nextLocation_1298, 10][ilocation2_1310];

var 1..10: unnamed_1313; %ref (Literal: 0 [0]).unnamed -28
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -28
var 1..1: iunnamed_1313;
constraint unnamed_1313 = [location2_1310, 10][iunnamed_1313];

var 0..20: mapget_1314; %optimise.state.MapGet@522
% doing constraints for lookup query: optimise.state.MapGet@522
var 1..100: imapget_1314;
constraint [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, mapget_1309][imapget_1314] = mapget_1309;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_1313][imapget_1314] = unnamed_1313;
constraint (((mapget_1309 = 20) /\ (unnamed_1313 = 1))) -> imapget_1314 >= 1;
constraint (((mapget_1309 = 20) /\ (unnamed_1313 = 2))) -> imapget_1314 >= 2;
constraint (((mapget_1309 = 20) /\ (unnamed_1313 = 3))) -> imapget_1314 >= 3;
constraint (((mapget_1309 = 20) /\ (unnamed_1313 = 4))) -> imapget_1314 >= 4;
constraint (((mapget_1309 = 20) /\ (unnamed_1313 = 5))) -> imapget_1314 >= 5;
constraint (((mapget_1309 = 20) /\ (unnamed_1313 = 6))) -> imapget_1314 >= 6;
constraint (((mapget_1309 = 20) /\ (unnamed_1313 = 7))) -> imapget_1314 >= 7;
constraint (((mapget_1309 = 20) /\ (unnamed_1313 = 8))) -> imapget_1314 >= 8;
constraint (((mapget_1309 = 20) /\ (unnamed_1313 = 9))) -> imapget_1314 >= 9;
constraint (((mapget_1309 = 20) /\ (unnamed_1313 = 10))) -> imapget_1314 >= 10;
constraint (((mapget_1309 = 24) /\ (unnamed_1313 = 1))) -> imapget_1314 >= 11;
constraint (((mapget_1309 = 24) /\ (unnamed_1313 = 2))) -> imapget_1314 >= 12;
constraint (((mapget_1309 = 24) /\ (unnamed_1313 = 3))) -> imapget_1314 >= 13;
constraint (((mapget_1309 = 24) /\ (unnamed_1313 = 4))) -> imapget_1314 >= 14;
constraint (((mapget_1309 = 24) /\ (unnamed_1313 = 5))) -> imapget_1314 >= 15;
constraint (((mapget_1309 = 24) /\ (unnamed_1313 = 6))) -> imapget_1314 >= 16;
constraint (((mapget_1309 = 24) /\ (unnamed_1313 = 7))) -> imapget_1314 >= 17;
constraint (((mapget_1309 = 24) /\ (unnamed_1313 = 8))) -> imapget_1314 >= 18;
constraint (((mapget_1309 = 24) /\ (unnamed_1313 = 9))) -> imapget_1314 >= 19;
constraint (((mapget_1309 = 24) /\ (unnamed_1313 = 10))) -> imapget_1314 >= 20;
constraint (((mapget_1309 = 25) /\ (unnamed_1313 = 1))) -> imapget_1314 >= 21;
constraint (((mapget_1309 = 25) /\ (unnamed_1313 = 2))) -> imapget_1314 >= 22;
constraint (((mapget_1309 = 25) /\ (unnamed_1313 = 3))) -> imapget_1314 >= 23;
constraint (((mapget_1309 = 25) /\ (unnamed_1313 = 4))) -> imapget_1314 >= 24;
constraint (((mapget_1309 = 25) /\ (unnamed_1313 = 5))) -> imapget_1314 >= 25;
constraint (((mapget_1309 = 25) /\ (unnamed_1313 = 6))) -> imapget_1314 >= 26;
constraint (((mapget_1309 = 25) /\ (unnamed_1313 = 7))) -> imapget_1314 >= 27;
constraint (((mapget_1309 = 25) /\ (unnamed_1313 = 8))) -> imapget_1314 >= 28;
constraint (((mapget_1309 = 25) /\ (unnamed_1313 = 9))) -> imapget_1314 >= 29;
constraint (((mapget_1309 = 25) /\ (unnamed_1313 = 10))) -> imapget_1314 >= 30;
constraint (((mapget_1309 = 27) /\ (unnamed_1313 = 1))) -> imapget_1314 >= 31;
constraint (((mapget_1309 = 27) /\ (unnamed_1313 = 2))) -> imapget_1314 >= 32;
constraint (((mapget_1309 = 27) /\ (unnamed_1313 = 3))) -> imapget_1314 >= 33;
constraint (((mapget_1309 = 27) /\ (unnamed_1313 = 4))) -> imapget_1314 >= 34;
constraint (((mapget_1309 = 27) /\ (unnamed_1313 = 5))) -> imapget_1314 >= 35;
constraint (((mapget_1309 = 27) /\ (unnamed_1313 = 6))) -> imapget_1314 >= 36;
constraint (((mapget_1309 = 27) /\ (unnamed_1313 = 7))) -> imapget_1314 >= 37;
constraint (((mapget_1309 = 27) /\ (unnamed_1313 = 8))) -> imapget_1314 >= 38;
constraint (((mapget_1309 = 27) /\ (unnamed_1313 = 9))) -> imapget_1314 >= 39;
constraint (((mapget_1309 = 27) /\ (unnamed_1313 = 10))) -> imapget_1314 >= 40;
constraint (((mapget_1309 = 28) /\ (unnamed_1313 = 1))) -> imapget_1314 >= 41;
constraint (((mapget_1309 = 28) /\ (unnamed_1313 = 2))) -> imapget_1314 >= 42;
constraint (((mapget_1309 = 28) /\ (unnamed_1313 = 3))) -> imapget_1314 >= 43;
constraint (((mapget_1309 = 28) /\ (unnamed_1313 = 4))) -> imapget_1314 >= 44;
constraint (((mapget_1309 = 28) /\ (unnamed_1313 = 5))) -> imapget_1314 >= 45;
constraint (((mapget_1309 = 28) /\ (unnamed_1313 = 6))) -> imapget_1314 >= 46;
constraint (((mapget_1309 = 28) /\ (unnamed_1313 = 7))) -> imapget_1314 >= 47;
constraint (((mapget_1309 = 28) /\ (unnamed_1313 = 8))) -> imapget_1314 >= 48;
constraint (((mapget_1309 = 28) /\ (unnamed_1313 = 9))) -> imapget_1314 >= 49;
constraint (((mapget_1309 = 28) /\ (unnamed_1313 = 10))) -> imapget_1314 >= 50;
constraint (((mapget_1309 = 29) /\ (unnamed_1313 = 1))) -> imapget_1314 >= 51;
constraint (((mapget_1309 = 29) /\ (unnamed_1313 = 2))) -> imapget_1314 >= 52;
constraint (((mapget_1309 = 29) /\ (unnamed_1313 = 3))) -> imapget_1314 >= 53;
constraint (((mapget_1309 = 29) /\ (unnamed_1313 = 4))) -> imapget_1314 >= 54;
constraint (((mapget_1309 = 29) /\ (unnamed_1313 = 5))) -> imapget_1314 >= 55;
constraint (((mapget_1309 = 29) /\ (unnamed_1313 = 6))) -> imapget_1314 >= 56;
constraint (((mapget_1309 = 29) /\ (unnamed_1313 = 7))) -> imapget_1314 >= 57;
constraint (((mapget_1309 = 29) /\ (unnamed_1313 = 8))) -> imapget_1314 >= 58;
constraint (((mapget_1309 = 29) /\ (unnamed_1313 = 9))) -> imapget_1314 >= 59;
constraint (((mapget_1309 = 29) /\ (unnamed_1313 = 10))) -> imapget_1314 >= 60;
constraint (((mapget_1309 = 30) /\ (unnamed_1313 = 1))) -> imapget_1314 >= 61;
constraint (((mapget_1309 = 30) /\ (unnamed_1313 = 2))) -> imapget_1314 >= 62;
constraint (((mapget_1309 = 30) /\ (unnamed_1313 = 3))) -> imapget_1314 >= 63;
constraint (((mapget_1309 = 30) /\ (unnamed_1313 = 4))) -> imapget_1314 >= 64;
constraint (((mapget_1309 = 30) /\ (unnamed_1313 = 5))) -> imapget_1314 >= 65;
constraint (((mapget_1309 = 30) /\ (unnamed_1313 = 6))) -> imapget_1314 >= 66;
constraint (((mapget_1309 = 30) /\ (unnamed_1313 = 7))) -> imapget_1314 >= 67;
constraint (((mapget_1309 = 30) /\ (unnamed_1313 = 8))) -> imapget_1314 >= 68;
constraint (((mapget_1309 = 30) /\ (unnamed_1313 = 9))) -> imapget_1314 >= 69;
constraint (((mapget_1309 = 30) /\ (unnamed_1313 = 10))) -> imapget_1314 >= 70;
constraint (((mapget_1309 = 32) /\ (unnamed_1313 = 1))) -> imapget_1314 >= 71;
constraint (((mapget_1309 = 32) /\ (unnamed_1313 = 2))) -> imapget_1314 >= 72;
constraint (((mapget_1309 = 32) /\ (unnamed_1313 = 3))) -> imapget_1314 >= 73;
constraint (((mapget_1309 = 32) /\ (unnamed_1313 = 4))) -> imapget_1314 >= 74;
constraint (((mapget_1309 = 32) /\ (unnamed_1313 = 5))) -> imapget_1314 >= 75;
constraint (((mapget_1309 = 32) /\ (unnamed_1313 = 6))) -> imapget_1314 >= 76;
constraint (((mapget_1309 = 32) /\ (unnamed_1313 = 7))) -> imapget_1314 >= 77;
constraint (((mapget_1309 = 32) /\ (unnamed_1313 = 8))) -> imapget_1314 >= 78;
constraint (((mapget_1309 = 32) /\ (unnamed_1313 = 9))) -> imapget_1314 >= 79;
constraint (((mapget_1309 = 32) /\ (unnamed_1313 = 10))) -> imapget_1314 >= 80;
constraint (((mapget_1309 = 33) /\ (unnamed_1313 = 1))) -> imapget_1314 >= 81;
constraint (((mapget_1309 = 33) /\ (unnamed_1313 = 2))) -> imapget_1314 >= 82;
constraint (((mapget_1309 = 33) /\ (unnamed_1313 = 3))) -> imapget_1314 >= 83;
constraint (((mapget_1309 = 33) /\ (unnamed_1313 = 4))) -> imapget_1314 >= 84;
constraint (((mapget_1309 = 33) /\ (unnamed_1313 = 5))) -> imapget_1314 >= 85;
constraint (((mapget_1309 = 33) /\ (unnamed_1313 = 6))) -> imapget_1314 >= 86;
constraint (((mapget_1309 = 33) /\ (unnamed_1313 = 7))) -> imapget_1314 >= 87;
constraint (((mapget_1309 = 33) /\ (unnamed_1313 = 8))) -> imapget_1314 >= 88;
constraint (((mapget_1309 = 33) /\ (unnamed_1313 = 9))) -> imapget_1314 >= 89;
constraint (((mapget_1309 = 33) /\ (unnamed_1313 = 10))) -> imapget_1314 >= 90;
constraint (((mapget_1309 = 34) /\ (unnamed_1313 = 1))) -> imapget_1314 >= 91;
constraint (((mapget_1309 = 34) /\ (unnamed_1313 = 2))) -> imapget_1314 >= 92;
constraint (((mapget_1309 = 34) /\ (unnamed_1313 = 3))) -> imapget_1314 >= 93;
constraint (((mapget_1309 = 34) /\ (unnamed_1313 = 4))) -> imapget_1314 >= 94;
constraint (((mapget_1309 = 34) /\ (unnamed_1313 = 5))) -> imapget_1314 >= 95;
constraint (((mapget_1309 = 34) /\ (unnamed_1313 = 6))) -> imapget_1314 >= 96;
constraint (((mapget_1309 = 34) /\ (unnamed_1313 = 7))) -> imapget_1314 >= 97;
constraint (((mapget_1309 = 34) /\ (unnamed_1313 = 8))) -> imapget_1314 >= 98;
constraint (((mapget_1309 = 34) /\ (unnamed_1313 = 9))) -> imapget_1314 >= 99;
constraint (((mapget_1309 = 34) /\ (unnamed_1313 = 10))) -> imapget_1314 >= 100;
constraint mapget_1314 = [0, 15, 16, 16, 6, 8, 8, 3, 4, 17, 15, 0, 11, 18, 10, 12, 18, 4, 11, 7, 16, 11, 0, 13, 13, 12, 8, 1, 14, 5, 16, 18, 13, 0, 12, 16, 6, 5, 15, 12, 6, 10, 13, 12, 0, 2, 8, 19, 9, 5, 8, 12, 12, 16, 2, 0, 11, 14, 16, 8, 8, 18, 8, 6, 8, 11, 0, 11, 20, 19, 3, 4, 1, 5, 19, 14, 11, 0, 7, 2, 4, 11, 14, 15, 9, 16, 20, 7, 0, 12, 17, 7, 5, 12, 5, 8, 19, 2, 12, 0, 20][imapget_1314];

var 0..20: ret_travelTime_1318; %ref (Literal: 0 [0]).ret_travelTime -26
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_travelTime -26
var 1..1: iret_travelTime_1318;
constraint ret_travelTime_1318 = [mapget_1314, 20][iret_travelTime_1318];

var 2..159: Add_1319 = (currentTime_1294 + ret_travelTime_1318);

var 1..10: nextLocation_1321; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_1321;
constraint nextLocation_1321 = [ret_getLocation_1291, 10][inextLocation_1321];

var {36,39,42,45,48,51,54,57,60,63}: listget_1334; %optimise.state.ListGet@536
constraint listget_1334 = chooseOrderVal_2[9];

var {36,39,42,45,48,51,54,57,60,63}: stop_1346; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_1346;
constraint stop_1346 = [listget_1334, 63][istop_1346];

var 1..10: locationID_1352; %ref ref (Literal: 0 [0]).stop -21.locationID -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).stop -21.locationID -7
var 1..10: ilocationID_1352;
constraint [36, 39, 42, 45, 48, 51, 54, 57, 60, 63, stop_1346][ilocationID_1352] = stop_1346;
constraint ((stop_1346 = 36)) -> ilocationID_1352 >= 1;
constraint ((stop_1346 = 39)) -> ilocationID_1352 >= 2;
constraint ((stop_1346 = 42)) -> ilocationID_1352 >= 3;
constraint ((stop_1346 = 45)) -> ilocationID_1352 >= 4;
constraint ((stop_1346 = 48)) -> ilocationID_1352 >= 5;
constraint ((stop_1346 = 51)) -> ilocationID_1352 >= 6;
constraint ((stop_1346 = 54)) -> ilocationID_1352 >= 7;
constraint ((stop_1346 = 57)) -> ilocationID_1352 >= 8;
constraint ((stop_1346 = 60)) -> ilocationID_1352 >= 9;
constraint ((stop_1346 = 63)) -> ilocationID_1352 >= 10;
constraint locationID_1352 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10][ilocationID_1352];

var 1..10: ret_getLocation_1356; %ref (Literal: 0 [0]).ret_getLocation -22
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getLocation -22
var 1..1: iret_getLocation_1356;
constraint ret_getLocation_1356 = [locationID_1352, 10][iret_getLocation_1356];

var 2..159: currentTime_1359; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_1359;
constraint currentTime_1359 = [Add_1319, 159][icurrentTime_1359];

var 1..10: currentLocation_1360; %ref (Literal: 0 [0]).currentLocation -19
% doing constraints for lookup query: ref (Literal: 0 [0]).currentLocation -19
var 1..1: icurrentLocation_1360;
constraint currentLocation_1360 = [nextLocation_1321, 10][icurrentLocation_1360];

var 1..10: nextLocation_1363; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_1363;
constraint nextLocation_1363 = [ret_getLocation_1356, 10][inextLocation_1363];

var 1..10: location1_1370; %ref (Literal: 0 [0]).location1 -24
% doing constraints for lookup query: ref (Literal: 0 [0]).location1 -24
var 1..1: ilocation1_1370;
constraint location1_1370 = [currentLocation_1360, 10][ilocation1_1370];

var 1..10: unnamed_1373; %ref (Literal: 0 [0]).unnamed -27
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -27
var 1..1: iunnamed_1373;
constraint unnamed_1373 = [location1_1370, 10][iunnamed_1373];

var {20,24,25,27,28,29,30,32,33,34}: mapget_1374; %optimise.state.MapGet@55e
% doing constraints for lookup query: optimise.state.MapGet@55e
var 1..10: imapget_1374;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_1373][imapget_1374] = unnamed_1373;
constraint ((unnamed_1373 = 1)) -> imapget_1374 >= 1;
constraint ((unnamed_1373 = 2)) -> imapget_1374 >= 2;
constraint ((unnamed_1373 = 3)) -> imapget_1374 >= 3;
constraint ((unnamed_1373 = 4)) -> imapget_1374 >= 4;
constraint ((unnamed_1373 = 5)) -> imapget_1374 >= 5;
constraint ((unnamed_1373 = 6)) -> imapget_1374 >= 6;
constraint ((unnamed_1373 = 7)) -> imapget_1374 >= 7;
constraint ((unnamed_1373 = 8)) -> imapget_1374 >= 8;
constraint ((unnamed_1373 = 9)) -> imapget_1374 >= 9;
constraint ((unnamed_1373 = 10)) -> imapget_1374 >= 10;
constraint mapget_1374 = [20, 24, 25, 27, 28, 29, 30, 32, 33, 34, 34][imapget_1374];

var 1..10: location2_1375; %ref (Literal: 0 [0]).location2 -25
% doing constraints for lookup query: ref (Literal: 0 [0]).location2 -25
var 1..1: ilocation2_1375;
constraint location2_1375 = [nextLocation_1363, 10][ilocation2_1375];

var 1..10: unnamed_1378; %ref (Literal: 0 [0]).unnamed -28
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -28
var 1..1: iunnamed_1378;
constraint unnamed_1378 = [location2_1375, 10][iunnamed_1378];

var 0..20: mapget_1379; %optimise.state.MapGet@563
% doing constraints for lookup query: optimise.state.MapGet@563
var 1..100: imapget_1379;
constraint [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, mapget_1374][imapget_1379] = mapget_1374;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_1378][imapget_1379] = unnamed_1378;
constraint (((mapget_1374 = 20) /\ (unnamed_1378 = 1))) -> imapget_1379 >= 1;
constraint (((mapget_1374 = 20) /\ (unnamed_1378 = 2))) -> imapget_1379 >= 2;
constraint (((mapget_1374 = 20) /\ (unnamed_1378 = 3))) -> imapget_1379 >= 3;
constraint (((mapget_1374 = 20) /\ (unnamed_1378 = 4))) -> imapget_1379 >= 4;
constraint (((mapget_1374 = 20) /\ (unnamed_1378 = 5))) -> imapget_1379 >= 5;
constraint (((mapget_1374 = 20) /\ (unnamed_1378 = 6))) -> imapget_1379 >= 6;
constraint (((mapget_1374 = 20) /\ (unnamed_1378 = 7))) -> imapget_1379 >= 7;
constraint (((mapget_1374 = 20) /\ (unnamed_1378 = 8))) -> imapget_1379 >= 8;
constraint (((mapget_1374 = 20) /\ (unnamed_1378 = 9))) -> imapget_1379 >= 9;
constraint (((mapget_1374 = 20) /\ (unnamed_1378 = 10))) -> imapget_1379 >= 10;
constraint (((mapget_1374 = 24) /\ (unnamed_1378 = 1))) -> imapget_1379 >= 11;
constraint (((mapget_1374 = 24) /\ (unnamed_1378 = 2))) -> imapget_1379 >= 12;
constraint (((mapget_1374 = 24) /\ (unnamed_1378 = 3))) -> imapget_1379 >= 13;
constraint (((mapget_1374 = 24) /\ (unnamed_1378 = 4))) -> imapget_1379 >= 14;
constraint (((mapget_1374 = 24) /\ (unnamed_1378 = 5))) -> imapget_1379 >= 15;
constraint (((mapget_1374 = 24) /\ (unnamed_1378 = 6))) -> imapget_1379 >= 16;
constraint (((mapget_1374 = 24) /\ (unnamed_1378 = 7))) -> imapget_1379 >= 17;
constraint (((mapget_1374 = 24) /\ (unnamed_1378 = 8))) -> imapget_1379 >= 18;
constraint (((mapget_1374 = 24) /\ (unnamed_1378 = 9))) -> imapget_1379 >= 19;
constraint (((mapget_1374 = 24) /\ (unnamed_1378 = 10))) -> imapget_1379 >= 20;
constraint (((mapget_1374 = 25) /\ (unnamed_1378 = 1))) -> imapget_1379 >= 21;
constraint (((mapget_1374 = 25) /\ (unnamed_1378 = 2))) -> imapget_1379 >= 22;
constraint (((mapget_1374 = 25) /\ (unnamed_1378 = 3))) -> imapget_1379 >= 23;
constraint (((mapget_1374 = 25) /\ (unnamed_1378 = 4))) -> imapget_1379 >= 24;
constraint (((mapget_1374 = 25) /\ (unnamed_1378 = 5))) -> imapget_1379 >= 25;
constraint (((mapget_1374 = 25) /\ (unnamed_1378 = 6))) -> imapget_1379 >= 26;
constraint (((mapget_1374 = 25) /\ (unnamed_1378 = 7))) -> imapget_1379 >= 27;
constraint (((mapget_1374 = 25) /\ (unnamed_1378 = 8))) -> imapget_1379 >= 28;
constraint (((mapget_1374 = 25) /\ (unnamed_1378 = 9))) -> imapget_1379 >= 29;
constraint (((mapget_1374 = 25) /\ (unnamed_1378 = 10))) -> imapget_1379 >= 30;
constraint (((mapget_1374 = 27) /\ (unnamed_1378 = 1))) -> imapget_1379 >= 31;
constraint (((mapget_1374 = 27) /\ (unnamed_1378 = 2))) -> imapget_1379 >= 32;
constraint (((mapget_1374 = 27) /\ (unnamed_1378 = 3))) -> imapget_1379 >= 33;
constraint (((mapget_1374 = 27) /\ (unnamed_1378 = 4))) -> imapget_1379 >= 34;
constraint (((mapget_1374 = 27) /\ (unnamed_1378 = 5))) -> imapget_1379 >= 35;
constraint (((mapget_1374 = 27) /\ (unnamed_1378 = 6))) -> imapget_1379 >= 36;
constraint (((mapget_1374 = 27) /\ (unnamed_1378 = 7))) -> imapget_1379 >= 37;
constraint (((mapget_1374 = 27) /\ (unnamed_1378 = 8))) -> imapget_1379 >= 38;
constraint (((mapget_1374 = 27) /\ (unnamed_1378 = 9))) -> imapget_1379 >= 39;
constraint (((mapget_1374 = 27) /\ (unnamed_1378 = 10))) -> imapget_1379 >= 40;
constraint (((mapget_1374 = 28) /\ (unnamed_1378 = 1))) -> imapget_1379 >= 41;
constraint (((mapget_1374 = 28) /\ (unnamed_1378 = 2))) -> imapget_1379 >= 42;
constraint (((mapget_1374 = 28) /\ (unnamed_1378 = 3))) -> imapget_1379 >= 43;
constraint (((mapget_1374 = 28) /\ (unnamed_1378 = 4))) -> imapget_1379 >= 44;
constraint (((mapget_1374 = 28) /\ (unnamed_1378 = 5))) -> imapget_1379 >= 45;
constraint (((mapget_1374 = 28) /\ (unnamed_1378 = 6))) -> imapget_1379 >= 46;
constraint (((mapget_1374 = 28) /\ (unnamed_1378 = 7))) -> imapget_1379 >= 47;
constraint (((mapget_1374 = 28) /\ (unnamed_1378 = 8))) -> imapget_1379 >= 48;
constraint (((mapget_1374 = 28) /\ (unnamed_1378 = 9))) -> imapget_1379 >= 49;
constraint (((mapget_1374 = 28) /\ (unnamed_1378 = 10))) -> imapget_1379 >= 50;
constraint (((mapget_1374 = 29) /\ (unnamed_1378 = 1))) -> imapget_1379 >= 51;
constraint (((mapget_1374 = 29) /\ (unnamed_1378 = 2))) -> imapget_1379 >= 52;
constraint (((mapget_1374 = 29) /\ (unnamed_1378 = 3))) -> imapget_1379 >= 53;
constraint (((mapget_1374 = 29) /\ (unnamed_1378 = 4))) -> imapget_1379 >= 54;
constraint (((mapget_1374 = 29) /\ (unnamed_1378 = 5))) -> imapget_1379 >= 55;
constraint (((mapget_1374 = 29) /\ (unnamed_1378 = 6))) -> imapget_1379 >= 56;
constraint (((mapget_1374 = 29) /\ (unnamed_1378 = 7))) -> imapget_1379 >= 57;
constraint (((mapget_1374 = 29) /\ (unnamed_1378 = 8))) -> imapget_1379 >= 58;
constraint (((mapget_1374 = 29) /\ (unnamed_1378 = 9))) -> imapget_1379 >= 59;
constraint (((mapget_1374 = 29) /\ (unnamed_1378 = 10))) -> imapget_1379 >= 60;
constraint (((mapget_1374 = 30) /\ (unnamed_1378 = 1))) -> imapget_1379 >= 61;
constraint (((mapget_1374 = 30) /\ (unnamed_1378 = 2))) -> imapget_1379 >= 62;
constraint (((mapget_1374 = 30) /\ (unnamed_1378 = 3))) -> imapget_1379 >= 63;
constraint (((mapget_1374 = 30) /\ (unnamed_1378 = 4))) -> imapget_1379 >= 64;
constraint (((mapget_1374 = 30) /\ (unnamed_1378 = 5))) -> imapget_1379 >= 65;
constraint (((mapget_1374 = 30) /\ (unnamed_1378 = 6))) -> imapget_1379 >= 66;
constraint (((mapget_1374 = 30) /\ (unnamed_1378 = 7))) -> imapget_1379 >= 67;
constraint (((mapget_1374 = 30) /\ (unnamed_1378 = 8))) -> imapget_1379 >= 68;
constraint (((mapget_1374 = 30) /\ (unnamed_1378 = 9))) -> imapget_1379 >= 69;
constraint (((mapget_1374 = 30) /\ (unnamed_1378 = 10))) -> imapget_1379 >= 70;
constraint (((mapget_1374 = 32) /\ (unnamed_1378 = 1))) -> imapget_1379 >= 71;
constraint (((mapget_1374 = 32) /\ (unnamed_1378 = 2))) -> imapget_1379 >= 72;
constraint (((mapget_1374 = 32) /\ (unnamed_1378 = 3))) -> imapget_1379 >= 73;
constraint (((mapget_1374 = 32) /\ (unnamed_1378 = 4))) -> imapget_1379 >= 74;
constraint (((mapget_1374 = 32) /\ (unnamed_1378 = 5))) -> imapget_1379 >= 75;
constraint (((mapget_1374 = 32) /\ (unnamed_1378 = 6))) -> imapget_1379 >= 76;
constraint (((mapget_1374 = 32) /\ (unnamed_1378 = 7))) -> imapget_1379 >= 77;
constraint (((mapget_1374 = 32) /\ (unnamed_1378 = 8))) -> imapget_1379 >= 78;
constraint (((mapget_1374 = 32) /\ (unnamed_1378 = 9))) -> imapget_1379 >= 79;
constraint (((mapget_1374 = 32) /\ (unnamed_1378 = 10))) -> imapget_1379 >= 80;
constraint (((mapget_1374 = 33) /\ (unnamed_1378 = 1))) -> imapget_1379 >= 81;
constraint (((mapget_1374 = 33) /\ (unnamed_1378 = 2))) -> imapget_1379 >= 82;
constraint (((mapget_1374 = 33) /\ (unnamed_1378 = 3))) -> imapget_1379 >= 83;
constraint (((mapget_1374 = 33) /\ (unnamed_1378 = 4))) -> imapget_1379 >= 84;
constraint (((mapget_1374 = 33) /\ (unnamed_1378 = 5))) -> imapget_1379 >= 85;
constraint (((mapget_1374 = 33) /\ (unnamed_1378 = 6))) -> imapget_1379 >= 86;
constraint (((mapget_1374 = 33) /\ (unnamed_1378 = 7))) -> imapget_1379 >= 87;
constraint (((mapget_1374 = 33) /\ (unnamed_1378 = 8))) -> imapget_1379 >= 88;
constraint (((mapget_1374 = 33) /\ (unnamed_1378 = 9))) -> imapget_1379 >= 89;
constraint (((mapget_1374 = 33) /\ (unnamed_1378 = 10))) -> imapget_1379 >= 90;
constraint (((mapget_1374 = 34) /\ (unnamed_1378 = 1))) -> imapget_1379 >= 91;
constraint (((mapget_1374 = 34) /\ (unnamed_1378 = 2))) -> imapget_1379 >= 92;
constraint (((mapget_1374 = 34) /\ (unnamed_1378 = 3))) -> imapget_1379 >= 93;
constraint (((mapget_1374 = 34) /\ (unnamed_1378 = 4))) -> imapget_1379 >= 94;
constraint (((mapget_1374 = 34) /\ (unnamed_1378 = 5))) -> imapget_1379 >= 95;
constraint (((mapget_1374 = 34) /\ (unnamed_1378 = 6))) -> imapget_1379 >= 96;
constraint (((mapget_1374 = 34) /\ (unnamed_1378 = 7))) -> imapget_1379 >= 97;
constraint (((mapget_1374 = 34) /\ (unnamed_1378 = 8))) -> imapget_1379 >= 98;
constraint (((mapget_1374 = 34) /\ (unnamed_1378 = 9))) -> imapget_1379 >= 99;
constraint (((mapget_1374 = 34) /\ (unnamed_1378 = 10))) -> imapget_1379 >= 100;
constraint mapget_1379 = [0, 15, 16, 16, 6, 8, 8, 3, 4, 17, 15, 0, 11, 18, 10, 12, 18, 4, 11, 7, 16, 11, 0, 13, 13, 12, 8, 1, 14, 5, 16, 18, 13, 0, 12, 16, 6, 5, 15, 12, 6, 10, 13, 12, 0, 2, 8, 19, 9, 5, 8, 12, 12, 16, 2, 0, 11, 14, 16, 8, 8, 18, 8, 6, 8, 11, 0, 11, 20, 19, 3, 4, 1, 5, 19, 14, 11, 0, 7, 2, 4, 11, 14, 15, 9, 16, 20, 7, 0, 12, 17, 7, 5, 12, 5, 8, 19, 2, 12, 0, 20][imapget_1379];

var 0..20: ret_travelTime_1383; %ref (Literal: 0 [0]).ret_travelTime -26
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_travelTime -26
var 1..1: iret_travelTime_1383;
constraint ret_travelTime_1383 = [mapget_1379, 20][iret_travelTime_1383];

var 2..179: Add_1384 = (currentTime_1359 + ret_travelTime_1383);

var 1..10: nextLocation_1386; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_1386;
constraint nextLocation_1386 = [ret_getLocation_1356, 10][inextLocation_1386];

var {36,39,42,45,48,51,54,57,60,63}: listget_1399; %optimise.state.ListGet@577
constraint listget_1399 = chooseOrderVal_2[10];

var {36,39,42,45,48,51,54,57,60,63}: stop_1411; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_1411;
constraint stop_1411 = [listget_1399, 63][istop_1411];

var 1..10: locationID_1417; %ref ref (Literal: 0 [0]).stop -21.locationID -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).stop -21.locationID -7
var 1..10: ilocationID_1417;
constraint [36, 39, 42, 45, 48, 51, 54, 57, 60, 63, stop_1411][ilocationID_1417] = stop_1411;
constraint ((stop_1411 = 36)) -> ilocationID_1417 >= 1;
constraint ((stop_1411 = 39)) -> ilocationID_1417 >= 2;
constraint ((stop_1411 = 42)) -> ilocationID_1417 >= 3;
constraint ((stop_1411 = 45)) -> ilocationID_1417 >= 4;
constraint ((stop_1411 = 48)) -> ilocationID_1417 >= 5;
constraint ((stop_1411 = 51)) -> ilocationID_1417 >= 6;
constraint ((stop_1411 = 54)) -> ilocationID_1417 >= 7;
constraint ((stop_1411 = 57)) -> ilocationID_1417 >= 8;
constraint ((stop_1411 = 60)) -> ilocationID_1417 >= 9;
constraint ((stop_1411 = 63)) -> ilocationID_1417 >= 10;
constraint locationID_1417 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 10][ilocationID_1417];

var 1..10: ret_getLocation_1421; %ref (Literal: 0 [0]).ret_getLocation -22
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_getLocation -22
var 1..1: iret_getLocation_1421;
constraint ret_getLocation_1421 = [locationID_1417, 10][iret_getLocation_1421];

var 2..179: currentTime_1424; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_1424;
constraint currentTime_1424 = [Add_1384, 179][icurrentTime_1424];

var 1..10: currentLocation_1425; %ref (Literal: 0 [0]).currentLocation -19
% doing constraints for lookup query: ref (Literal: 0 [0]).currentLocation -19
var 1..1: icurrentLocation_1425;
constraint currentLocation_1425 = [nextLocation_1386, 10][icurrentLocation_1425];

var 1..10: nextLocation_1428; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_1428;
constraint nextLocation_1428 = [ret_getLocation_1421, 10][inextLocation_1428];

var 1..10: location1_1435; %ref (Literal: 0 [0]).location1 -24
% doing constraints for lookup query: ref (Literal: 0 [0]).location1 -24
var 1..1: ilocation1_1435;
constraint location1_1435 = [currentLocation_1425, 10][ilocation1_1435];

var 1..10: unnamed_1438; %ref (Literal: 0 [0]).unnamed -27
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -27
var 1..1: iunnamed_1438;
constraint unnamed_1438 = [location1_1435, 10][iunnamed_1438];

var {20,24,25,27,28,29,30,32,33,34}: mapget_1439; %optimise.state.MapGet@59f
% doing constraints for lookup query: optimise.state.MapGet@59f
var 1..10: imapget_1439;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_1438][imapget_1439] = unnamed_1438;
constraint ((unnamed_1438 = 1)) -> imapget_1439 >= 1;
constraint ((unnamed_1438 = 2)) -> imapget_1439 >= 2;
constraint ((unnamed_1438 = 3)) -> imapget_1439 >= 3;
constraint ((unnamed_1438 = 4)) -> imapget_1439 >= 4;
constraint ((unnamed_1438 = 5)) -> imapget_1439 >= 5;
constraint ((unnamed_1438 = 6)) -> imapget_1439 >= 6;
constraint ((unnamed_1438 = 7)) -> imapget_1439 >= 7;
constraint ((unnamed_1438 = 8)) -> imapget_1439 >= 8;
constraint ((unnamed_1438 = 9)) -> imapget_1439 >= 9;
constraint ((unnamed_1438 = 10)) -> imapget_1439 >= 10;
constraint mapget_1439 = [20, 24, 25, 27, 28, 29, 30, 32, 33, 34, 34][imapget_1439];

var 1..10: location2_1440; %ref (Literal: 0 [0]).location2 -25
% doing constraints for lookup query: ref (Literal: 0 [0]).location2 -25
var 1..1: ilocation2_1440;
constraint location2_1440 = [nextLocation_1428, 10][ilocation2_1440];

var 1..10: unnamed_1443; %ref (Literal: 0 [0]).unnamed -28
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -28
var 1..1: iunnamed_1443;
constraint unnamed_1443 = [location2_1440, 10][iunnamed_1443];

var 0..20: mapget_1444; %optimise.state.MapGet@5a4
% doing constraints for lookup query: optimise.state.MapGet@5a4
var 1..100: imapget_1444;
constraint [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 24, 24, 24, 24, 24, 24, 24, 24, 24, 24, 25, 25, 25, 25, 25, 25, 25, 25, 25, 25, 27, 27, 27, 27, 27, 27, 27, 27, 27, 27, 28, 28, 28, 28, 28, 28, 28, 28, 28, 28, 29, 29, 29, 29, 29, 29, 29, 29, 29, 29, 30, 30, 30, 30, 30, 30, 30, 30, 30, 30, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 33, 33, 33, 33, 33, 33, 33, 33, 33, 33, 34, 34, 34, 34, 34, 34, 34, 34, 34, 34, mapget_1439][imapget_1444] = mapget_1439;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_1443][imapget_1444] = unnamed_1443;
constraint (((mapget_1439 = 20) /\ (unnamed_1443 = 1))) -> imapget_1444 >= 1;
constraint (((mapget_1439 = 20) /\ (unnamed_1443 = 2))) -> imapget_1444 >= 2;
constraint (((mapget_1439 = 20) /\ (unnamed_1443 = 3))) -> imapget_1444 >= 3;
constraint (((mapget_1439 = 20) /\ (unnamed_1443 = 4))) -> imapget_1444 >= 4;
constraint (((mapget_1439 = 20) /\ (unnamed_1443 = 5))) -> imapget_1444 >= 5;
constraint (((mapget_1439 = 20) /\ (unnamed_1443 = 6))) -> imapget_1444 >= 6;
constraint (((mapget_1439 = 20) /\ (unnamed_1443 = 7))) -> imapget_1444 >= 7;
constraint (((mapget_1439 = 20) /\ (unnamed_1443 = 8))) -> imapget_1444 >= 8;
constraint (((mapget_1439 = 20) /\ (unnamed_1443 = 9))) -> imapget_1444 >= 9;
constraint (((mapget_1439 = 20) /\ (unnamed_1443 = 10))) -> imapget_1444 >= 10;
constraint (((mapget_1439 = 24) /\ (unnamed_1443 = 1))) -> imapget_1444 >= 11;
constraint (((mapget_1439 = 24) /\ (unnamed_1443 = 2))) -> imapget_1444 >= 12;
constraint (((mapget_1439 = 24) /\ (unnamed_1443 = 3))) -> imapget_1444 >= 13;
constraint (((mapget_1439 = 24) /\ (unnamed_1443 = 4))) -> imapget_1444 >= 14;
constraint (((mapget_1439 = 24) /\ (unnamed_1443 = 5))) -> imapget_1444 >= 15;
constraint (((mapget_1439 = 24) /\ (unnamed_1443 = 6))) -> imapget_1444 >= 16;
constraint (((mapget_1439 = 24) /\ (unnamed_1443 = 7))) -> imapget_1444 >= 17;
constraint (((mapget_1439 = 24) /\ (unnamed_1443 = 8))) -> imapget_1444 >= 18;
constraint (((mapget_1439 = 24) /\ (unnamed_1443 = 9))) -> imapget_1444 >= 19;
constraint (((mapget_1439 = 24) /\ (unnamed_1443 = 10))) -> imapget_1444 >= 20;
constraint (((mapget_1439 = 25) /\ (unnamed_1443 = 1))) -> imapget_1444 >= 21;
constraint (((mapget_1439 = 25) /\ (unnamed_1443 = 2))) -> imapget_1444 >= 22;
constraint (((mapget_1439 = 25) /\ (unnamed_1443 = 3))) -> imapget_1444 >= 23;
constraint (((mapget_1439 = 25) /\ (unnamed_1443 = 4))) -> imapget_1444 >= 24;
constraint (((mapget_1439 = 25) /\ (unnamed_1443 = 5))) -> imapget_1444 >= 25;
constraint (((mapget_1439 = 25) /\ (unnamed_1443 = 6))) -> imapget_1444 >= 26;
constraint (((mapget_1439 = 25) /\ (unnamed_1443 = 7))) -> imapget_1444 >= 27;
constraint (((mapget_1439 = 25) /\ (unnamed_1443 = 8))) -> imapget_1444 >= 28;
constraint (((mapget_1439 = 25) /\ (unnamed_1443 = 9))) -> imapget_1444 >= 29;
constraint (((mapget_1439 = 25) /\ (unnamed_1443 = 10))) -> imapget_1444 >= 30;
constraint (((mapget_1439 = 27) /\ (unnamed_1443 = 1))) -> imapget_1444 >= 31;
constraint (((mapget_1439 = 27) /\ (unnamed_1443 = 2))) -> imapget_1444 >= 32;
constraint (((mapget_1439 = 27) /\ (unnamed_1443 = 3))) -> imapget_1444 >= 33;
constraint (((mapget_1439 = 27) /\ (unnamed_1443 = 4))) -> imapget_1444 >= 34;
constraint (((mapget_1439 = 27) /\ (unnamed_1443 = 5))) -> imapget_1444 >= 35;
constraint (((mapget_1439 = 27) /\ (unnamed_1443 = 6))) -> imapget_1444 >= 36;
constraint (((mapget_1439 = 27) /\ (unnamed_1443 = 7))) -> imapget_1444 >= 37;
constraint (((mapget_1439 = 27) /\ (unnamed_1443 = 8))) -> imapget_1444 >= 38;
constraint (((mapget_1439 = 27) /\ (unnamed_1443 = 9))) -> imapget_1444 >= 39;
constraint (((mapget_1439 = 27) /\ (unnamed_1443 = 10))) -> imapget_1444 >= 40;
constraint (((mapget_1439 = 28) /\ (unnamed_1443 = 1))) -> imapget_1444 >= 41;
constraint (((mapget_1439 = 28) /\ (unnamed_1443 = 2))) -> imapget_1444 >= 42;
constraint (((mapget_1439 = 28) /\ (unnamed_1443 = 3))) -> imapget_1444 >= 43;
constraint (((mapget_1439 = 28) /\ (unnamed_1443 = 4))) -> imapget_1444 >= 44;
constraint (((mapget_1439 = 28) /\ (unnamed_1443 = 5))) -> imapget_1444 >= 45;
constraint (((mapget_1439 = 28) /\ (unnamed_1443 = 6))) -> imapget_1444 >= 46;
constraint (((mapget_1439 = 28) /\ (unnamed_1443 = 7))) -> imapget_1444 >= 47;
constraint (((mapget_1439 = 28) /\ (unnamed_1443 = 8))) -> imapget_1444 >= 48;
constraint (((mapget_1439 = 28) /\ (unnamed_1443 = 9))) -> imapget_1444 >= 49;
constraint (((mapget_1439 = 28) /\ (unnamed_1443 = 10))) -> imapget_1444 >= 50;
constraint (((mapget_1439 = 29) /\ (unnamed_1443 = 1))) -> imapget_1444 >= 51;
constraint (((mapget_1439 = 29) /\ (unnamed_1443 = 2))) -> imapget_1444 >= 52;
constraint (((mapget_1439 = 29) /\ (unnamed_1443 = 3))) -> imapget_1444 >= 53;
constraint (((mapget_1439 = 29) /\ (unnamed_1443 = 4))) -> imapget_1444 >= 54;
constraint (((mapget_1439 = 29) /\ (unnamed_1443 = 5))) -> imapget_1444 >= 55;
constraint (((mapget_1439 = 29) /\ (unnamed_1443 = 6))) -> imapget_1444 >= 56;
constraint (((mapget_1439 = 29) /\ (unnamed_1443 = 7))) -> imapget_1444 >= 57;
constraint (((mapget_1439 = 29) /\ (unnamed_1443 = 8))) -> imapget_1444 >= 58;
constraint (((mapget_1439 = 29) /\ (unnamed_1443 = 9))) -> imapget_1444 >= 59;
constraint (((mapget_1439 = 29) /\ (unnamed_1443 = 10))) -> imapget_1444 >= 60;
constraint (((mapget_1439 = 30) /\ (unnamed_1443 = 1))) -> imapget_1444 >= 61;
constraint (((mapget_1439 = 30) /\ (unnamed_1443 = 2))) -> imapget_1444 >= 62;
constraint (((mapget_1439 = 30) /\ (unnamed_1443 = 3))) -> imapget_1444 >= 63;
constraint (((mapget_1439 = 30) /\ (unnamed_1443 = 4))) -> imapget_1444 >= 64;
constraint (((mapget_1439 = 30) /\ (unnamed_1443 = 5))) -> imapget_1444 >= 65;
constraint (((mapget_1439 = 30) /\ (unnamed_1443 = 6))) -> imapget_1444 >= 66;
constraint (((mapget_1439 = 30) /\ (unnamed_1443 = 7))) -> imapget_1444 >= 67;
constraint (((mapget_1439 = 30) /\ (unnamed_1443 = 8))) -> imapget_1444 >= 68;
constraint (((mapget_1439 = 30) /\ (unnamed_1443 = 9))) -> imapget_1444 >= 69;
constraint (((mapget_1439 = 30) /\ (unnamed_1443 = 10))) -> imapget_1444 >= 70;
constraint (((mapget_1439 = 32) /\ (unnamed_1443 = 1))) -> imapget_1444 >= 71;
constraint (((mapget_1439 = 32) /\ (unnamed_1443 = 2))) -> imapget_1444 >= 72;
constraint (((mapget_1439 = 32) /\ (unnamed_1443 = 3))) -> imapget_1444 >= 73;
constraint (((mapget_1439 = 32) /\ (unnamed_1443 = 4))) -> imapget_1444 >= 74;
constraint (((mapget_1439 = 32) /\ (unnamed_1443 = 5))) -> imapget_1444 >= 75;
constraint (((mapget_1439 = 32) /\ (unnamed_1443 = 6))) -> imapget_1444 >= 76;
constraint (((mapget_1439 = 32) /\ (unnamed_1443 = 7))) -> imapget_1444 >= 77;
constraint (((mapget_1439 = 32) /\ (unnamed_1443 = 8))) -> imapget_1444 >= 78;
constraint (((mapget_1439 = 32) /\ (unnamed_1443 = 9))) -> imapget_1444 >= 79;
constraint (((mapget_1439 = 32) /\ (unnamed_1443 = 10))) -> imapget_1444 >= 80;
constraint (((mapget_1439 = 33) /\ (unnamed_1443 = 1))) -> imapget_1444 >= 81;
constraint (((mapget_1439 = 33) /\ (unnamed_1443 = 2))) -> imapget_1444 >= 82;
constraint (((mapget_1439 = 33) /\ (unnamed_1443 = 3))) -> imapget_1444 >= 83;
constraint (((mapget_1439 = 33) /\ (unnamed_1443 = 4))) -> imapget_1444 >= 84;
constraint (((mapget_1439 = 33) /\ (unnamed_1443 = 5))) -> imapget_1444 >= 85;
constraint (((mapget_1439 = 33) /\ (unnamed_1443 = 6))) -> imapget_1444 >= 86;
constraint (((mapget_1439 = 33) /\ (unnamed_1443 = 7))) -> imapget_1444 >= 87;
constraint (((mapget_1439 = 33) /\ (unnamed_1443 = 8))) -> imapget_1444 >= 88;
constraint (((mapget_1439 = 33) /\ (unnamed_1443 = 9))) -> imapget_1444 >= 89;
constraint (((mapget_1439 = 33) /\ (unnamed_1443 = 10))) -> imapget_1444 >= 90;
constraint (((mapget_1439 = 34) /\ (unnamed_1443 = 1))) -> imapget_1444 >= 91;
constraint (((mapget_1439 = 34) /\ (unnamed_1443 = 2))) -> imapget_1444 >= 92;
constraint (((mapget_1439 = 34) /\ (unnamed_1443 = 3))) -> imapget_1444 >= 93;
constraint (((mapget_1439 = 34) /\ (unnamed_1443 = 4))) -> imapget_1444 >= 94;
constraint (((mapget_1439 = 34) /\ (unnamed_1443 = 5))) -> imapget_1444 >= 95;
constraint (((mapget_1439 = 34) /\ (unnamed_1443 = 6))) -> imapget_1444 >= 96;
constraint (((mapget_1439 = 34) /\ (unnamed_1443 = 7))) -> imapget_1444 >= 97;
constraint (((mapget_1439 = 34) /\ (unnamed_1443 = 8))) -> imapget_1444 >= 98;
constraint (((mapget_1439 = 34) /\ (unnamed_1443 = 9))) -> imapget_1444 >= 99;
constraint (((mapget_1439 = 34) /\ (unnamed_1443 = 10))) -> imapget_1444 >= 100;
constraint mapget_1444 = [0, 15, 16, 16, 6, 8, 8, 3, 4, 17, 15, 0, 11, 18, 10, 12, 18, 4, 11, 7, 16, 11, 0, 13, 13, 12, 8, 1, 14, 5, 16, 18, 13, 0, 12, 16, 6, 5, 15, 12, 6, 10, 13, 12, 0, 2, 8, 19, 9, 5, 8, 12, 12, 16, 2, 0, 11, 14, 16, 8, 8, 18, 8, 6, 8, 11, 0, 11, 20, 19, 3, 4, 1, 5, 19, 14, 11, 0, 7, 2, 4, 11, 14, 15, 9, 16, 20, 7, 0, 12, 17, 7, 5, 12, 5, 8, 19, 2, 12, 0, 20][imapget_1444];

var 0..20: ret_travelTime_1448; %ref (Literal: 0 [0]).ret_travelTime -26
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_travelTime -26
var 1..1: iret_travelTime_1448;
constraint ret_travelTime_1448 = [mapget_1444, 20][iret_travelTime_1448];

var 2..199: Add_1449 = (currentTime_1424 + ret_travelTime_1448);

var 1..10: nextLocation_1451; %ref (Literal: 0 [0]).nextLocation -23
% doing constraints for lookup query: ref (Literal: 0 [0]).nextLocation -23
var 1..1: inextLocation_1451;
constraint nextLocation_1451 = [ret_getLocation_1421, 10][inextLocation_1451];

var 2..199: currentTime_1460; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_1460;
constraint currentTime_1460 = [Add_1449, 199][icurrentTime_1460];

var 1..10: currentLocation_1461; %ref (Literal: 0 [0]).currentLocation -19
% doing constraints for lookup query: ref (Literal: 0 [0]).currentLocation -19
var 1..1: icurrentLocation_1461;
constraint currentLocation_1461 = [nextLocation_1451, 10][icurrentLocation_1461];

var 1..10: location1_1471; %ref (Literal: 0 [0]).location1 -29
% doing constraints for lookup query: ref (Literal: 0 [0]).location1 -29
var 1..1: ilocation1_1471;
constraint location1_1471 = [currentLocation_1461, 10][ilocation1_1471];

var 1..10: unnamed_1474; %ref (Literal: 0 [0]).unnamed -32
% doing constraints for lookup query: ref (Literal: 0 [0]).unnamed -32
var 1..1: iunnamed_1474;
constraint unnamed_1474 = [location1_1471, 10][iunnamed_1474];

var {20,24,25,27,28,29,30,32,33,34}: mapget_1475; %optimise.state.MapGet@5c3
% doing constraints for lookup query: optimise.state.MapGet@5c3
var 1..10: imapget_1475;
constraint [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, unnamed_1474][imapget_1475] = unnamed_1474;
constraint ((unnamed_1474 = 1)) -> imapget_1475 >= 1;
constraint ((unnamed_1474 = 2)) -> imapget_1475 >= 2;
constraint ((unnamed_1474 = 3)) -> imapget_1475 >= 3;
constraint ((unnamed_1474 = 4)) -> imapget_1475 >= 4;
constraint ((unnamed_1474 = 5)) -> imapget_1475 >= 5;
constraint ((unnamed_1474 = 6)) -> imapget_1475 >= 6;
constraint ((unnamed_1474 = 7)) -> imapget_1475 >= 7;
constraint ((unnamed_1474 = 8)) -> imapget_1475 >= 8;
constraint ((unnamed_1474 = 9)) -> imapget_1475 >= 9;
constraint ((unnamed_1474 = 10)) -> imapget_1475 >= 10;
constraint mapget_1475 = [20, 24, 25, 27, 28, 29, 30, 32, 33, 34, 34][imapget_1475];

var {2,5,7,11,12,14,18,19}: mapget_1480; %optimise.state.MapGet@5c8
% doing constraints for lookup query: optimise.state.MapGet@5c8
var 1..10: imapget_1480;
constraint [20, 24, 25, 27, 28, 29, 30, 32, 33, 34, mapget_1475][imapget_1480] = mapget_1475;
constraint ((mapget_1475 = 20)) -> imapget_1480 >= 1;
constraint ((mapget_1475 = 24)) -> imapget_1480 >= 2;
constraint ((mapget_1475 = 25)) -> imapget_1480 >= 3;
constraint ((mapget_1475 = 27)) -> imapget_1480 >= 4;
constraint ((mapget_1475 = 28)) -> imapget_1480 >= 5;
constraint ((mapget_1475 = 29)) -> imapget_1480 >= 6;
constraint ((mapget_1475 = 30)) -> imapget_1480 >= 7;
constraint ((mapget_1475 = 32)) -> imapget_1480 >= 8;
constraint ((mapget_1475 = 33)) -> imapget_1480 >= 9;
constraint ((mapget_1475 = 34)) -> imapget_1480 >= 10;
constraint mapget_1480 = [5, 19, 18, 19, 12, 2, 7, 2, 14, 11, 19][imapget_1480];

var {2,5,7,11,12,14,18,19}: ret_travelTime_1484; %ref (Literal: 0 [0]).ret_travelTime -31
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_travelTime -31
var 1..1: iret_travelTime_1484;
constraint ret_travelTime_1484 = [mapget_1480, 19][iret_travelTime_1484];

var 4..218: Add_1485 = (currentTime_1460 + ret_travelTime_1484);

var 4..218: tripFinishTime_1678; %ref (Literal: routing.Trip@29d25e65 [2]).tripFinishTime -14
% doing constraints for lookup query: ref (Literal: routing.Trip@29d25e65 [2]).tripFinishTime -14
var 1..1: itripFinishTime_1678;
constraint tripFinishTime_1678 = [Add_1485, 218][itripFinishTime_1678];

var 4..218: objective; %ref (Literal: 0 [0]).ret_evaluate -17
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_evaluate -17
var 1..1: iobjective;
constraint objective = [tripFinishTime_1678, 218][iobjective];
var {36,39,42,45,48,51,54,57,60,63}: stop_868; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_868;
constraint stop_868 = [listget_814, 63][istop_868];

var {2,5,7,11,12,14,18,19}: currentTime_871; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_871;
constraint currentTime_871 = [Add_864, 19][icurrentTime_871];

var {36,39,42,45,48,51,54,57,60,63}: stop_933; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_933;
constraint stop_933 = [listget_879, 63][istop_933];

var 2..39: currentTime_936; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_936;
constraint currentTime_936 = [Add_929, 39][icurrentTime_936];

var {36,39,42,45,48,51,54,57,60,63}: stop_998; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_998;
constraint stop_998 = [listget_944, 63][istop_998];

var 2..59: currentTime_1001; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_1001;
constraint currentTime_1001 = [Add_994, 59][icurrentTime_1001];

var {36,39,42,45,48,51,54,57,60,63}: stop_1063; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_1063;
constraint stop_1063 = [listget_1009, 63][istop_1063];

var 2..79: currentTime_1066; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_1066;
constraint currentTime_1066 = [Add_1059, 79][icurrentTime_1066];

var {36,39,42,45,48,51,54,57,60,63}: stop_1128; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_1128;
constraint stop_1128 = [listget_1074, 63][istop_1128];

var 2..99: currentTime_1131; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_1131;
constraint currentTime_1131 = [Add_1124, 99][icurrentTime_1131];

var {36,39,42,45,48,51,54,57,60,63}: stop_1193; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_1193;
constraint stop_1193 = [listget_1139, 63][istop_1193];

var 2..119: currentTime_1196; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_1196;
constraint currentTime_1196 = [Add_1189, 119][icurrentTime_1196];

var {36,39,42,45,48,51,54,57,60,63}: stop_1258; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_1258;
constraint stop_1258 = [listget_1204, 63][istop_1258];

var 2..139: currentTime_1261; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_1261;
constraint currentTime_1261 = [Add_1254, 139][icurrentTime_1261];

var {36,39,42,45,48,51,54,57,60,63}: stop_1323; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_1323;
constraint stop_1323 = [listget_1269, 63][istop_1323];

var 2..159: currentTime_1326; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_1326;
constraint currentTime_1326 = [Add_1319, 159][icurrentTime_1326];

var {36,39,42,45,48,51,54,57,60,63}: stop_1388; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_1388;
constraint stop_1388 = [listget_1334, 63][istop_1388];

var 2..179: currentTime_1391; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_1391;
constraint currentTime_1391 = [Add_1384, 179][icurrentTime_1391];

var {36,39,42,45,48,51,54,57,60,63}: stop_1453; %ref (Literal: 0 [0]).stop -21
% doing constraints for lookup query: ref (Literal: 0 [0]).stop -21
var 1..1: istop_1453;
constraint stop_1453 = [listget_1399, 63][istop_1453];

var 2..199: currentTime_1456; %ref (Literal: 0 [0]).currentTime -18
% doing constraints for lookup query: ref (Literal: 0 [0]).currentTime -18
var 1..1: icurrentTime_1456;
constraint currentTime_1456 = [Add_1449, 199][icurrentTime_1456];

var {0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199}: expectedArrivalTime_1520; %ref ref ref (Literal: 0 [0]).j -35.pickupStop -12.expectedArrivalTime -8
% doing constraints for lookup query: ref ref ref (Literal: 0 [0]).j -35.pickupStop -12.expectedArrivalTime -8
var 1..11: iexpectedArrivalTime_1520;
constraint [36, stop_868, stop_933, stop_998, stop_1063, stop_1128, stop_1193, stop_1258, stop_1323, stop_1388, stop_1453, 36][iexpectedArrivalTime_1520] = 36;
constraint (true) -> iexpectedArrivalTime_1520 >= 1;
constraint ((36 = stop_868)) -> iexpectedArrivalTime_1520 >= 2;
constraint ((36 = stop_933)) -> iexpectedArrivalTime_1520 >= 3;
constraint ((36 = stop_998)) -> iexpectedArrivalTime_1520 >= 4;
constraint ((36 = stop_1063)) -> iexpectedArrivalTime_1520 >= 5;
constraint ((36 = stop_1128)) -> iexpectedArrivalTime_1520 >= 6;
constraint ((36 = stop_1193)) -> iexpectedArrivalTime_1520 >= 7;
constraint ((36 = stop_1258)) -> iexpectedArrivalTime_1520 >= 8;
constraint ((36 = stop_1323)) -> iexpectedArrivalTime_1520 >= 9;
constraint ((36 = stop_1388)) -> iexpectedArrivalTime_1520 >= 10;
constraint ((36 = stop_1453)) -> iexpectedArrivalTime_1520 >= 11;
constraint expectedArrivalTime_1520 = [0, currentTime_871, currentTime_936, currentTime_1001, currentTime_1066, currentTime_1131, currentTime_1196, currentTime_1261, currentTime_1326, currentTime_1391, currentTime_1456, 199][iexpectedArrivalTime_1520];

var {0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199}: expectedArrivalTime_1527; %ref ref ref (Literal: 0 [0]).j -35.deliveryStop -11.expectedArrivalTime -8
% doing constraints for lookup query: ref ref ref (Literal: 0 [0]).j -35.deliveryStop -11.expectedArrivalTime -8
var 1..11: iexpectedArrivalTime_1527;
constraint [39, stop_868, stop_933, stop_998, stop_1063, stop_1128, stop_1193, stop_1258, stop_1323, stop_1388, stop_1453, 39][iexpectedArrivalTime_1527] = 39;
constraint (true) -> iexpectedArrivalTime_1527 >= 1;
constraint ((39 = stop_868)) -> iexpectedArrivalTime_1527 >= 2;
constraint ((39 = stop_933)) -> iexpectedArrivalTime_1527 >= 3;
constraint ((39 = stop_998)) -> iexpectedArrivalTime_1527 >= 4;
constraint ((39 = stop_1063)) -> iexpectedArrivalTime_1527 >= 5;
constraint ((39 = stop_1128)) -> iexpectedArrivalTime_1527 >= 6;
constraint ((39 = stop_1193)) -> iexpectedArrivalTime_1527 >= 7;
constraint ((39 = stop_1258)) -> iexpectedArrivalTime_1527 >= 8;
constraint ((39 = stop_1323)) -> iexpectedArrivalTime_1527 >= 9;
constraint ((39 = stop_1388)) -> iexpectedArrivalTime_1527 >= 10;
constraint ((39 = stop_1453)) -> iexpectedArrivalTime_1527 >= 11;
constraint expectedArrivalTime_1527 = [0, currentTime_871, currentTime_936, currentTime_1001, currentTime_1066, currentTime_1131, currentTime_1196, currentTime_1261, currentTime_1326, currentTime_1391, currentTime_1456, 199][iexpectedArrivalTime_1527];

var bool: Greater_1528 = (expectedArrivalTime_1520 > expectedArrivalTime_1527);

var {0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199}: expectedArrivalTime_1556; %ref ref ref (Literal: 0 [0]).j -35.pickupStop -12.expectedArrivalTime -8
% doing constraints for lookup query: ref ref ref (Literal: 0 [0]).j -35.pickupStop -12.expectedArrivalTime -8
var 1..11: iexpectedArrivalTime_1556;
constraint [42, stop_868, stop_933, stop_998, stop_1063, stop_1128, stop_1193, stop_1258, stop_1323, stop_1388, stop_1453, 42][iexpectedArrivalTime_1556] = 42;
constraint (true) -> iexpectedArrivalTime_1556 >= 1;
constraint ((42 = stop_868)) -> iexpectedArrivalTime_1556 >= 2;
constraint ((42 = stop_933)) -> iexpectedArrivalTime_1556 >= 3;
constraint ((42 = stop_998)) -> iexpectedArrivalTime_1556 >= 4;
constraint ((42 = stop_1063)) -> iexpectedArrivalTime_1556 >= 5;
constraint ((42 = stop_1128)) -> iexpectedArrivalTime_1556 >= 6;
constraint ((42 = stop_1193)) -> iexpectedArrivalTime_1556 >= 7;
constraint ((42 = stop_1258)) -> iexpectedArrivalTime_1556 >= 8;
constraint ((42 = stop_1323)) -> iexpectedArrivalTime_1556 >= 9;
constraint ((42 = stop_1388)) -> iexpectedArrivalTime_1556 >= 10;
constraint ((42 = stop_1453)) -> iexpectedArrivalTime_1556 >= 11;
constraint expectedArrivalTime_1556 = [0, currentTime_871, currentTime_936, currentTime_1001, currentTime_1066, currentTime_1131, currentTime_1196, currentTime_1261, currentTime_1326, currentTime_1391, currentTime_1456, 199][iexpectedArrivalTime_1556];

var {0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199}: expectedArrivalTime_1563; %ref ref ref (Literal: 0 [0]).j -35.deliveryStop -11.expectedArrivalTime -8
% doing constraints for lookup query: ref ref ref (Literal: 0 [0]).j -35.deliveryStop -11.expectedArrivalTime -8
var 1..11: iexpectedArrivalTime_1563;
constraint [45, stop_868, stop_933, stop_998, stop_1063, stop_1128, stop_1193, stop_1258, stop_1323, stop_1388, stop_1453, 45][iexpectedArrivalTime_1563] = 45;
constraint (true) -> iexpectedArrivalTime_1563 >= 1;
constraint ((45 = stop_868)) -> iexpectedArrivalTime_1563 >= 2;
constraint ((45 = stop_933)) -> iexpectedArrivalTime_1563 >= 3;
constraint ((45 = stop_998)) -> iexpectedArrivalTime_1563 >= 4;
constraint ((45 = stop_1063)) -> iexpectedArrivalTime_1563 >= 5;
constraint ((45 = stop_1128)) -> iexpectedArrivalTime_1563 >= 6;
constraint ((45 = stop_1193)) -> iexpectedArrivalTime_1563 >= 7;
constraint ((45 = stop_1258)) -> iexpectedArrivalTime_1563 >= 8;
constraint ((45 = stop_1323)) -> iexpectedArrivalTime_1563 >= 9;
constraint ((45 = stop_1388)) -> iexpectedArrivalTime_1563 >= 10;
constraint ((45 = stop_1453)) -> iexpectedArrivalTime_1563 >= 11;
constraint expectedArrivalTime_1563 = [0, currentTime_871, currentTime_936, currentTime_1001, currentTime_1066, currentTime_1131, currentTime_1196, currentTime_1261, currentTime_1326, currentTime_1391, currentTime_1456, 199][iexpectedArrivalTime_1563];

var bool: Greater_1564 = (expectedArrivalTime_1556 > expectedArrivalTime_1563);

var {0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199}: expectedArrivalTime_1592; %ref ref ref (Literal: 0 [0]).j -35.pickupStop -12.expectedArrivalTime -8
% doing constraints for lookup query: ref ref ref (Literal: 0 [0]).j -35.pickupStop -12.expectedArrivalTime -8
var 1..11: iexpectedArrivalTime_1592;
constraint [48, stop_868, stop_933, stop_998, stop_1063, stop_1128, stop_1193, stop_1258, stop_1323, stop_1388, stop_1453, 48][iexpectedArrivalTime_1592] = 48;
constraint (true) -> iexpectedArrivalTime_1592 >= 1;
constraint ((48 = stop_868)) -> iexpectedArrivalTime_1592 >= 2;
constraint ((48 = stop_933)) -> iexpectedArrivalTime_1592 >= 3;
constraint ((48 = stop_998)) -> iexpectedArrivalTime_1592 >= 4;
constraint ((48 = stop_1063)) -> iexpectedArrivalTime_1592 >= 5;
constraint ((48 = stop_1128)) -> iexpectedArrivalTime_1592 >= 6;
constraint ((48 = stop_1193)) -> iexpectedArrivalTime_1592 >= 7;
constraint ((48 = stop_1258)) -> iexpectedArrivalTime_1592 >= 8;
constraint ((48 = stop_1323)) -> iexpectedArrivalTime_1592 >= 9;
constraint ((48 = stop_1388)) -> iexpectedArrivalTime_1592 >= 10;
constraint ((48 = stop_1453)) -> iexpectedArrivalTime_1592 >= 11;
constraint expectedArrivalTime_1592 = [0, currentTime_871, currentTime_936, currentTime_1001, currentTime_1066, currentTime_1131, currentTime_1196, currentTime_1261, currentTime_1326, currentTime_1391, currentTime_1456, 199][iexpectedArrivalTime_1592];

var {0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199}: expectedArrivalTime_1599; %ref ref ref (Literal: 0 [0]).j -35.deliveryStop -11.expectedArrivalTime -8
% doing constraints for lookup query: ref ref ref (Literal: 0 [0]).j -35.deliveryStop -11.expectedArrivalTime -8
var 1..11: iexpectedArrivalTime_1599;
constraint [51, stop_868, stop_933, stop_998, stop_1063, stop_1128, stop_1193, stop_1258, stop_1323, stop_1388, stop_1453, 51][iexpectedArrivalTime_1599] = 51;
constraint (true) -> iexpectedArrivalTime_1599 >= 1;
constraint ((51 = stop_868)) -> iexpectedArrivalTime_1599 >= 2;
constraint ((51 = stop_933)) -> iexpectedArrivalTime_1599 >= 3;
constraint ((51 = stop_998)) -> iexpectedArrivalTime_1599 >= 4;
constraint ((51 = stop_1063)) -> iexpectedArrivalTime_1599 >= 5;
constraint ((51 = stop_1128)) -> iexpectedArrivalTime_1599 >= 6;
constraint ((51 = stop_1193)) -> iexpectedArrivalTime_1599 >= 7;
constraint ((51 = stop_1258)) -> iexpectedArrivalTime_1599 >= 8;
constraint ((51 = stop_1323)) -> iexpectedArrivalTime_1599 >= 9;
constraint ((51 = stop_1388)) -> iexpectedArrivalTime_1599 >= 10;
constraint ((51 = stop_1453)) -> iexpectedArrivalTime_1599 >= 11;
constraint expectedArrivalTime_1599 = [0, currentTime_871, currentTime_936, currentTime_1001, currentTime_1066, currentTime_1131, currentTime_1196, currentTime_1261, currentTime_1326, currentTime_1391, currentTime_1456, 199][iexpectedArrivalTime_1599];

var bool: Greater_1600 = (expectedArrivalTime_1592 > expectedArrivalTime_1599);

var {0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199}: expectedArrivalTime_1628; %ref ref ref (Literal: 0 [0]).j -35.pickupStop -12.expectedArrivalTime -8
% doing constraints for lookup query: ref ref ref (Literal: 0 [0]).j -35.pickupStop -12.expectedArrivalTime -8
var 1..11: iexpectedArrivalTime_1628;
constraint [54, stop_868, stop_933, stop_998, stop_1063, stop_1128, stop_1193, stop_1258, stop_1323, stop_1388, stop_1453, 54][iexpectedArrivalTime_1628] = 54;
constraint (true) -> iexpectedArrivalTime_1628 >= 1;
constraint ((54 = stop_868)) -> iexpectedArrivalTime_1628 >= 2;
constraint ((54 = stop_933)) -> iexpectedArrivalTime_1628 >= 3;
constraint ((54 = stop_998)) -> iexpectedArrivalTime_1628 >= 4;
constraint ((54 = stop_1063)) -> iexpectedArrivalTime_1628 >= 5;
constraint ((54 = stop_1128)) -> iexpectedArrivalTime_1628 >= 6;
constraint ((54 = stop_1193)) -> iexpectedArrivalTime_1628 >= 7;
constraint ((54 = stop_1258)) -> iexpectedArrivalTime_1628 >= 8;
constraint ((54 = stop_1323)) -> iexpectedArrivalTime_1628 >= 9;
constraint ((54 = stop_1388)) -> iexpectedArrivalTime_1628 >= 10;
constraint ((54 = stop_1453)) -> iexpectedArrivalTime_1628 >= 11;
constraint expectedArrivalTime_1628 = [0, currentTime_871, currentTime_936, currentTime_1001, currentTime_1066, currentTime_1131, currentTime_1196, currentTime_1261, currentTime_1326, currentTime_1391, currentTime_1456, 199][iexpectedArrivalTime_1628];

var {0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199}: expectedArrivalTime_1635; %ref ref ref (Literal: 0 [0]).j -35.deliveryStop -11.expectedArrivalTime -8
% doing constraints for lookup query: ref ref ref (Literal: 0 [0]).j -35.deliveryStop -11.expectedArrivalTime -8
var 1..11: iexpectedArrivalTime_1635;
constraint [57, stop_868, stop_933, stop_998, stop_1063, stop_1128, stop_1193, stop_1258, stop_1323, stop_1388, stop_1453, 57][iexpectedArrivalTime_1635] = 57;
constraint (true) -> iexpectedArrivalTime_1635 >= 1;
constraint ((57 = stop_868)) -> iexpectedArrivalTime_1635 >= 2;
constraint ((57 = stop_933)) -> iexpectedArrivalTime_1635 >= 3;
constraint ((57 = stop_998)) -> iexpectedArrivalTime_1635 >= 4;
constraint ((57 = stop_1063)) -> iexpectedArrivalTime_1635 >= 5;
constraint ((57 = stop_1128)) -> iexpectedArrivalTime_1635 >= 6;
constraint ((57 = stop_1193)) -> iexpectedArrivalTime_1635 >= 7;
constraint ((57 = stop_1258)) -> iexpectedArrivalTime_1635 >= 8;
constraint ((57 = stop_1323)) -> iexpectedArrivalTime_1635 >= 9;
constraint ((57 = stop_1388)) -> iexpectedArrivalTime_1635 >= 10;
constraint ((57 = stop_1453)) -> iexpectedArrivalTime_1635 >= 11;
constraint expectedArrivalTime_1635 = [0, currentTime_871, currentTime_936, currentTime_1001, currentTime_1066, currentTime_1131, currentTime_1196, currentTime_1261, currentTime_1326, currentTime_1391, currentTime_1456, 199][iexpectedArrivalTime_1635];

var bool: Greater_1636 = (expectedArrivalTime_1628 > expectedArrivalTime_1635);

var {0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199}: expectedArrivalTime_1664; %ref ref ref (Literal: 0 [0]).j -35.pickupStop -12.expectedArrivalTime -8
% doing constraints for lookup query: ref ref ref (Literal: 0 [0]).j -35.pickupStop -12.expectedArrivalTime -8
var 1..11: iexpectedArrivalTime_1664;
constraint [60, stop_868, stop_933, stop_998, stop_1063, stop_1128, stop_1193, stop_1258, stop_1323, stop_1388, stop_1453, 60][iexpectedArrivalTime_1664] = 60;
constraint (true) -> iexpectedArrivalTime_1664 >= 1;
constraint ((60 = stop_868)) -> iexpectedArrivalTime_1664 >= 2;
constraint ((60 = stop_933)) -> iexpectedArrivalTime_1664 >= 3;
constraint ((60 = stop_998)) -> iexpectedArrivalTime_1664 >= 4;
constraint ((60 = stop_1063)) -> iexpectedArrivalTime_1664 >= 5;
constraint ((60 = stop_1128)) -> iexpectedArrivalTime_1664 >= 6;
constraint ((60 = stop_1193)) -> iexpectedArrivalTime_1664 >= 7;
constraint ((60 = stop_1258)) -> iexpectedArrivalTime_1664 >= 8;
constraint ((60 = stop_1323)) -> iexpectedArrivalTime_1664 >= 9;
constraint ((60 = stop_1388)) -> iexpectedArrivalTime_1664 >= 10;
constraint ((60 = stop_1453)) -> iexpectedArrivalTime_1664 >= 11;
constraint expectedArrivalTime_1664 = [0, currentTime_871, currentTime_936, currentTime_1001, currentTime_1066, currentTime_1131, currentTime_1196, currentTime_1261, currentTime_1326, currentTime_1391, currentTime_1456, 199][iexpectedArrivalTime_1664];

var {0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199}: expectedArrivalTime_1671; %ref ref ref (Literal: 0 [0]).j -35.deliveryStop -11.expectedArrivalTime -8
% doing constraints for lookup query: ref ref ref (Literal: 0 [0]).j -35.deliveryStop -11.expectedArrivalTime -8
var 1..11: iexpectedArrivalTime_1671;
constraint [63, stop_868, stop_933, stop_998, stop_1063, stop_1128, stop_1193, stop_1258, stop_1323, stop_1388, stop_1453, 63][iexpectedArrivalTime_1671] = 63;
constraint (true) -> iexpectedArrivalTime_1671 >= 1;
constraint ((63 = stop_868)) -> iexpectedArrivalTime_1671 >= 2;
constraint ((63 = stop_933)) -> iexpectedArrivalTime_1671 >= 3;
constraint ((63 = stop_998)) -> iexpectedArrivalTime_1671 >= 4;
constraint ((63 = stop_1063)) -> iexpectedArrivalTime_1671 >= 5;
constraint ((63 = stop_1128)) -> iexpectedArrivalTime_1671 >= 6;
constraint ((63 = stop_1193)) -> iexpectedArrivalTime_1671 >= 7;
constraint ((63 = stop_1258)) -> iexpectedArrivalTime_1671 >= 8;
constraint ((63 = stop_1323)) -> iexpectedArrivalTime_1671 >= 9;
constraint ((63 = stop_1388)) -> iexpectedArrivalTime_1671 >= 10;
constraint ((63 = stop_1453)) -> iexpectedArrivalTime_1671 >= 11;
constraint expectedArrivalTime_1671 = [0, currentTime_871, currentTime_936, currentTime_1001, currentTime_1066, currentTime_1131, currentTime_1196, currentTime_1261, currentTime_1326, currentTime_1391, currentTime_1456, 199][iexpectedArrivalTime_1671];

var bool: Greater_1672 = (expectedArrivalTime_1664 > expectedArrivalTime_1671);

array[1..6] of var 1..6: prev;
constraint prev[1] = 4;
constraint prev[2] in {2,5}; %optimise.state.EndCond@643
constraint prev[3] in {1,3}; %optimise.state.EndCond@5fb
constraint prev[4] in {4,6}; %optimise.state.EndCond@68b
constraint prev[5] in {3,5}; %optimise.state.EndCond@61f
constraint prev[6] in {2,6}; %optimise.state.EndCond@667
constraint alldifferent (prev);
constraint (prev[3] = 1) -> not Greater_1528;
constraint (prev[5] = 3) -> not Greater_1564;
constraint (prev[2] = 5) -> not Greater_1600;
constraint (prev[6] = 2) -> not Greater_1636;
constraint (prev[4] = 6) -> not Greater_1672;
solve :: seq_search([
		 int_search(chooseOrderIndex_2,input_order,indomain_min,complete),
		int_search(chooseOrderIndex_2, first_fail, indomain_min, complete),
		int_search(chooseOrderVal_2, first_fail, indomain_min, complete),
		int_search(prev, first_fail, indomain_min, complete),
		bool_search([Greater_1528, Greater_1564, Greater_1600, Greater_1636, Greater_1672], input_order, indomain_max, complete),
		int_search([listget_814, stop_826, istop_826, locationID_832, ilocationID_832, ret_getLocation_836, iret_getLocation_836, nextLocation_843, inextLocation_843, location2_855, ilocation2_855, unnamed_858, iunnamed_858, mapget_859, imapget_859, ret_travelTime_863, iret_travelTime_863, Add_864, nextLocation_866, inextLocation_866, listget_879, stop_891, istop_891, locationID_897, ilocationID_897, ret_getLocation_901, iret_getLocation_901, currentTime_904, icurrentTime_904, currentLocation_905, icurrentLocation_905, nextLocation_908, inextLocation_908, location1_915, ilocation1_915, unnamed_918, iunnamed_918, mapget_919, imapget_919, location2_920, ilocation2_920, unnamed_923, iunnamed_923, mapget_924, imapget_924, ret_travelTime_928, iret_travelTime_928, Add_929, nextLocation_931, inextLocation_931, listget_944, stop_956, istop_956, locationID_962, ilocationID_962, ret_getLocation_966, iret_getLocation_966, currentTime_969, icurrentTime_969, currentLocation_970, icurrentLocation_970, nextLocation_973, inextLocation_973, location1_980, ilocation1_980, unnamed_983, iunnamed_983, mapget_984, imapget_984, location2_985, ilocation2_985, unnamed_988, iunnamed_988, mapget_989, imapget_989, ret_travelTime_993, iret_travelTime_993, Add_994, nextLocation_996, inextLocation_996, listget_1009, stop_1021, istop_1021, locationID_1027, ilocationID_1027, ret_getLocation_1031, iret_getLocation_1031, currentTime_1034, icurrentTime_1034, currentLocation_1035, icurrentLocation_1035, nextLocation_1038, inextLocation_1038, location1_1045, ilocation1_1045, unnamed_1048, iunnamed_1048, mapget_1049, imapget_1049, location2_1050, ilocation2_1050, unnamed_1053, iunnamed_1053, mapget_1054, imapget_1054, ret_travelTime_1058, iret_travelTime_1058, Add_1059, nextLocation_1061, inextLocation_1061, listget_1074, stop_1086, istop_1086, locationID_1092, ilocationID_1092, ret_getLocation_1096, iret_getLocation_1096, currentTime_1099, icurrentTime_1099, currentLocation_1100, icurrentLocation_1100, nextLocation_1103, inextLocation_1103, location1_1110, ilocation1_1110, unnamed_1113, iunnamed_1113, mapget_1114, imapget_1114, location2_1115, ilocation2_1115, unnamed_1118, iunnamed_1118, mapget_1119, imapget_1119, ret_travelTime_1123, iret_travelTime_1123, Add_1124, nextLocation_1126, inextLocation_1126, listget_1139, stop_1151, istop_1151, locationID_1157, ilocationID_1157, ret_getLocation_1161, iret_getLocation_1161, currentTime_1164, icurrentTime_1164, currentLocation_1165, icurrentLocation_1165, nextLocation_1168, inextLocation_1168, location1_1175, ilocation1_1175, unnamed_1178, iunnamed_1178, mapget_1179, imapget_1179, location2_1180, ilocation2_1180, unnamed_1183, iunnamed_1183, mapget_1184, imapget_1184, ret_travelTime_1188, iret_travelTime_1188, Add_1189, nextLocation_1191, inextLocation_1191, listget_1204, stop_1216, istop_1216, locationID_1222, ilocationID_1222, ret_getLocation_1226, iret_getLocation_1226, currentTime_1229, icurrentTime_1229, currentLocation_1230, icurrentLocation_1230, nextLocation_1233, inextLocation_1233, location1_1240, ilocation1_1240, unnamed_1243, iunnamed_1243, mapget_1244, imapget_1244, location2_1245, ilocation2_1245, unnamed_1248, iunnamed_1248, mapget_1249, imapget_1249, ret_travelTime_1253, iret_travelTime_1253, Add_1254, nextLocation_1256, inextLocation_1256, listget_1269, stop_1281, istop_1281, locationID_1287, ilocationID_1287, ret_getLocation_1291, iret_getLocation_1291, currentTime_1294, icurrentTime_1294, currentLocation_1295, icurrentLocation_1295, nextLocation_1298, inextLocation_1298, location1_1305, ilocation1_1305, unnamed_1308, iunnamed_1308, mapget_1309, imapget_1309, location2_1310, ilocation2_1310, unnamed_1313, iunnamed_1313, mapget_1314, imapget_1314, ret_travelTime_1318, iret_travelTime_1318, Add_1319, nextLocation_1321, inextLocation_1321, listget_1334, stop_1346, istop_1346, locationID_1352, ilocationID_1352, ret_getLocation_1356, iret_getLocation_1356, currentTime_1359, icurrentTime_1359, currentLocation_1360, icurrentLocation_1360, nextLocation_1363, inextLocation_1363, location1_1370, ilocation1_1370, unnamed_1373, iunnamed_1373, mapget_1374, imapget_1374, location2_1375, ilocation2_1375, unnamed_1378, iunnamed_1378, mapget_1379, imapget_1379, ret_travelTime_1383, iret_travelTime_1383, Add_1384, nextLocation_1386, inextLocation_1386, listget_1399, stop_1411, istop_1411, locationID_1417, ilocationID_1417, ret_getLocation_1421, iret_getLocation_1421, currentTime_1424, icurrentTime_1424, currentLocation_1425, icurrentLocation_1425, nextLocation_1428, inextLocation_1428, location1_1435, ilocation1_1435, unnamed_1438, iunnamed_1438, mapget_1439, imapget_1439, location2_1440, ilocation2_1440, unnamed_1443, iunnamed_1443, mapget_1444, imapget_1444, ret_travelTime_1448, iret_travelTime_1448, Add_1449, nextLocation_1451, inextLocation_1451, currentTime_1460, icurrentTime_1460, currentLocation_1461, icurrentLocation_1461, location1_1471, ilocation1_1471, unnamed_1474, iunnamed_1474, mapget_1475, imapget_1475, mapget_1480, imapget_1480, ret_travelTime_1484, iret_travelTime_1484, Add_1485, tripFinishTime_1678, itripFinishTime_1678, objective, iobjective, stop_868, istop_868, currentTime_871, icurrentTime_871, stop_933, istop_933, currentTime_936, icurrentTime_936, stop_998, istop_998, currentTime_1001, icurrentTime_1001, stop_1063, istop_1063, currentTime_1066, icurrentTime_1066, stop_1128, istop_1128, currentTime_1131, icurrentTime_1131, stop_1193, istop_1193, currentTime_1196, icurrentTime_1196, stop_1258, istop_1258, currentTime_1261, icurrentTime_1261, stop_1323, istop_1323, currentTime_1326, icurrentTime_1326, stop_1388, istop_1388, currentTime_1391, icurrentTime_1391, stop_1453, istop_1453, currentTime_1456, icurrentTime_1456, expectedArrivalTime_1520, iexpectedArrivalTime_1520, expectedArrivalTime_1527, iexpectedArrivalTime_1527, expectedArrivalTime_1556, iexpectedArrivalTime_1556, expectedArrivalTime_1563, iexpectedArrivalTime_1563, expectedArrivalTime_1592, iexpectedArrivalTime_1592, expectedArrivalTime_1599, iexpectedArrivalTime_1599, expectedArrivalTime_1628, iexpectedArrivalTime_1628, expectedArrivalTime_1635, iexpectedArrivalTime_1635, expectedArrivalTime_1664, iexpectedArrivalTime_1664, expectedArrivalTime_1671, iexpectedArrivalTime_1671], first_fail, indomain_min, complete),
	])
	minimize objective;

output [
	"chooseOrderIndex_2 = \(chooseOrderIndex_2);\n",
	"chooseOrderVal_2 = \(chooseOrderVal_2);\n",
	"prev = \(prev);\n",
	"constraint Greater_1528 = \(Greater_1528);\n",
	"constraint Greater_1564 = \(Greater_1564);\n",
	"constraint Greater_1600 = \(Greater_1600);\n",
	"constraint Greater_1636 = \(Greater_1636);\n",
	"constraint Greater_1672 = \(Greater_1672);\n",
	"listget_814 = \(listget_814);\n",
	"stop_826 = \(stop_826);\n",
	"istop_826 = \(istop_826);\n",
	"locationID_832 = \(locationID_832);\n",
	"ilocationID_832 = \(ilocationID_832);\n",
	"ret_getLocation_836 = \(ret_getLocation_836);\n",
	"iret_getLocation_836 = \(iret_getLocation_836);\n",
	"nextLocation_843 = \(nextLocation_843);\n",
	"inextLocation_843 = \(inextLocation_843);\n",
	"location2_855 = \(location2_855);\n",
	"ilocation2_855 = \(ilocation2_855);\n",
	"unnamed_858 = \(unnamed_858);\n",
	"iunnamed_858 = \(iunnamed_858);\n",
	"mapget_859 = \(mapget_859);\n",
	"imapget_859 = \(imapget_859);\n",
	"ret_travelTime_863 = \(ret_travelTime_863);\n",
	"iret_travelTime_863 = \(iret_travelTime_863);\n",
	"constraint Add_864 = \(Add_864);\n",
	"nextLocation_866 = \(nextLocation_866);\n",
	"inextLocation_866 = \(inextLocation_866);\n",
	"listget_879 = \(listget_879);\n",
	"stop_891 = \(stop_891);\n",
	"istop_891 = \(istop_891);\n",
	"locationID_897 = \(locationID_897);\n",
	"ilocationID_897 = \(ilocationID_897);\n",
	"ret_getLocation_901 = \(ret_getLocation_901);\n",
	"iret_getLocation_901 = \(iret_getLocation_901);\n",
	"currentTime_904 = \(currentTime_904);\n",
	"icurrentTime_904 = \(icurrentTime_904);\n",
	"currentLocation_905 = \(currentLocation_905);\n",
	"icurrentLocation_905 = \(icurrentLocation_905);\n",
	"nextLocation_908 = \(nextLocation_908);\n",
	"inextLocation_908 = \(inextLocation_908);\n",
	"location1_915 = \(location1_915);\n",
	"ilocation1_915 = \(ilocation1_915);\n",
	"unnamed_918 = \(unnamed_918);\n",
	"iunnamed_918 = \(iunnamed_918);\n",
	"mapget_919 = \(mapget_919);\n",
	"imapget_919 = \(imapget_919);\n",
	"location2_920 = \(location2_920);\n",
	"ilocation2_920 = \(ilocation2_920);\n",
	"unnamed_923 = \(unnamed_923);\n",
	"iunnamed_923 = \(iunnamed_923);\n",
	"mapget_924 = \(mapget_924);\n",
	"imapget_924 = \(imapget_924);\n",
	"ret_travelTime_928 = \(ret_travelTime_928);\n",
	"iret_travelTime_928 = \(iret_travelTime_928);\n",
	"constraint Add_929 = \(Add_929);\n",
	"nextLocation_931 = \(nextLocation_931);\n",
	"inextLocation_931 = \(inextLocation_931);\n",
	"listget_944 = \(listget_944);\n",
	"stop_956 = \(stop_956);\n",
	"istop_956 = \(istop_956);\n",
	"locationID_962 = \(locationID_962);\n",
	"ilocationID_962 = \(ilocationID_962);\n",
	"ret_getLocation_966 = \(ret_getLocation_966);\n",
	"iret_getLocation_966 = \(iret_getLocation_966);\n",
	"currentTime_969 = \(currentTime_969);\n",
	"icurrentTime_969 = \(icurrentTime_969);\n",
	"currentLocation_970 = \(currentLocation_970);\n",
	"icurrentLocation_970 = \(icurrentLocation_970);\n",
	"nextLocation_973 = \(nextLocation_973);\n",
	"inextLocation_973 = \(inextLocation_973);\n",
	"location1_980 = \(location1_980);\n",
	"ilocation1_980 = \(ilocation1_980);\n",
	"unnamed_983 = \(unnamed_983);\n",
	"iunnamed_983 = \(iunnamed_983);\n",
	"mapget_984 = \(mapget_984);\n",
	"imapget_984 = \(imapget_984);\n",
	"location2_985 = \(location2_985);\n",
	"ilocation2_985 = \(ilocation2_985);\n",
	"unnamed_988 = \(unnamed_988);\n",
	"iunnamed_988 = \(iunnamed_988);\n",
	"mapget_989 = \(mapget_989);\n",
	"imapget_989 = \(imapget_989);\n",
	"ret_travelTime_993 = \(ret_travelTime_993);\n",
	"iret_travelTime_993 = \(iret_travelTime_993);\n",
	"constraint Add_994 = \(Add_994);\n",
	"nextLocation_996 = \(nextLocation_996);\n",
	"inextLocation_996 = \(inextLocation_996);\n",
	"listget_1009 = \(listget_1009);\n",
	"stop_1021 = \(stop_1021);\n",
	"istop_1021 = \(istop_1021);\n",
	"locationID_1027 = \(locationID_1027);\n",
	"ilocationID_1027 = \(ilocationID_1027);\n",
	"ret_getLocation_1031 = \(ret_getLocation_1031);\n",
	"iret_getLocation_1031 = \(iret_getLocation_1031);\n",
	"currentTime_1034 = \(currentTime_1034);\n",
	"icurrentTime_1034 = \(icurrentTime_1034);\n",
	"currentLocation_1035 = \(currentLocation_1035);\n",
	"icurrentLocation_1035 = \(icurrentLocation_1035);\n",
	"nextLocation_1038 = \(nextLocation_1038);\n",
	"inextLocation_1038 = \(inextLocation_1038);\n",
	"location1_1045 = \(location1_1045);\n",
	"ilocation1_1045 = \(ilocation1_1045);\n",
	"unnamed_1048 = \(unnamed_1048);\n",
	"iunnamed_1048 = \(iunnamed_1048);\n",
	"mapget_1049 = \(mapget_1049);\n",
	"imapget_1049 = \(imapget_1049);\n",
	"location2_1050 = \(location2_1050);\n",
	"ilocation2_1050 = \(ilocation2_1050);\n",
	"unnamed_1053 = \(unnamed_1053);\n",
	"iunnamed_1053 = \(iunnamed_1053);\n",
	"mapget_1054 = \(mapget_1054);\n",
	"imapget_1054 = \(imapget_1054);\n",
	"ret_travelTime_1058 = \(ret_travelTime_1058);\n",
	"iret_travelTime_1058 = \(iret_travelTime_1058);\n",
	"constraint Add_1059 = \(Add_1059);\n",
	"nextLocation_1061 = \(nextLocation_1061);\n",
	"inextLocation_1061 = \(inextLocation_1061);\n",
	"listget_1074 = \(listget_1074);\n",
	"stop_1086 = \(stop_1086);\n",
	"istop_1086 = \(istop_1086);\n",
	"locationID_1092 = \(locationID_1092);\n",
	"ilocationID_1092 = \(ilocationID_1092);\n",
	"ret_getLocation_1096 = \(ret_getLocation_1096);\n",
	"iret_getLocation_1096 = \(iret_getLocation_1096);\n",
	"currentTime_1099 = \(currentTime_1099);\n",
	"icurrentTime_1099 = \(icurrentTime_1099);\n",
	"currentLocation_1100 = \(currentLocation_1100);\n",
	"icurrentLocation_1100 = \(icurrentLocation_1100);\n",
	"nextLocation_1103 = \(nextLocation_1103);\n",
	"inextLocation_1103 = \(inextLocation_1103);\n",
	"location1_1110 = \(location1_1110);\n",
	"ilocation1_1110 = \(ilocation1_1110);\n",
	"unnamed_1113 = \(unnamed_1113);\n",
	"iunnamed_1113 = \(iunnamed_1113);\n",
	"mapget_1114 = \(mapget_1114);\n",
	"imapget_1114 = \(imapget_1114);\n",
	"location2_1115 = \(location2_1115);\n",
	"ilocation2_1115 = \(ilocation2_1115);\n",
	"unnamed_1118 = \(unnamed_1118);\n",
	"iunnamed_1118 = \(iunnamed_1118);\n",
	"mapget_1119 = \(mapget_1119);\n",
	"imapget_1119 = \(imapget_1119);\n",
	"ret_travelTime_1123 = \(ret_travelTime_1123);\n",
	"iret_travelTime_1123 = \(iret_travelTime_1123);\n",
	"constraint Add_1124 = \(Add_1124);\n",
	"nextLocation_1126 = \(nextLocation_1126);\n",
	"inextLocation_1126 = \(inextLocation_1126);\n",
	"listget_1139 = \(listget_1139);\n",
	"stop_1151 = \(stop_1151);\n",
	"istop_1151 = \(istop_1151);\n",
	"locationID_1157 = \(locationID_1157);\n",
	"ilocationID_1157 = \(ilocationID_1157);\n",
	"ret_getLocation_1161 = \(ret_getLocation_1161);\n",
	"iret_getLocation_1161 = \(iret_getLocation_1161);\n",
	"currentTime_1164 = \(currentTime_1164);\n",
	"icurrentTime_1164 = \(icurrentTime_1164);\n",
	"currentLocation_1165 = \(currentLocation_1165);\n",
	"icurrentLocation_1165 = \(icurrentLocation_1165);\n",
	"nextLocation_1168 = \(nextLocation_1168);\n",
	"inextLocation_1168 = \(inextLocation_1168);\n",
	"location1_1175 = \(location1_1175);\n",
	"ilocation1_1175 = \(ilocation1_1175);\n",
	"unnamed_1178 = \(unnamed_1178);\n",
	"iunnamed_1178 = \(iunnamed_1178);\n",
	"mapget_1179 = \(mapget_1179);\n",
	"imapget_1179 = \(imapget_1179);\n",
	"location2_1180 = \(location2_1180);\n",
	"ilocation2_1180 = \(ilocation2_1180);\n",
	"unnamed_1183 = \(unnamed_1183);\n",
	"iunnamed_1183 = \(iunnamed_1183);\n",
	"mapget_1184 = \(mapget_1184);\n",
	"imapget_1184 = \(imapget_1184);\n",
	"ret_travelTime_1188 = \(ret_travelTime_1188);\n",
	"iret_travelTime_1188 = \(iret_travelTime_1188);\n",
	"constraint Add_1189 = \(Add_1189);\n",
	"nextLocation_1191 = \(nextLocation_1191);\n",
	"inextLocation_1191 = \(inextLocation_1191);\n",
	"listget_1204 = \(listget_1204);\n",
	"stop_1216 = \(stop_1216);\n",
	"istop_1216 = \(istop_1216);\n",
	"locationID_1222 = \(locationID_1222);\n",
	"ilocationID_1222 = \(ilocationID_1222);\n",
	"ret_getLocation_1226 = \(ret_getLocation_1226);\n",
	"iret_getLocation_1226 = \(iret_getLocation_1226);\n",
	"currentTime_1229 = \(currentTime_1229);\n",
	"icurrentTime_1229 = \(icurrentTime_1229);\n",
	"currentLocation_1230 = \(currentLocation_1230);\n",
	"icurrentLocation_1230 = \(icurrentLocation_1230);\n",
	"nextLocation_1233 = \(nextLocation_1233);\n",
	"inextLocation_1233 = \(inextLocation_1233);\n",
	"location1_1240 = \(location1_1240);\n",
	"ilocation1_1240 = \(ilocation1_1240);\n",
	"unnamed_1243 = \(unnamed_1243);\n",
	"iunnamed_1243 = \(iunnamed_1243);\n",
	"mapget_1244 = \(mapget_1244);\n",
	"imapget_1244 = \(imapget_1244);\n",
	"location2_1245 = \(location2_1245);\n",
	"ilocation2_1245 = \(ilocation2_1245);\n",
	"unnamed_1248 = \(unnamed_1248);\n",
	"iunnamed_1248 = \(iunnamed_1248);\n",
	"mapget_1249 = \(mapget_1249);\n",
	"imapget_1249 = \(imapget_1249);\n",
	"ret_travelTime_1253 = \(ret_travelTime_1253);\n",
	"iret_travelTime_1253 = \(iret_travelTime_1253);\n",
	"constraint Add_1254 = \(Add_1254);\n",
	"nextLocation_1256 = \(nextLocation_1256);\n",
	"inextLocation_1256 = \(inextLocation_1256);\n",
	"listget_1269 = \(listget_1269);\n",
	"stop_1281 = \(stop_1281);\n",
	"istop_1281 = \(istop_1281);\n",
	"locationID_1287 = \(locationID_1287);\n",
	"ilocationID_1287 = \(ilocationID_1287);\n",
	"ret_getLocation_1291 = \(ret_getLocation_1291);\n",
	"iret_getLocation_1291 = \(iret_getLocation_1291);\n",
	"currentTime_1294 = \(currentTime_1294);\n",
	"icurrentTime_1294 = \(icurrentTime_1294);\n",
	"currentLocation_1295 = \(currentLocation_1295);\n",
	"icurrentLocation_1295 = \(icurrentLocation_1295);\n",
	"nextLocation_1298 = \(nextLocation_1298);\n",
	"inextLocation_1298 = \(inextLocation_1298);\n",
	"location1_1305 = \(location1_1305);\n",
	"ilocation1_1305 = \(ilocation1_1305);\n",
	"unnamed_1308 = \(unnamed_1308);\n",
	"iunnamed_1308 = \(iunnamed_1308);\n",
	"mapget_1309 = \(mapget_1309);\n",
	"imapget_1309 = \(imapget_1309);\n",
	"location2_1310 = \(location2_1310);\n",
	"ilocation2_1310 = \(ilocation2_1310);\n",
	"unnamed_1313 = \(unnamed_1313);\n",
	"iunnamed_1313 = \(iunnamed_1313);\n",
	"mapget_1314 = \(mapget_1314);\n",
	"imapget_1314 = \(imapget_1314);\n",
	"ret_travelTime_1318 = \(ret_travelTime_1318);\n",
	"iret_travelTime_1318 = \(iret_travelTime_1318);\n",
	"constraint Add_1319 = \(Add_1319);\n",
	"nextLocation_1321 = \(nextLocation_1321);\n",
	"inextLocation_1321 = \(inextLocation_1321);\n",
	"listget_1334 = \(listget_1334);\n",
	"stop_1346 = \(stop_1346);\n",
	"istop_1346 = \(istop_1346);\n",
	"locationID_1352 = \(locationID_1352);\n",
	"ilocationID_1352 = \(ilocationID_1352);\n",
	"ret_getLocation_1356 = \(ret_getLocation_1356);\n",
	"iret_getLocation_1356 = \(iret_getLocation_1356);\n",
	"currentTime_1359 = \(currentTime_1359);\n",
	"icurrentTime_1359 = \(icurrentTime_1359);\n",
	"currentLocation_1360 = \(currentLocation_1360);\n",
	"icurrentLocation_1360 = \(icurrentLocation_1360);\n",
	"nextLocation_1363 = \(nextLocation_1363);\n",
	"inextLocation_1363 = \(inextLocation_1363);\n",
	"location1_1370 = \(location1_1370);\n",
	"ilocation1_1370 = \(ilocation1_1370);\n",
	"unnamed_1373 = \(unnamed_1373);\n",
	"iunnamed_1373 = \(iunnamed_1373);\n",
	"mapget_1374 = \(mapget_1374);\n",
	"imapget_1374 = \(imapget_1374);\n",
	"location2_1375 = \(location2_1375);\n",
	"ilocation2_1375 = \(ilocation2_1375);\n",
	"unnamed_1378 = \(unnamed_1378);\n",
	"iunnamed_1378 = \(iunnamed_1378);\n",
	"mapget_1379 = \(mapget_1379);\n",
	"imapget_1379 = \(imapget_1379);\n",
	"ret_travelTime_1383 = \(ret_travelTime_1383);\n",
	"iret_travelTime_1383 = \(iret_travelTime_1383);\n",
	"constraint Add_1384 = \(Add_1384);\n",
	"nextLocation_1386 = \(nextLocation_1386);\n",
	"inextLocation_1386 = \(inextLocation_1386);\n",
	"listget_1399 = \(listget_1399);\n",
	"stop_1411 = \(stop_1411);\n",
	"istop_1411 = \(istop_1411);\n",
	"locationID_1417 = \(locationID_1417);\n",
	"ilocationID_1417 = \(ilocationID_1417);\n",
	"ret_getLocation_1421 = \(ret_getLocation_1421);\n",
	"iret_getLocation_1421 = \(iret_getLocation_1421);\n",
	"currentTime_1424 = \(currentTime_1424);\n",
	"icurrentTime_1424 = \(icurrentTime_1424);\n",
	"currentLocation_1425 = \(currentLocation_1425);\n",
	"icurrentLocation_1425 = \(icurrentLocation_1425);\n",
	"nextLocation_1428 = \(nextLocation_1428);\n",
	"inextLocation_1428 = \(inextLocation_1428);\n",
	"location1_1435 = \(location1_1435);\n",
	"ilocation1_1435 = \(ilocation1_1435);\n",
	"unnamed_1438 = \(unnamed_1438);\n",
	"iunnamed_1438 = \(iunnamed_1438);\n",
	"mapget_1439 = \(mapget_1439);\n",
	"imapget_1439 = \(imapget_1439);\n",
	"location2_1440 = \(location2_1440);\n",
	"ilocation2_1440 = \(ilocation2_1440);\n",
	"unnamed_1443 = \(unnamed_1443);\n",
	"iunnamed_1443 = \(iunnamed_1443);\n",
	"mapget_1444 = \(mapget_1444);\n",
	"imapget_1444 = \(imapget_1444);\n",
	"ret_travelTime_1448 = \(ret_travelTime_1448);\n",
	"iret_travelTime_1448 = \(iret_travelTime_1448);\n",
	"constraint Add_1449 = \(Add_1449);\n",
	"nextLocation_1451 = \(nextLocation_1451);\n",
	"inextLocation_1451 = \(inextLocation_1451);\n",
	"currentTime_1460 = \(currentTime_1460);\n",
	"icurrentTime_1460 = \(icurrentTime_1460);\n",
	"currentLocation_1461 = \(currentLocation_1461);\n",
	"icurrentLocation_1461 = \(icurrentLocation_1461);\n",
	"location1_1471 = \(location1_1471);\n",
	"ilocation1_1471 = \(ilocation1_1471);\n",
	"unnamed_1474 = \(unnamed_1474);\n",
	"iunnamed_1474 = \(iunnamed_1474);\n",
	"mapget_1475 = \(mapget_1475);\n",
	"imapget_1475 = \(imapget_1475);\n",
	"mapget_1480 = \(mapget_1480);\n",
	"imapget_1480 = \(imapget_1480);\n",
	"ret_travelTime_1484 = \(ret_travelTime_1484);\n",
	"iret_travelTime_1484 = \(iret_travelTime_1484);\n",
	"constraint Add_1485 = \(Add_1485);\n",
	"tripFinishTime_1678 = \(tripFinishTime_1678);\n",
	"itripFinishTime_1678 = \(itripFinishTime_1678);\n",
	"iobjective = \(iobjective);\n",
	"stop_868 = \(stop_868);\n",
	"istop_868 = \(istop_868);\n",
	"currentTime_871 = \(currentTime_871);\n",
	"icurrentTime_871 = \(icurrentTime_871);\n",
	"stop_933 = \(stop_933);\n",
	"istop_933 = \(istop_933);\n",
	"currentTime_936 = \(currentTime_936);\n",
	"icurrentTime_936 = \(icurrentTime_936);\n",
	"stop_998 = \(stop_998);\n",
	"istop_998 = \(istop_998);\n",
	"currentTime_1001 = \(currentTime_1001);\n",
	"icurrentTime_1001 = \(icurrentTime_1001);\n",
	"stop_1063 = \(stop_1063);\n",
	"istop_1063 = \(istop_1063);\n",
	"currentTime_1066 = \(currentTime_1066);\n",
	"icurrentTime_1066 = \(icurrentTime_1066);\n",
	"stop_1128 = \(stop_1128);\n",
	"istop_1128 = \(istop_1128);\n",
	"currentTime_1131 = \(currentTime_1131);\n",
	"icurrentTime_1131 = \(icurrentTime_1131);\n",
	"stop_1193 = \(stop_1193);\n",
	"istop_1193 = \(istop_1193);\n",
	"currentTime_1196 = \(currentTime_1196);\n",
	"icurrentTime_1196 = \(icurrentTime_1196);\n",
	"stop_1258 = \(stop_1258);\n",
	"istop_1258 = \(istop_1258);\n",
	"currentTime_1261 = \(currentTime_1261);\n",
	"icurrentTime_1261 = \(icurrentTime_1261);\n",
	"stop_1323 = \(stop_1323);\n",
	"istop_1323 = \(istop_1323);\n",
	"currentTime_1326 = \(currentTime_1326);\n",
	"icurrentTime_1326 = \(icurrentTime_1326);\n",
	"stop_1388 = \(stop_1388);\n",
	"istop_1388 = \(istop_1388);\n",
	"currentTime_1391 = \(currentTime_1391);\n",
	"icurrentTime_1391 = \(icurrentTime_1391);\n",
	"stop_1453 = \(stop_1453);\n",
	"istop_1453 = \(istop_1453);\n",
	"currentTime_1456 = \(currentTime_1456);\n",
	"icurrentTime_1456 = \(icurrentTime_1456);\n",
	"expectedArrivalTime_1520 = \(expectedArrivalTime_1520);\n",
	"iexpectedArrivalTime_1520 = \(iexpectedArrivalTime_1520);\n",
	"expectedArrivalTime_1527 = \(expectedArrivalTime_1527);\n",
	"iexpectedArrivalTime_1527 = \(iexpectedArrivalTime_1527);\n",
	"expectedArrivalTime_1556 = \(expectedArrivalTime_1556);\n",
	"iexpectedArrivalTime_1556 = \(iexpectedArrivalTime_1556);\n",
	"expectedArrivalTime_1563 = \(expectedArrivalTime_1563);\n",
	"iexpectedArrivalTime_1563 = \(iexpectedArrivalTime_1563);\n",
	"expectedArrivalTime_1592 = \(expectedArrivalTime_1592);\n",
	"iexpectedArrivalTime_1592 = \(iexpectedArrivalTime_1592);\n",
	"expectedArrivalTime_1599 = \(expectedArrivalTime_1599);\n",
	"iexpectedArrivalTime_1599 = \(iexpectedArrivalTime_1599);\n",
	"expectedArrivalTime_1628 = \(expectedArrivalTime_1628);\n",
	"iexpectedArrivalTime_1628 = \(iexpectedArrivalTime_1628);\n",
	"expectedArrivalTime_1635 = \(expectedArrivalTime_1635);\n",
	"iexpectedArrivalTime_1635 = \(iexpectedArrivalTime_1635);\n",
	"expectedArrivalTime_1664 = \(expectedArrivalTime_1664);\n",
	"iexpectedArrivalTime_1664 = \(iexpectedArrivalTime_1664);\n",
	"expectedArrivalTime_1671 = \(expectedArrivalTime_1671);\n",
	"iexpectedArrivalTime_1671 = \(iexpectedArrivalTime_1671);\n",
	"constraint objective = \(objective);\n",
];

