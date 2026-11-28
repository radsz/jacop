include "globals.mzn";
var 0..1: numUsed_1277; %ref (Literal: 0 [0]).numUsed -17
% doing constraints for lookup query: ref (Literal: 0 [0]).numUsed -17
var 1..3: inumUsed_1277;
constraint [(not notret_isEmpty_1213), notret_isEmpty_1213, true][inumUsed_1277];
constraint numUsed_1277 = [0, 1, 1][inumUsed_1277];
constraint notret_isEmpty_1273 -> (inumUsed_1277 < 3);
var 1..2: Add_1279 = (numUsed_1277 + 1);
var 0..2: numUsed_1337; %ref (Literal: 0 [0]).numUsed -17
% doing constraints for lookup query: ref (Literal: 0 [0]).numUsed -17
var 1..4: inumUsed_1337;
constraint [true, notret_isEmpty_1213, notret_isEmpty_1273, true][inumUsed_1337];
constraint (true) -> inumUsed_1337 >= 1;
constraint (notret_isEmpty_1213) -> inumUsed_1337 >= 2;
constraint (notret_isEmpty_1273) -> inumUsed_1337 >= 3;
constraint numUsed_1337 = [0, 1, Add_1279, 2][inumUsed_1337];
constraint notret_isEmpty_1333 -> (inumUsed_1337 < 4);
var 1..3: Add_1339 = (numUsed_1337 + 1);
var 0..3: numUsed_1397; %ref (Literal: 0 [0]).numUsed -17
% doing constraints for lookup query: ref (Literal: 0 [0]).numUsed -17
var 1..5: inumUsed_1397;
constraint [true, notret_isEmpty_1213, notret_isEmpty_1273, notret_isEmpty_1333, true][inumUsed_1397];
constraint (true) -> inumUsed_1397 >= 1;
constraint (notret_isEmpty_1213) -> inumUsed_1397 >= 2;
constraint (notret_isEmpty_1273) -> inumUsed_1397 >= 3;
constraint (notret_isEmpty_1333) -> inumUsed_1397 >= 4;
constraint numUsed_1397 = [0, 1, Add_1279, Add_1339, 3][inumUsed_1397];
constraint notret_isEmpty_1393 -> (inumUsed_1397 < 5);
var 1..4: Add_1399 = (numUsed_1397 + 1);
var 0..4: numUsed_1457; %ref (Literal: 0 [0]).numUsed -17
% doing constraints for lookup query: ref (Literal: 0 [0]).numUsed -17
var 1..6: inumUsed_1457;
constraint [true, notret_isEmpty_1213, notret_isEmpty_1273, notret_isEmpty_1333, notret_isEmpty_1393, true][inumUsed_1457];
constraint (true) -> inumUsed_1457 >= 1;
constraint (notret_isEmpty_1213) -> inumUsed_1457 >= 2;
constraint (notret_isEmpty_1273) -> inumUsed_1457 >= 3;
constraint (notret_isEmpty_1333) -> inumUsed_1457 >= 4;
constraint (notret_isEmpty_1393) -> inumUsed_1457 >= 5;
constraint numUsed_1457 = [0, 1, Add_1279, Add_1339, Add_1399, 4][inumUsed_1457];
constraint notret_isEmpty_1453 -> (inumUsed_1457 < 6);
var 1..5: Add_1459 = (numUsed_1457 + 1);
var 0..5: numUsed_1517; %ref (Literal: 0 [0]).numUsed -17
% doing constraints for lookup query: ref (Literal: 0 [0]).numUsed -17
var 1..7: inumUsed_1517;
constraint [true, notret_isEmpty_1213, notret_isEmpty_1273, notret_isEmpty_1333, notret_isEmpty_1393, notret_isEmpty_1453, true][inumUsed_1517];
constraint (true) -> inumUsed_1517 >= 1;
constraint (notret_isEmpty_1213) -> inumUsed_1517 >= 2;
constraint (notret_isEmpty_1273) -> inumUsed_1517 >= 3;
constraint (notret_isEmpty_1333) -> inumUsed_1517 >= 4;
constraint (notret_isEmpty_1393) -> inumUsed_1517 >= 5;
constraint (notret_isEmpty_1453) -> inumUsed_1517 >= 6;
constraint numUsed_1517 = [0, 1, Add_1279, Add_1339, Add_1399, Add_1459, 5][inumUsed_1517];
constraint notret_isEmpty_1513 -> (inumUsed_1517 < 7);
var 1..6: Add_1519 = (numUsed_1517 + 1);
var 0..6: numUsed_1577; %ref (Literal: 0 [0]).numUsed -17
% doing constraints for lookup query: ref (Literal: 0 [0]).numUsed -17
var 1..8: inumUsed_1577;
constraint [true, notret_isEmpty_1213, notret_isEmpty_1273, notret_isEmpty_1333, notret_isEmpty_1393, notret_isEmpty_1453, notret_isEmpty_1513, true][inumUsed_1577];
constraint (true) -> inumUsed_1577 >= 1;
constraint (notret_isEmpty_1213) -> inumUsed_1577 >= 2;
constraint (notret_isEmpty_1273) -> inumUsed_1577 >= 3;
constraint (notret_isEmpty_1333) -> inumUsed_1577 >= 4;
constraint (notret_isEmpty_1393) -> inumUsed_1577 >= 5;
constraint (notret_isEmpty_1453) -> inumUsed_1577 >= 6;
constraint (notret_isEmpty_1513) -> inumUsed_1577 >= 7;
constraint numUsed_1577 = [0, 1, Add_1279, Add_1339, Add_1399, Add_1459, Add_1519, 6][inumUsed_1577];
constraint notret_isEmpty_1573 -> (inumUsed_1577 < 8);
var 1..7: Add_1579 = (numUsed_1577 + 1);
var 0..7: numUsed_1637; %ref (Literal: 0 [0]).numUsed -17
% doing constraints for lookup query: ref (Literal: 0 [0]).numUsed -17
var 1..9: inumUsed_1637;
constraint [true, notret_isEmpty_1213, notret_isEmpty_1273, notret_isEmpty_1333, notret_isEmpty_1393, notret_isEmpty_1453, notret_isEmpty_1513, notret_isEmpty_1573, true][inumUsed_1637];
constraint (true) -> inumUsed_1637 >= 1;
constraint (notret_isEmpty_1213) -> inumUsed_1637 >= 2;
constraint (notret_isEmpty_1273) -> inumUsed_1637 >= 3;
constraint (notret_isEmpty_1333) -> inumUsed_1637 >= 4;
constraint (notret_isEmpty_1393) -> inumUsed_1637 >= 5;
constraint (notret_isEmpty_1453) -> inumUsed_1637 >= 6;
constraint (notret_isEmpty_1513) -> inumUsed_1637 >= 7;
constraint (notret_isEmpty_1573) -> inumUsed_1637 >= 8;
constraint numUsed_1637 = [0, 1, Add_1279, Add_1339, Add_1399, Add_1459, Add_1519, Add_1579, 7][inumUsed_1637];
constraint notret_isEmpty_1633 -> (inumUsed_1637 < 9);
var 1..8: Add_1639 = (numUsed_1637 + 1);
var 0..8: numUsed_1697; %ref (Literal: 0 [0]).numUsed -17
% doing constraints for lookup query: ref (Literal: 0 [0]).numUsed -17
var 1..10: inumUsed_1697;
constraint [true, notret_isEmpty_1213, notret_isEmpty_1273, notret_isEmpty_1333, notret_isEmpty_1393, notret_isEmpty_1453, notret_isEmpty_1513, notret_isEmpty_1573, notret_isEmpty_1633, true][inumUsed_1697];
constraint (true) -> inumUsed_1697 >= 1;
constraint (notret_isEmpty_1213) -> inumUsed_1697 >= 2;
constraint (notret_isEmpty_1273) -> inumUsed_1697 >= 3;
constraint (notret_isEmpty_1333) -> inumUsed_1697 >= 4;
constraint (notret_isEmpty_1393) -> inumUsed_1697 >= 5;
constraint (notret_isEmpty_1453) -> inumUsed_1697 >= 6;
constraint (notret_isEmpty_1513) -> inumUsed_1697 >= 7;
constraint (notret_isEmpty_1573) -> inumUsed_1697 >= 8;
constraint (notret_isEmpty_1633) -> inumUsed_1697 >= 9;
constraint numUsed_1697 = [0, 1, Add_1279, Add_1339, Add_1399, Add_1459, Add_1519, Add_1579, Add_1639, 8][inumUsed_1697];
constraint notret_isEmpty_1693 -> (inumUsed_1697 < 10);
var 1..9: Add_1699 = (numUsed_1697 + 1);
var 0..9: numUsed_1757; %ref (Literal: 0 [0]).numUsed -17
% doing constraints for lookup query: ref (Literal: 0 [0]).numUsed -17
var 1..11: inumUsed_1757;
constraint [true, notret_isEmpty_1213, notret_isEmpty_1273, notret_isEmpty_1333, notret_isEmpty_1393, notret_isEmpty_1453, notret_isEmpty_1513, notret_isEmpty_1573, notret_isEmpty_1633, notret_isEmpty_1693, true][inumUsed_1757];
constraint (true) -> inumUsed_1757 >= 1;
constraint (notret_isEmpty_1213) -> inumUsed_1757 >= 2;
constraint (notret_isEmpty_1273) -> inumUsed_1757 >= 3;
constraint (notret_isEmpty_1333) -> inumUsed_1757 >= 4;
constraint (notret_isEmpty_1393) -> inumUsed_1757 >= 5;
constraint (notret_isEmpty_1453) -> inumUsed_1757 >= 6;
constraint (notret_isEmpty_1513) -> inumUsed_1757 >= 7;
constraint (notret_isEmpty_1573) -> inumUsed_1757 >= 8;
constraint (notret_isEmpty_1633) -> inumUsed_1757 >= 9;
constraint (notret_isEmpty_1693) -> inumUsed_1757 >= 10;
constraint numUsed_1757 = [0, 1, Add_1279, Add_1339, Add_1399, Add_1459, Add_1519, Add_1579, Add_1639, Add_1699, 9][inumUsed_1757];
constraint notret_isEmpty_1753 -> (inumUsed_1757 < 11);
var 1..10: Add_1759 = (numUsed_1757 + 1);
var 0..10: numUsed_1817; %ref (Literal: 0 [0]).numUsed -17
% doing constraints for lookup query: ref (Literal: 0 [0]).numUsed -17
var 1..12: inumUsed_1817;
constraint [true, notret_isEmpty_1213, notret_isEmpty_1273, notret_isEmpty_1333, notret_isEmpty_1393, notret_isEmpty_1453, notret_isEmpty_1513, notret_isEmpty_1573, notret_isEmpty_1633, notret_isEmpty_1693, notret_isEmpty_1753, true][inumUsed_1817];
constraint (true) -> inumUsed_1817 >= 1;
constraint (notret_isEmpty_1213) -> inumUsed_1817 >= 2;
constraint (notret_isEmpty_1273) -> inumUsed_1817 >= 3;
constraint (notret_isEmpty_1333) -> inumUsed_1817 >= 4;
constraint (notret_isEmpty_1393) -> inumUsed_1817 >= 5;
constraint (notret_isEmpty_1453) -> inumUsed_1817 >= 6;
constraint (notret_isEmpty_1513) -> inumUsed_1817 >= 7;
constraint (notret_isEmpty_1573) -> inumUsed_1817 >= 8;
constraint (notret_isEmpty_1633) -> inumUsed_1817 >= 9;
constraint (notret_isEmpty_1693) -> inumUsed_1817 >= 10;
constraint (notret_isEmpty_1753) -> inumUsed_1817 >= 11;
constraint numUsed_1817 = [0, 1, Add_1279, Add_1339, Add_1399, Add_1459, Add_1519, Add_1579, Add_1639, Add_1699, Add_1759, 10][inumUsed_1817];
constraint notret_isEmpty_1813 -> (inumUsed_1817 < 12);
var 1..11: Add_1819 = (numUsed_1817 + 1);
var 0..11: numUsed_1825; %ref (Literal: 0 [0]).numUsed -17
% doing constraints for lookup query: ref (Literal: 0 [0]).numUsed -17
var 1..12: inumUsed_1825;
constraint [true, notret_isEmpty_1213, notret_isEmpty_1273, notret_isEmpty_1333, notret_isEmpty_1393, notret_isEmpty_1453, notret_isEmpty_1513, notret_isEmpty_1573, notret_isEmpty_1633, notret_isEmpty_1693, notret_isEmpty_1753, notret_isEmpty_1813, true][inumUsed_1825];
constraint (true) -> inumUsed_1825 >= 1;
constraint (notret_isEmpty_1213) -> inumUsed_1825 >= 2;
constraint (notret_isEmpty_1273) -> inumUsed_1825 >= 3;
constraint (notret_isEmpty_1333) -> inumUsed_1825 >= 4;
constraint (notret_isEmpty_1393) -> inumUsed_1825 >= 5;
constraint (notret_isEmpty_1453) -> inumUsed_1825 >= 6;
constraint (notret_isEmpty_1513) -> inumUsed_1825 >= 7;
constraint (notret_isEmpty_1573) -> inumUsed_1825 >= 8;
constraint (notret_isEmpty_1633) -> inumUsed_1825 >= 9;
constraint (notret_isEmpty_1693) -> inumUsed_1825 >= 10;
constraint (notret_isEmpty_1753) -> inumUsed_1825 >= 11;
constraint (notret_isEmpty_1813) -> inumUsed_1825 >= 12;
constraint numUsed_1825 = [0, 1, Add_1279, Add_1339, Add_1399, Add_1459, Add_1519, Add_1579, Add_1639, Add_1699, Add_1759, Add_1819, 11][inumUsed_1825];

var 0..11: objective; %ref (Literal: 0 [0]).ret_evaluate -16
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_evaluate -16
var 1..1: iobjective;
constraint objective = [numUsed_1825, 11][iobjective];
var {4,7,10,13,16,19,22,25,28,31,34}: chooseobj_588; %optimise.state.ChooseObject@24c
constraint chooseobj_588 in {4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34};

var {5,8,11,14,17,20,23,26,29,32,35}: items_597; %ref optimise.state.ChooseObject@24c.items -6
% doing constraints for lookup query: ref optimise.state.ChooseObject@24c.items -6
var 1..11: iitems_597;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_588][iitems_597] = chooseobj_588;
constraint ((chooseobj_588 = 4)) -> iitems_597 >= 1;
constraint ((chooseobj_588 = 7)) -> iitems_597 >= 2;
constraint ((chooseobj_588 = 10)) -> iitems_597 >= 3;
constraint ((chooseobj_588 = 13)) -> iitems_597 >= 4;
constraint ((chooseobj_588 = 16)) -> iitems_597 >= 5;
constraint ((chooseobj_588 = 19)) -> iitems_597 >= 6;
constraint ((chooseobj_588 = 22)) -> iitems_597 >= 7;
constraint ((chooseobj_588 = 25)) -> iitems_597 >= 8;
constraint ((chooseobj_588 = 28)) -> iitems_597 >= 9;
constraint ((chooseobj_588 = 31)) -> iitems_597 >= 10;
constraint ((chooseobj_588 = 34)) -> iitems_597 >= 11;
constraint items_597 = [5, 8, 11, 14, 17, 20, 23, 26, 29, 32, 35, 35][iitems_597];

var {4,7,10,13,16,19,22,25,28,31,34}: chooseobj_641; %optimise.state.ChooseObject@281
constraint chooseobj_641 in {4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34};

var {5,8,11,14,17,20,23,26,29,32,35}: items_650; %ref optimise.state.ChooseObject@281.items -6
% doing constraints for lookup query: ref optimise.state.ChooseObject@281.items -6
var 1..11: iitems_650;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_641][iitems_650] = chooseobj_641;
constraint ((chooseobj_641 = 4)) -> iitems_650 >= 1;
constraint ((chooseobj_641 = 7)) -> iitems_650 >= 2;
constraint ((chooseobj_641 = 10)) -> iitems_650 >= 3;
constraint ((chooseobj_641 = 13)) -> iitems_650 >= 4;
constraint ((chooseobj_641 = 16)) -> iitems_650 >= 5;
constraint ((chooseobj_641 = 19)) -> iitems_650 >= 6;
constraint ((chooseobj_641 = 22)) -> iitems_650 >= 7;
constraint ((chooseobj_641 = 25)) -> iitems_650 >= 8;
constraint ((chooseobj_641 = 28)) -> iitems_650 >= 9;
constraint ((chooseobj_641 = 31)) -> iitems_650 >= 10;
constraint ((chooseobj_641 = 34)) -> iitems_650 >= 11;
constraint items_650 = [5, 8, 11, 14, 17, 20, 23, 26, 29, 32, 35, 35][iitems_650];

var {16,20}: spaceLeft_660; %ref optimise.state.ChooseObject@281.spaceLeft -7
% doing constraints for lookup query: ref optimise.state.ChooseObject@281.spaceLeft -7
var 1..12: ispaceLeft_660;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_588, chooseobj_641][ispaceLeft_660] = chooseobj_641;
constraint ((chooseobj_641 = 4)) -> ispaceLeft_660 >= 1;
constraint ((chooseobj_641 = 7)) -> ispaceLeft_660 >= 2;
constraint ((chooseobj_641 = 10)) -> ispaceLeft_660 >= 3;
constraint ((chooseobj_641 = 13)) -> ispaceLeft_660 >= 4;
constraint ((chooseobj_641 = 16)) -> ispaceLeft_660 >= 5;
constraint ((chooseobj_641 = 19)) -> ispaceLeft_660 >= 6;
constraint ((chooseobj_641 = 22)) -> ispaceLeft_660 >= 7;
constraint ((chooseobj_641 = 25)) -> ispaceLeft_660 >= 8;
constraint ((chooseobj_641 = 28)) -> ispaceLeft_660 >= 9;
constraint ((chooseobj_641 = 31)) -> ispaceLeft_660 >= 10;
constraint ((chooseobj_641 = 34)) -> ispaceLeft_660 >= 11;
constraint ((chooseobj_641 = chooseobj_588)) -> ispaceLeft_660 >= 12;
constraint spaceLeft_660 = [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 16, 20][ispaceLeft_660];

var {15,19}: Subtract_664 = (spaceLeft_660 - 1);

var {4,7,10,13,16,19,22,25,28,31,34}: chooseobj_694; %optimise.state.ChooseObject@2b6
constraint chooseobj_694 in {4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34};

var {5,8,11,14,17,20,23,26,29,32,35}: items_703; %ref optimise.state.ChooseObject@2b6.items -6
% doing constraints for lookup query: ref optimise.state.ChooseObject@2b6.items -6
var 1..11: iitems_703;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_694][iitems_703] = chooseobj_694;
constraint ((chooseobj_694 = 4)) -> iitems_703 >= 1;
constraint ((chooseobj_694 = 7)) -> iitems_703 >= 2;
constraint ((chooseobj_694 = 10)) -> iitems_703 >= 3;
constraint ((chooseobj_694 = 13)) -> iitems_703 >= 4;
constraint ((chooseobj_694 = 16)) -> iitems_703 >= 5;
constraint ((chooseobj_694 = 19)) -> iitems_703 >= 6;
constraint ((chooseobj_694 = 22)) -> iitems_703 >= 7;
constraint ((chooseobj_694 = 25)) -> iitems_703 >= 8;
constraint ((chooseobj_694 = 28)) -> iitems_703 >= 9;
constraint ((chooseobj_694 = 31)) -> iitems_703 >= 10;
constraint ((chooseobj_694 = 34)) -> iitems_703 >= 11;
constraint items_703 = [5, 8, 11, 14, 17, 20, 23, 26, 29, 32, 35, 35][iitems_703];

var {15,16,19,20}: spaceLeft_713; %ref optimise.state.ChooseObject@2b6.spaceLeft -7
% doing constraints for lookup query: ref optimise.state.ChooseObject@2b6.spaceLeft -7
var 1..13: ispaceLeft_713;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_588, chooseobj_641, chooseobj_694][ispaceLeft_713] = chooseobj_694;
constraint ((chooseobj_694 = 4)) -> ispaceLeft_713 >= 1;
constraint ((chooseobj_694 = 7)) -> ispaceLeft_713 >= 2;
constraint ((chooseobj_694 = 10)) -> ispaceLeft_713 >= 3;
constraint ((chooseobj_694 = 13)) -> ispaceLeft_713 >= 4;
constraint ((chooseobj_694 = 16)) -> ispaceLeft_713 >= 5;
constraint ((chooseobj_694 = 19)) -> ispaceLeft_713 >= 6;
constraint ((chooseobj_694 = 22)) -> ispaceLeft_713 >= 7;
constraint ((chooseobj_694 = 25)) -> ispaceLeft_713 >= 8;
constraint ((chooseobj_694 = 28)) -> ispaceLeft_713 >= 9;
constraint ((chooseobj_694 = 31)) -> ispaceLeft_713 >= 10;
constraint ((chooseobj_694 = 34)) -> ispaceLeft_713 >= 11;
constraint ((chooseobj_694 = chooseobj_588)) -> ispaceLeft_713 >= 12;
constraint ((chooseobj_694 = chooseobj_641)) -> ispaceLeft_713 >= 13;
constraint spaceLeft_713 = [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 16, Subtract_664, 20][ispaceLeft_713];

var {7,8,11,12}: Subtract_717 = (spaceLeft_713 - 8);

var {4,7,10,13,16,19,22,25,28,31,34}: chooseobj_747; %optimise.state.ChooseObject@2eb
constraint chooseobj_747 in {4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34};

var {5,8,11,14,17,20,23,26,29,32,35}: items_756; %ref optimise.state.ChooseObject@2eb.items -6
% doing constraints for lookup query: ref optimise.state.ChooseObject@2eb.items -6
var 1..11: iitems_756;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_747][iitems_756] = chooseobj_747;
constraint ((chooseobj_747 = 4)) -> iitems_756 >= 1;
constraint ((chooseobj_747 = 7)) -> iitems_756 >= 2;
constraint ((chooseobj_747 = 10)) -> iitems_756 >= 3;
constraint ((chooseobj_747 = 13)) -> iitems_756 >= 4;
constraint ((chooseobj_747 = 16)) -> iitems_756 >= 5;
constraint ((chooseobj_747 = 19)) -> iitems_756 >= 6;
constraint ((chooseobj_747 = 22)) -> iitems_756 >= 7;
constraint ((chooseobj_747 = 25)) -> iitems_756 >= 8;
constraint ((chooseobj_747 = 28)) -> iitems_756 >= 9;
constraint ((chooseobj_747 = 31)) -> iitems_756 >= 10;
constraint ((chooseobj_747 = 34)) -> iitems_756 >= 11;
constraint items_756 = [5, 8, 11, 14, 17, 20, 23, 26, 29, 32, 35, 35][iitems_756];

var {7,8,11,12,15,16,19,20}: spaceLeft_766; %ref optimise.state.ChooseObject@2eb.spaceLeft -7
% doing constraints for lookup query: ref optimise.state.ChooseObject@2eb.spaceLeft -7
var 1..14: ispaceLeft_766;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747][ispaceLeft_766] = chooseobj_747;
constraint ((chooseobj_747 = 4)) -> ispaceLeft_766 >= 1;
constraint ((chooseobj_747 = 7)) -> ispaceLeft_766 >= 2;
constraint ((chooseobj_747 = 10)) -> ispaceLeft_766 >= 3;
constraint ((chooseobj_747 = 13)) -> ispaceLeft_766 >= 4;
constraint ((chooseobj_747 = 16)) -> ispaceLeft_766 >= 5;
constraint ((chooseobj_747 = 19)) -> ispaceLeft_766 >= 6;
constraint ((chooseobj_747 = 22)) -> ispaceLeft_766 >= 7;
constraint ((chooseobj_747 = 25)) -> ispaceLeft_766 >= 8;
constraint ((chooseobj_747 = 28)) -> ispaceLeft_766 >= 9;
constraint ((chooseobj_747 = 31)) -> ispaceLeft_766 >= 10;
constraint ((chooseobj_747 = 34)) -> ispaceLeft_766 >= 11;
constraint ((chooseobj_747 = chooseobj_588)) -> ispaceLeft_766 >= 12;
constraint ((chooseobj_747 = chooseobj_641)) -> ispaceLeft_766 >= 13;
constraint ((chooseobj_747 = chooseobj_694)) -> ispaceLeft_766 >= 14;
constraint spaceLeft_766 = [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 16, Subtract_664, Subtract_717, 20][ispaceLeft_766];

var {-1,0,3,4,7,8,11,12}: Subtract_770 = (spaceLeft_766 - 8);

var {4,7,10,13,16,19,22,25,28,31,34}: chooseobj_800; %optimise.state.ChooseObject@320
constraint chooseobj_800 in {4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34};

var {5,8,11,14,17,20,23,26,29,32,35}: items_809; %ref optimise.state.ChooseObject@320.items -6
% doing constraints for lookup query: ref optimise.state.ChooseObject@320.items -6
var 1..11: iitems_809;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_800][iitems_809] = chooseobj_800;
constraint ((chooseobj_800 = 4)) -> iitems_809 >= 1;
constraint ((chooseobj_800 = 7)) -> iitems_809 >= 2;
constraint ((chooseobj_800 = 10)) -> iitems_809 >= 3;
constraint ((chooseobj_800 = 13)) -> iitems_809 >= 4;
constraint ((chooseobj_800 = 16)) -> iitems_809 >= 5;
constraint ((chooseobj_800 = 19)) -> iitems_809 >= 6;
constraint ((chooseobj_800 = 22)) -> iitems_809 >= 7;
constraint ((chooseobj_800 = 25)) -> iitems_809 >= 8;
constraint ((chooseobj_800 = 28)) -> iitems_809 >= 9;
constraint ((chooseobj_800 = 31)) -> iitems_809 >= 10;
constraint ((chooseobj_800 = 34)) -> iitems_809 >= 11;
constraint items_809 = [5, 8, 11, 14, 17, 20, 23, 26, 29, 32, 35, 35][iitems_809];

var {-1,0,3,4,7,8,11,12,15,16,19,20}: spaceLeft_819; %ref optimise.state.ChooseObject@320.spaceLeft -7
% doing constraints for lookup query: ref optimise.state.ChooseObject@320.spaceLeft -7
var 1..15: ispaceLeft_819;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800][ispaceLeft_819] = chooseobj_800;
constraint ((chooseobj_800 = 4)) -> ispaceLeft_819 >= 1;
constraint ((chooseobj_800 = 7)) -> ispaceLeft_819 >= 2;
constraint ((chooseobj_800 = 10)) -> ispaceLeft_819 >= 3;
constraint ((chooseobj_800 = 13)) -> ispaceLeft_819 >= 4;
constraint ((chooseobj_800 = 16)) -> ispaceLeft_819 >= 5;
constraint ((chooseobj_800 = 19)) -> ispaceLeft_819 >= 6;
constraint ((chooseobj_800 = 22)) -> ispaceLeft_819 >= 7;
constraint ((chooseobj_800 = 25)) -> ispaceLeft_819 >= 8;
constraint ((chooseobj_800 = 28)) -> ispaceLeft_819 >= 9;
constraint ((chooseobj_800 = 31)) -> ispaceLeft_819 >= 10;
constraint ((chooseobj_800 = 34)) -> ispaceLeft_819 >= 11;
constraint ((chooseobj_800 = chooseobj_588)) -> ispaceLeft_819 >= 12;
constraint ((chooseobj_800 = chooseobj_641)) -> ispaceLeft_819 >= 13;
constraint ((chooseobj_800 = chooseobj_694)) -> ispaceLeft_819 >= 14;
constraint ((chooseobj_800 = chooseobj_747)) -> ispaceLeft_819 >= 15;
constraint spaceLeft_819 = [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 16, Subtract_664, Subtract_717, Subtract_770, 20][ispaceLeft_819];

var {-11,-10,-7,-6,-3,-2,1,2,5,6,9,10}: Subtract_823 = (spaceLeft_819 - 10);

var {4,7,10,13,16,19,22,25,28,31,34}: chooseobj_853; %optimise.state.ChooseObject@355
constraint chooseobj_853 in {4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34};

var {5,8,11,14,17,20,23,26,29,32,35}: items_862; %ref optimise.state.ChooseObject@355.items -6
% doing constraints for lookup query: ref optimise.state.ChooseObject@355.items -6
var 1..11: iitems_862;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_853][iitems_862] = chooseobj_853;
constraint ((chooseobj_853 = 4)) -> iitems_862 >= 1;
constraint ((chooseobj_853 = 7)) -> iitems_862 >= 2;
constraint ((chooseobj_853 = 10)) -> iitems_862 >= 3;
constraint ((chooseobj_853 = 13)) -> iitems_862 >= 4;
constraint ((chooseobj_853 = 16)) -> iitems_862 >= 5;
constraint ((chooseobj_853 = 19)) -> iitems_862 >= 6;
constraint ((chooseobj_853 = 22)) -> iitems_862 >= 7;
constraint ((chooseobj_853 = 25)) -> iitems_862 >= 8;
constraint ((chooseobj_853 = 28)) -> iitems_862 >= 9;
constraint ((chooseobj_853 = 31)) -> iitems_862 >= 10;
constraint ((chooseobj_853 = 34)) -> iitems_862 >= 11;
constraint items_862 = [5, 8, 11, 14, 17, 20, 23, 26, 29, 32, 35, 35][iitems_862];

var {-11,-10,-7,-6,-3,-2,-1,0,1,2,3,4,5,6,7,8,9,10,11,12,15,16,19,20}: spaceLeft_872; %ref optimise.state.ChooseObject@355.spaceLeft -7
% doing constraints for lookup query: ref optimise.state.ChooseObject@355.spaceLeft -7
var 1..16: ispaceLeft_872;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853][ispaceLeft_872] = chooseobj_853;
constraint ((chooseobj_853 = 4)) -> ispaceLeft_872 >= 1;
constraint ((chooseobj_853 = 7)) -> ispaceLeft_872 >= 2;
constraint ((chooseobj_853 = 10)) -> ispaceLeft_872 >= 3;
constraint ((chooseobj_853 = 13)) -> ispaceLeft_872 >= 4;
constraint ((chooseobj_853 = 16)) -> ispaceLeft_872 >= 5;
constraint ((chooseobj_853 = 19)) -> ispaceLeft_872 >= 6;
constraint ((chooseobj_853 = 22)) -> ispaceLeft_872 >= 7;
constraint ((chooseobj_853 = 25)) -> ispaceLeft_872 >= 8;
constraint ((chooseobj_853 = 28)) -> ispaceLeft_872 >= 9;
constraint ((chooseobj_853 = 31)) -> ispaceLeft_872 >= 10;
constraint ((chooseobj_853 = 34)) -> ispaceLeft_872 >= 11;
constraint ((chooseobj_853 = chooseobj_588)) -> ispaceLeft_872 >= 12;
constraint ((chooseobj_853 = chooseobj_641)) -> ispaceLeft_872 >= 13;
constraint ((chooseobj_853 = chooseobj_694)) -> ispaceLeft_872 >= 14;
constraint ((chooseobj_853 = chooseobj_747)) -> ispaceLeft_872 >= 15;
constraint ((chooseobj_853 = chooseobj_800)) -> ispaceLeft_872 >= 16;
constraint spaceLeft_872 = [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 16, Subtract_664, Subtract_717, Subtract_770, Subtract_823, 20][ispaceLeft_872];

var {-12,-11,-8,-7,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8,9,10,11,14,15,18,19}: Subtract_876 = (spaceLeft_872 - 1);

var {4,7,10,13,16,19,22,25,28,31,34}: chooseobj_906; %optimise.state.ChooseObject@38a
constraint chooseobj_906 in {4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34};

var {5,8,11,14,17,20,23,26,29,32,35}: items_915; %ref optimise.state.ChooseObject@38a.items -6
% doing constraints for lookup query: ref optimise.state.ChooseObject@38a.items -6
var 1..11: iitems_915;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_906][iitems_915] = chooseobj_906;
constraint ((chooseobj_906 = 4)) -> iitems_915 >= 1;
constraint ((chooseobj_906 = 7)) -> iitems_915 >= 2;
constraint ((chooseobj_906 = 10)) -> iitems_915 >= 3;
constraint ((chooseobj_906 = 13)) -> iitems_915 >= 4;
constraint ((chooseobj_906 = 16)) -> iitems_915 >= 5;
constraint ((chooseobj_906 = 19)) -> iitems_915 >= 6;
constraint ((chooseobj_906 = 22)) -> iitems_915 >= 7;
constraint ((chooseobj_906 = 25)) -> iitems_915 >= 8;
constraint ((chooseobj_906 = 28)) -> iitems_915 >= 9;
constraint ((chooseobj_906 = 31)) -> iitems_915 >= 10;
constraint ((chooseobj_906 = 34)) -> iitems_915 >= 11;
constraint items_915 = [5, 8, 11, 14, 17, 20, 23, 26, 29, 32, 35, 35][iitems_915];

var {-12,-11,-10,-8,-7,-6,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8,9,10,11,12,14,15,16,18,19,20}: spaceLeft_925; %ref optimise.state.ChooseObject@38a.spaceLeft -7
% doing constraints for lookup query: ref optimise.state.ChooseObject@38a.spaceLeft -7
var 1..17: ispaceLeft_925;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853, chooseobj_906][ispaceLeft_925] = chooseobj_906;
constraint ((chooseobj_906 = 4)) -> ispaceLeft_925 >= 1;
constraint ((chooseobj_906 = 7)) -> ispaceLeft_925 >= 2;
constraint ((chooseobj_906 = 10)) -> ispaceLeft_925 >= 3;
constraint ((chooseobj_906 = 13)) -> ispaceLeft_925 >= 4;
constraint ((chooseobj_906 = 16)) -> ispaceLeft_925 >= 5;
constraint ((chooseobj_906 = 19)) -> ispaceLeft_925 >= 6;
constraint ((chooseobj_906 = 22)) -> ispaceLeft_925 >= 7;
constraint ((chooseobj_906 = 25)) -> ispaceLeft_925 >= 8;
constraint ((chooseobj_906 = 28)) -> ispaceLeft_925 >= 9;
constraint ((chooseobj_906 = 31)) -> ispaceLeft_925 >= 10;
constraint ((chooseobj_906 = 34)) -> ispaceLeft_925 >= 11;
constraint ((chooseobj_906 = chooseobj_588)) -> ispaceLeft_925 >= 12;
constraint ((chooseobj_906 = chooseobj_641)) -> ispaceLeft_925 >= 13;
constraint ((chooseobj_906 = chooseobj_694)) -> ispaceLeft_925 >= 14;
constraint ((chooseobj_906 = chooseobj_747)) -> ispaceLeft_925 >= 15;
constraint ((chooseobj_906 = chooseobj_800)) -> ispaceLeft_925 >= 16;
constraint ((chooseobj_906 = chooseobj_853)) -> ispaceLeft_925 >= 17;
constraint spaceLeft_925 = [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 16, Subtract_664, Subtract_717, Subtract_770, Subtract_823, Subtract_876, 20][ispaceLeft_925];

var {-17,-16,-15,-13,-12,-11,-9,-8,-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,9,10,11,13,14,15}: Subtract_929 = (spaceLeft_925 - 5);

var {4,7,10,13,16,19,22,25,28,31,34}: chooseobj_959; %optimise.state.ChooseObject@3bf
constraint chooseobj_959 in {4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34};

var {5,8,11,14,17,20,23,26,29,32,35}: items_968; %ref optimise.state.ChooseObject@3bf.items -6
% doing constraints for lookup query: ref optimise.state.ChooseObject@3bf.items -6
var 1..11: iitems_968;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_959][iitems_968] = chooseobj_959;
constraint ((chooseobj_959 = 4)) -> iitems_968 >= 1;
constraint ((chooseobj_959 = 7)) -> iitems_968 >= 2;
constraint ((chooseobj_959 = 10)) -> iitems_968 >= 3;
constraint ((chooseobj_959 = 13)) -> iitems_968 >= 4;
constraint ((chooseobj_959 = 16)) -> iitems_968 >= 5;
constraint ((chooseobj_959 = 19)) -> iitems_968 >= 6;
constraint ((chooseobj_959 = 22)) -> iitems_968 >= 7;
constraint ((chooseobj_959 = 25)) -> iitems_968 >= 8;
constraint ((chooseobj_959 = 28)) -> iitems_968 >= 9;
constraint ((chooseobj_959 = 31)) -> iitems_968 >= 10;
constraint ((chooseobj_959 = 34)) -> iitems_968 >= 11;
constraint items_968 = [5, 8, 11, 14, 17, 20, 23, 26, 29, 32, 35, 35][iitems_968];

var {-17,-16,-15,-13,-12,-11,-10,-9,-8,-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,18,19,20}: spaceLeft_978; %ref optimise.state.ChooseObject@3bf.spaceLeft -7
% doing constraints for lookup query: ref optimise.state.ChooseObject@3bf.spaceLeft -7
var 1..18: ispaceLeft_978;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853, chooseobj_906, chooseobj_959][ispaceLeft_978] = chooseobj_959;
constraint ((chooseobj_959 = 4)) -> ispaceLeft_978 >= 1;
constraint ((chooseobj_959 = 7)) -> ispaceLeft_978 >= 2;
constraint ((chooseobj_959 = 10)) -> ispaceLeft_978 >= 3;
constraint ((chooseobj_959 = 13)) -> ispaceLeft_978 >= 4;
constraint ((chooseobj_959 = 16)) -> ispaceLeft_978 >= 5;
constraint ((chooseobj_959 = 19)) -> ispaceLeft_978 >= 6;
constraint ((chooseobj_959 = 22)) -> ispaceLeft_978 >= 7;
constraint ((chooseobj_959 = 25)) -> ispaceLeft_978 >= 8;
constraint ((chooseobj_959 = 28)) -> ispaceLeft_978 >= 9;
constraint ((chooseobj_959 = 31)) -> ispaceLeft_978 >= 10;
constraint ((chooseobj_959 = 34)) -> ispaceLeft_978 >= 11;
constraint ((chooseobj_959 = chooseobj_588)) -> ispaceLeft_978 >= 12;
constraint ((chooseobj_959 = chooseobj_641)) -> ispaceLeft_978 >= 13;
constraint ((chooseobj_959 = chooseobj_694)) -> ispaceLeft_978 >= 14;
constraint ((chooseobj_959 = chooseobj_747)) -> ispaceLeft_978 >= 15;
constraint ((chooseobj_959 = chooseobj_800)) -> ispaceLeft_978 >= 16;
constraint ((chooseobj_959 = chooseobj_853)) -> ispaceLeft_978 >= 17;
constraint ((chooseobj_959 = chooseobj_906)) -> ispaceLeft_978 >= 18;
constraint spaceLeft_978 = [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 16, Subtract_664, Subtract_717, Subtract_770, Subtract_823, Subtract_876, Subtract_929, 20][ispaceLeft_978];

var {-20,-19,-18,-16,-15,-14,-13,-12,-11,-10,-9,-8,-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8,9,10,11,12,13,15,16,17}: Subtract_982 = (spaceLeft_978 - 3);

var {4,7,10,13,16,19,22,25,28,31,34}: chooseobj_1012; %optimise.state.ChooseObject@3f4
constraint chooseobj_1012 in {4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34};

var {5,8,11,14,17,20,23,26,29,32,35}: items_1021; %ref optimise.state.ChooseObject@3f4.items -6
% doing constraints for lookup query: ref optimise.state.ChooseObject@3f4.items -6
var 1..11: iitems_1021;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_1012][iitems_1021] = chooseobj_1012;
constraint ((chooseobj_1012 = 4)) -> iitems_1021 >= 1;
constraint ((chooseobj_1012 = 7)) -> iitems_1021 >= 2;
constraint ((chooseobj_1012 = 10)) -> iitems_1021 >= 3;
constraint ((chooseobj_1012 = 13)) -> iitems_1021 >= 4;
constraint ((chooseobj_1012 = 16)) -> iitems_1021 >= 5;
constraint ((chooseobj_1012 = 19)) -> iitems_1021 >= 6;
constraint ((chooseobj_1012 = 22)) -> iitems_1021 >= 7;
constraint ((chooseobj_1012 = 25)) -> iitems_1021 >= 8;
constraint ((chooseobj_1012 = 28)) -> iitems_1021 >= 9;
constraint ((chooseobj_1012 = 31)) -> iitems_1021 >= 10;
constraint ((chooseobj_1012 = 34)) -> iitems_1021 >= 11;
constraint items_1021 = [5, 8, 11, 14, 17, 20, 23, 26, 29, 32, 35, 35][iitems_1021];

var -20..20: spaceLeft_1031; %ref optimise.state.ChooseObject@3f4.spaceLeft -7
% doing constraints for lookup query: ref optimise.state.ChooseObject@3f4.spaceLeft -7
var 1..19: ispaceLeft_1031;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853, chooseobj_906, chooseobj_959, chooseobj_1012][ispaceLeft_1031] = chooseobj_1012;
constraint ((chooseobj_1012 = 4)) -> ispaceLeft_1031 >= 1;
constraint ((chooseobj_1012 = 7)) -> ispaceLeft_1031 >= 2;
constraint ((chooseobj_1012 = 10)) -> ispaceLeft_1031 >= 3;
constraint ((chooseobj_1012 = 13)) -> ispaceLeft_1031 >= 4;
constraint ((chooseobj_1012 = 16)) -> ispaceLeft_1031 >= 5;
constraint ((chooseobj_1012 = 19)) -> ispaceLeft_1031 >= 6;
constraint ((chooseobj_1012 = 22)) -> ispaceLeft_1031 >= 7;
constraint ((chooseobj_1012 = 25)) -> ispaceLeft_1031 >= 8;
constraint ((chooseobj_1012 = 28)) -> ispaceLeft_1031 >= 9;
constraint ((chooseobj_1012 = 31)) -> ispaceLeft_1031 >= 10;
constraint ((chooseobj_1012 = 34)) -> ispaceLeft_1031 >= 11;
constraint ((chooseobj_1012 = chooseobj_588)) -> ispaceLeft_1031 >= 12;
constraint ((chooseobj_1012 = chooseobj_641)) -> ispaceLeft_1031 >= 13;
constraint ((chooseobj_1012 = chooseobj_694)) -> ispaceLeft_1031 >= 14;
constraint ((chooseobj_1012 = chooseobj_747)) -> ispaceLeft_1031 >= 15;
constraint ((chooseobj_1012 = chooseobj_800)) -> ispaceLeft_1031 >= 16;
constraint ((chooseobj_1012 = chooseobj_853)) -> ispaceLeft_1031 >= 17;
constraint ((chooseobj_1012 = chooseobj_906)) -> ispaceLeft_1031 >= 18;
constraint ((chooseobj_1012 = chooseobj_959)) -> ispaceLeft_1031 >= 19;
constraint spaceLeft_1031 = [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 16, Subtract_664, Subtract_717, Subtract_770, Subtract_823, Subtract_876, Subtract_929, Subtract_982, 20][ispaceLeft_1031];

var -28..12: Subtract_1035 = (spaceLeft_1031 - 8);

var {4,7,10,13,16,19,22,25,28,31,34}: chooseobj_1065; %optimise.state.ChooseObject@429
constraint chooseobj_1065 in {4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34};

var {5,8,11,14,17,20,23,26,29,32,35}: items_1074; %ref optimise.state.ChooseObject@429.items -6
% doing constraints for lookup query: ref optimise.state.ChooseObject@429.items -6
var 1..11: iitems_1074;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_1065][iitems_1074] = chooseobj_1065;
constraint ((chooseobj_1065 = 4)) -> iitems_1074 >= 1;
constraint ((chooseobj_1065 = 7)) -> iitems_1074 >= 2;
constraint ((chooseobj_1065 = 10)) -> iitems_1074 >= 3;
constraint ((chooseobj_1065 = 13)) -> iitems_1074 >= 4;
constraint ((chooseobj_1065 = 16)) -> iitems_1074 >= 5;
constraint ((chooseobj_1065 = 19)) -> iitems_1074 >= 6;
constraint ((chooseobj_1065 = 22)) -> iitems_1074 >= 7;
constraint ((chooseobj_1065 = 25)) -> iitems_1074 >= 8;
constraint ((chooseobj_1065 = 28)) -> iitems_1074 >= 9;
constraint ((chooseobj_1065 = 31)) -> iitems_1074 >= 10;
constraint ((chooseobj_1065 = 34)) -> iitems_1074 >= 11;
constraint items_1074 = [5, 8, 11, 14, 17, 20, 23, 26, 29, 32, 35, 35][iitems_1074];

var -28..20: spaceLeft_1084; %ref optimise.state.ChooseObject@429.spaceLeft -7
% doing constraints for lookup query: ref optimise.state.ChooseObject@429.spaceLeft -7
var 1..20: ispaceLeft_1084;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853, chooseobj_906, chooseobj_959, chooseobj_1012, chooseobj_1065][ispaceLeft_1084] = chooseobj_1065;
constraint ((chooseobj_1065 = 4)) -> ispaceLeft_1084 >= 1;
constraint ((chooseobj_1065 = 7)) -> ispaceLeft_1084 >= 2;
constraint ((chooseobj_1065 = 10)) -> ispaceLeft_1084 >= 3;
constraint ((chooseobj_1065 = 13)) -> ispaceLeft_1084 >= 4;
constraint ((chooseobj_1065 = 16)) -> ispaceLeft_1084 >= 5;
constraint ((chooseobj_1065 = 19)) -> ispaceLeft_1084 >= 6;
constraint ((chooseobj_1065 = 22)) -> ispaceLeft_1084 >= 7;
constraint ((chooseobj_1065 = 25)) -> ispaceLeft_1084 >= 8;
constraint ((chooseobj_1065 = 28)) -> ispaceLeft_1084 >= 9;
constraint ((chooseobj_1065 = 31)) -> ispaceLeft_1084 >= 10;
constraint ((chooseobj_1065 = 34)) -> ispaceLeft_1084 >= 11;
constraint ((chooseobj_1065 = chooseobj_588)) -> ispaceLeft_1084 >= 12;
constraint ((chooseobj_1065 = chooseobj_641)) -> ispaceLeft_1084 >= 13;
constraint ((chooseobj_1065 = chooseobj_694)) -> ispaceLeft_1084 >= 14;
constraint ((chooseobj_1065 = chooseobj_747)) -> ispaceLeft_1084 >= 15;
constraint ((chooseobj_1065 = chooseobj_800)) -> ispaceLeft_1084 >= 16;
constraint ((chooseobj_1065 = chooseobj_853)) -> ispaceLeft_1084 >= 17;
constraint ((chooseobj_1065 = chooseobj_906)) -> ispaceLeft_1084 >= 18;
constraint ((chooseobj_1065 = chooseobj_959)) -> ispaceLeft_1084 >= 19;
constraint ((chooseobj_1065 = chooseobj_1012)) -> ispaceLeft_1084 >= 20;
constraint spaceLeft_1084 = [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 16, Subtract_664, Subtract_717, Subtract_770, Subtract_823, Subtract_876, Subtract_929, Subtract_982, Subtract_1035, 20][ispaceLeft_1084];

var -34..14: Subtract_1088 = (spaceLeft_1084 - 6);

var {4,7,10,13,16,19,22,25,28,31,34}: chooseobj_1118; %optimise.state.ChooseObject@45e
constraint chooseobj_1118 in {4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34};

var {5,8,11,14,17,20,23,26,29,32,35}: items_1127; %ref optimise.state.ChooseObject@45e.items -6
% doing constraints for lookup query: ref optimise.state.ChooseObject@45e.items -6
var 1..11: iitems_1127;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_1118][iitems_1127] = chooseobj_1118;
constraint ((chooseobj_1118 = 4)) -> iitems_1127 >= 1;
constraint ((chooseobj_1118 = 7)) -> iitems_1127 >= 2;
constraint ((chooseobj_1118 = 10)) -> iitems_1127 >= 3;
constraint ((chooseobj_1118 = 13)) -> iitems_1127 >= 4;
constraint ((chooseobj_1118 = 16)) -> iitems_1127 >= 5;
constraint ((chooseobj_1118 = 19)) -> iitems_1127 >= 6;
constraint ((chooseobj_1118 = 22)) -> iitems_1127 >= 7;
constraint ((chooseobj_1118 = 25)) -> iitems_1127 >= 8;
constraint ((chooseobj_1118 = 28)) -> iitems_1127 >= 9;
constraint ((chooseobj_1118 = 31)) -> iitems_1127 >= 10;
constraint ((chooseobj_1118 = 34)) -> iitems_1127 >= 11;
constraint items_1127 = [5, 8, 11, 14, 17, 20, 23, 26, 29, 32, 35, 35][iitems_1127];

var -34..20: spaceLeft_1137; %ref optimise.state.ChooseObject@45e.spaceLeft -7
% doing constraints for lookup query: ref optimise.state.ChooseObject@45e.spaceLeft -7
var 1..21: ispaceLeft_1137;
constraint [4, 7, 10, 13, 16, 19, 22, 25, 28, 31, 34, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853, chooseobj_906, chooseobj_959, chooseobj_1012, chooseobj_1065, chooseobj_1118][ispaceLeft_1137] = chooseobj_1118;
constraint ((chooseobj_1118 = 4)) -> ispaceLeft_1137 >= 1;
constraint ((chooseobj_1118 = 7)) -> ispaceLeft_1137 >= 2;
constraint ((chooseobj_1118 = 10)) -> ispaceLeft_1137 >= 3;
constraint ((chooseobj_1118 = 13)) -> ispaceLeft_1137 >= 4;
constraint ((chooseobj_1118 = 16)) -> ispaceLeft_1137 >= 5;
constraint ((chooseobj_1118 = 19)) -> ispaceLeft_1137 >= 6;
constraint ((chooseobj_1118 = 22)) -> ispaceLeft_1137 >= 7;
constraint ((chooseobj_1118 = 25)) -> ispaceLeft_1137 >= 8;
constraint ((chooseobj_1118 = 28)) -> ispaceLeft_1137 >= 9;
constraint ((chooseobj_1118 = 31)) -> ispaceLeft_1137 >= 10;
constraint ((chooseobj_1118 = 34)) -> ispaceLeft_1137 >= 11;
constraint ((chooseobj_1118 = chooseobj_588)) -> ispaceLeft_1137 >= 12;
constraint ((chooseobj_1118 = chooseobj_641)) -> ispaceLeft_1137 >= 13;
constraint ((chooseobj_1118 = chooseobj_694)) -> ispaceLeft_1137 >= 14;
constraint ((chooseobj_1118 = chooseobj_747)) -> ispaceLeft_1137 >= 15;
constraint ((chooseobj_1118 = chooseobj_800)) -> ispaceLeft_1137 >= 16;
constraint ((chooseobj_1118 = chooseobj_853)) -> ispaceLeft_1137 >= 17;
constraint ((chooseobj_1118 = chooseobj_906)) -> ispaceLeft_1137 >= 18;
constraint ((chooseobj_1118 = chooseobj_959)) -> ispaceLeft_1137 >= 19;
constraint ((chooseobj_1118 = chooseobj_1012)) -> ispaceLeft_1137 >= 20;
constraint ((chooseobj_1118 = chooseobj_1065)) -> ispaceLeft_1137 >= 21;
constraint spaceLeft_1137 = [20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 20, 16, Subtract_664, Subtract_717, Subtract_770, Subtract_823, Subtract_876, Subtract_929, Subtract_982, Subtract_1035, Subtract_1088, 20][ispaceLeft_1137];

var -35..19: Subtract_1141 = (spaceLeft_1137 - 1);

var -35..20: spaceLeft_1192; %ref ref (Literal: 0 [0]).b -19.spaceLeft -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).b -19.spaceLeft -7
var 1..12: ispaceLeft_1192;
constraint [4, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853, chooseobj_906, chooseobj_959, chooseobj_1012, chooseobj_1065, chooseobj_1118, 4][ispaceLeft_1192] = 4;
constraint (true) -> ispaceLeft_1192 >= 1;
constraint ((4 = chooseobj_588)) -> ispaceLeft_1192 >= 2;
constraint ((4 = chooseobj_641)) -> ispaceLeft_1192 >= 3;
constraint ((4 = chooseobj_694)) -> ispaceLeft_1192 >= 4;
constraint ((4 = chooseobj_747)) -> ispaceLeft_1192 >= 5;
constraint ((4 = chooseobj_800)) -> ispaceLeft_1192 >= 6;
constraint ((4 = chooseobj_853)) -> ispaceLeft_1192 >= 7;
constraint ((4 = chooseobj_906)) -> ispaceLeft_1192 >= 8;
constraint ((4 = chooseobj_959)) -> ispaceLeft_1192 >= 9;
constraint ((4 = chooseobj_1012)) -> ispaceLeft_1192 >= 10;
constraint ((4 = chooseobj_1065)) -> ispaceLeft_1192 >= 11;
constraint ((4 = chooseobj_1118)) -> ispaceLeft_1192 >= 12;
constraint spaceLeft_1192 = [20, 16, Subtract_664, Subtract_717, Subtract_770, Subtract_823, Subtract_876, Subtract_929, Subtract_982, Subtract_1035, Subtract_1088, Subtract_1141, 20][ispaceLeft_1192];

var bool: Less_1194 = (spaceLeft_1192 < 0);

var bool: ret_tooFull_1198; %ref (Literal: 0 [0]).ret_tooFull -20
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_tooFull -20
var 1..1: iret_tooFull_1198;
constraint ret_tooFull_1198 = [Less_1194, false][iret_tooFull_1198];

var bool: setempty_1209 = not (((5 = items_597)) \/ ((5 = items_650)) \/ ((5 = items_703)) \/ ((5 = items_756)) \/ ((5 = items_809)) \/ ((5 = items_862)) \/ ((5 = items_915)) \/ ((5 = items_968)) \/ ((5 = items_1021)) \/ ((5 = items_1074)) \/ ((5 = items_1127)));

var bool: ret_isEmpty_1213; %ref (Literal: 0 [0]).ret_isEmpty -21
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_isEmpty -21
var 1..1: iret_isEmpty_1213;
constraint ret_isEmpty_1213 = [setempty_1209, false][iret_isEmpty_1213];

var bool: notret_isEmpty_1213 = not ret_isEmpty_1213;

var -35..20: spaceLeft_1252; %ref ref (Literal: 0 [0]).b -19.spaceLeft -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).b -19.spaceLeft -7
var 1..12: ispaceLeft_1252;
constraint [7, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853, chooseobj_906, chooseobj_959, chooseobj_1012, chooseobj_1065, chooseobj_1118, 7][ispaceLeft_1252] = 7;
constraint (true) -> ispaceLeft_1252 >= 1;
constraint ((7 = chooseobj_588)) -> ispaceLeft_1252 >= 2;
constraint ((7 = chooseobj_641)) -> ispaceLeft_1252 >= 3;
constraint ((7 = chooseobj_694)) -> ispaceLeft_1252 >= 4;
constraint ((7 = chooseobj_747)) -> ispaceLeft_1252 >= 5;
constraint ((7 = chooseobj_800)) -> ispaceLeft_1252 >= 6;
constraint ((7 = chooseobj_853)) -> ispaceLeft_1252 >= 7;
constraint ((7 = chooseobj_906)) -> ispaceLeft_1252 >= 8;
constraint ((7 = chooseobj_959)) -> ispaceLeft_1252 >= 9;
constraint ((7 = chooseobj_1012)) -> ispaceLeft_1252 >= 10;
constraint ((7 = chooseobj_1065)) -> ispaceLeft_1252 >= 11;
constraint ((7 = chooseobj_1118)) -> ispaceLeft_1252 >= 12;
constraint spaceLeft_1252 = [20, 16, Subtract_664, Subtract_717, Subtract_770, Subtract_823, Subtract_876, Subtract_929, Subtract_982, Subtract_1035, Subtract_1088, Subtract_1141, 20][ispaceLeft_1252];

var bool: Less_1254 = (spaceLeft_1252 < 0);

var bool: ret_tooFull_1258; %ref (Literal: 0 [0]).ret_tooFull -20
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_tooFull -20
var 1..1: iret_tooFull_1258;
constraint ret_tooFull_1258 = [Less_1254, false][iret_tooFull_1258];

var bool: setempty_1269 = not (((8 = items_597)) \/ ((8 = items_650)) \/ ((8 = items_703)) \/ ((8 = items_756)) \/ ((8 = items_809)) \/ ((8 = items_862)) \/ ((8 = items_915)) \/ ((8 = items_968)) \/ ((8 = items_1021)) \/ ((8 = items_1074)) \/ ((8 = items_1127)));

var bool: ret_isEmpty_1273; %ref (Literal: 0 [0]).ret_isEmpty -21
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_isEmpty -21
var 1..1: iret_isEmpty_1273;
constraint ret_isEmpty_1273 = [setempty_1269, false][iret_isEmpty_1273];

var bool: notret_isEmpty_1273 = not ret_isEmpty_1273;

var -35..20: spaceLeft_1312; %ref ref (Literal: 0 [0]).b -19.spaceLeft -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).b -19.spaceLeft -7
var 1..12: ispaceLeft_1312;
constraint [10, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853, chooseobj_906, chooseobj_959, chooseobj_1012, chooseobj_1065, chooseobj_1118, 10][ispaceLeft_1312] = 10;
constraint (true) -> ispaceLeft_1312 >= 1;
constraint ((10 = chooseobj_588)) -> ispaceLeft_1312 >= 2;
constraint ((10 = chooseobj_641)) -> ispaceLeft_1312 >= 3;
constraint ((10 = chooseobj_694)) -> ispaceLeft_1312 >= 4;
constraint ((10 = chooseobj_747)) -> ispaceLeft_1312 >= 5;
constraint ((10 = chooseobj_800)) -> ispaceLeft_1312 >= 6;
constraint ((10 = chooseobj_853)) -> ispaceLeft_1312 >= 7;
constraint ((10 = chooseobj_906)) -> ispaceLeft_1312 >= 8;
constraint ((10 = chooseobj_959)) -> ispaceLeft_1312 >= 9;
constraint ((10 = chooseobj_1012)) -> ispaceLeft_1312 >= 10;
constraint ((10 = chooseobj_1065)) -> ispaceLeft_1312 >= 11;
constraint ((10 = chooseobj_1118)) -> ispaceLeft_1312 >= 12;
constraint spaceLeft_1312 = [20, 16, Subtract_664, Subtract_717, Subtract_770, Subtract_823, Subtract_876, Subtract_929, Subtract_982, Subtract_1035, Subtract_1088, Subtract_1141, 20][ispaceLeft_1312];

var bool: Less_1314 = (spaceLeft_1312 < 0);

var bool: ret_tooFull_1318; %ref (Literal: 0 [0]).ret_tooFull -20
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_tooFull -20
var 1..1: iret_tooFull_1318;
constraint ret_tooFull_1318 = [Less_1314, false][iret_tooFull_1318];

var bool: setempty_1329 = not (((11 = items_597)) \/ ((11 = items_650)) \/ ((11 = items_703)) \/ ((11 = items_756)) \/ ((11 = items_809)) \/ ((11 = items_862)) \/ ((11 = items_915)) \/ ((11 = items_968)) \/ ((11 = items_1021)) \/ ((11 = items_1074)) \/ ((11 = items_1127)));

var bool: ret_isEmpty_1333; %ref (Literal: 0 [0]).ret_isEmpty -21
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_isEmpty -21
var 1..1: iret_isEmpty_1333;
constraint ret_isEmpty_1333 = [setempty_1329, false][iret_isEmpty_1333];

var bool: notret_isEmpty_1333 = not ret_isEmpty_1333;

var -35..20: spaceLeft_1372; %ref ref (Literal: 0 [0]).b -19.spaceLeft -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).b -19.spaceLeft -7
var 1..12: ispaceLeft_1372;
constraint [13, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853, chooseobj_906, chooseobj_959, chooseobj_1012, chooseobj_1065, chooseobj_1118, 13][ispaceLeft_1372] = 13;
constraint (true) -> ispaceLeft_1372 >= 1;
constraint ((13 = chooseobj_588)) -> ispaceLeft_1372 >= 2;
constraint ((13 = chooseobj_641)) -> ispaceLeft_1372 >= 3;
constraint ((13 = chooseobj_694)) -> ispaceLeft_1372 >= 4;
constraint ((13 = chooseobj_747)) -> ispaceLeft_1372 >= 5;
constraint ((13 = chooseobj_800)) -> ispaceLeft_1372 >= 6;
constraint ((13 = chooseobj_853)) -> ispaceLeft_1372 >= 7;
constraint ((13 = chooseobj_906)) -> ispaceLeft_1372 >= 8;
constraint ((13 = chooseobj_959)) -> ispaceLeft_1372 >= 9;
constraint ((13 = chooseobj_1012)) -> ispaceLeft_1372 >= 10;
constraint ((13 = chooseobj_1065)) -> ispaceLeft_1372 >= 11;
constraint ((13 = chooseobj_1118)) -> ispaceLeft_1372 >= 12;
constraint spaceLeft_1372 = [20, 16, Subtract_664, Subtract_717, Subtract_770, Subtract_823, Subtract_876, Subtract_929, Subtract_982, Subtract_1035, Subtract_1088, Subtract_1141, 20][ispaceLeft_1372];

var bool: Less_1374 = (spaceLeft_1372 < 0);

var bool: ret_tooFull_1378; %ref (Literal: 0 [0]).ret_tooFull -20
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_tooFull -20
var 1..1: iret_tooFull_1378;
constraint ret_tooFull_1378 = [Less_1374, false][iret_tooFull_1378];

var bool: setempty_1389 = not (((14 = items_597)) \/ ((14 = items_650)) \/ ((14 = items_703)) \/ ((14 = items_756)) \/ ((14 = items_809)) \/ ((14 = items_862)) \/ ((14 = items_915)) \/ ((14 = items_968)) \/ ((14 = items_1021)) \/ ((14 = items_1074)) \/ ((14 = items_1127)));

var bool: ret_isEmpty_1393; %ref (Literal: 0 [0]).ret_isEmpty -21
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_isEmpty -21
var 1..1: iret_isEmpty_1393;
constraint ret_isEmpty_1393 = [setempty_1389, false][iret_isEmpty_1393];

var bool: notret_isEmpty_1393 = not ret_isEmpty_1393;

var -35..20: spaceLeft_1432; %ref ref (Literal: 0 [0]).b -19.spaceLeft -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).b -19.spaceLeft -7
var 1..12: ispaceLeft_1432;
constraint [16, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853, chooseobj_906, chooseobj_959, chooseobj_1012, chooseobj_1065, chooseobj_1118, 16][ispaceLeft_1432] = 16;
constraint (true) -> ispaceLeft_1432 >= 1;
constraint ((16 = chooseobj_588)) -> ispaceLeft_1432 >= 2;
constraint ((16 = chooseobj_641)) -> ispaceLeft_1432 >= 3;
constraint ((16 = chooseobj_694)) -> ispaceLeft_1432 >= 4;
constraint ((16 = chooseobj_747)) -> ispaceLeft_1432 >= 5;
constraint ((16 = chooseobj_800)) -> ispaceLeft_1432 >= 6;
constraint ((16 = chooseobj_853)) -> ispaceLeft_1432 >= 7;
constraint ((16 = chooseobj_906)) -> ispaceLeft_1432 >= 8;
constraint ((16 = chooseobj_959)) -> ispaceLeft_1432 >= 9;
constraint ((16 = chooseobj_1012)) -> ispaceLeft_1432 >= 10;
constraint ((16 = chooseobj_1065)) -> ispaceLeft_1432 >= 11;
constraint ((16 = chooseobj_1118)) -> ispaceLeft_1432 >= 12;
constraint spaceLeft_1432 = [20, 16, Subtract_664, Subtract_717, Subtract_770, Subtract_823, Subtract_876, Subtract_929, Subtract_982, Subtract_1035, Subtract_1088, Subtract_1141, 20][ispaceLeft_1432];

var bool: Less_1434 = (spaceLeft_1432 < 0);

var bool: ret_tooFull_1438; %ref (Literal: 0 [0]).ret_tooFull -20
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_tooFull -20
var 1..1: iret_tooFull_1438;
constraint ret_tooFull_1438 = [Less_1434, false][iret_tooFull_1438];

var bool: setempty_1449 = not (((17 = items_597)) \/ ((17 = items_650)) \/ ((17 = items_703)) \/ ((17 = items_756)) \/ ((17 = items_809)) \/ ((17 = items_862)) \/ ((17 = items_915)) \/ ((17 = items_968)) \/ ((17 = items_1021)) \/ ((17 = items_1074)) \/ ((17 = items_1127)));

var bool: ret_isEmpty_1453; %ref (Literal: 0 [0]).ret_isEmpty -21
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_isEmpty -21
var 1..1: iret_isEmpty_1453;
constraint ret_isEmpty_1453 = [setempty_1449, false][iret_isEmpty_1453];

var bool: notret_isEmpty_1453 = not ret_isEmpty_1453;

var -35..20: spaceLeft_1492; %ref ref (Literal: 0 [0]).b -19.spaceLeft -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).b -19.spaceLeft -7
var 1..12: ispaceLeft_1492;
constraint [19, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853, chooseobj_906, chooseobj_959, chooseobj_1012, chooseobj_1065, chooseobj_1118, 19][ispaceLeft_1492] = 19;
constraint (true) -> ispaceLeft_1492 >= 1;
constraint ((19 = chooseobj_588)) -> ispaceLeft_1492 >= 2;
constraint ((19 = chooseobj_641)) -> ispaceLeft_1492 >= 3;
constraint ((19 = chooseobj_694)) -> ispaceLeft_1492 >= 4;
constraint ((19 = chooseobj_747)) -> ispaceLeft_1492 >= 5;
constraint ((19 = chooseobj_800)) -> ispaceLeft_1492 >= 6;
constraint ((19 = chooseobj_853)) -> ispaceLeft_1492 >= 7;
constraint ((19 = chooseobj_906)) -> ispaceLeft_1492 >= 8;
constraint ((19 = chooseobj_959)) -> ispaceLeft_1492 >= 9;
constraint ((19 = chooseobj_1012)) -> ispaceLeft_1492 >= 10;
constraint ((19 = chooseobj_1065)) -> ispaceLeft_1492 >= 11;
constraint ((19 = chooseobj_1118)) -> ispaceLeft_1492 >= 12;
constraint spaceLeft_1492 = [20, 16, Subtract_664, Subtract_717, Subtract_770, Subtract_823, Subtract_876, Subtract_929, Subtract_982, Subtract_1035, Subtract_1088, Subtract_1141, 20][ispaceLeft_1492];

var bool: Less_1494 = (spaceLeft_1492 < 0);

var bool: ret_tooFull_1498; %ref (Literal: 0 [0]).ret_tooFull -20
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_tooFull -20
var 1..1: iret_tooFull_1498;
constraint ret_tooFull_1498 = [Less_1494, false][iret_tooFull_1498];

var bool: setempty_1509 = not (((20 = items_597)) \/ ((20 = items_650)) \/ ((20 = items_703)) \/ ((20 = items_756)) \/ ((20 = items_809)) \/ ((20 = items_862)) \/ ((20 = items_915)) \/ ((20 = items_968)) \/ ((20 = items_1021)) \/ ((20 = items_1074)) \/ ((20 = items_1127)));

var bool: ret_isEmpty_1513; %ref (Literal: 0 [0]).ret_isEmpty -21
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_isEmpty -21
var 1..1: iret_isEmpty_1513;
constraint ret_isEmpty_1513 = [setempty_1509, false][iret_isEmpty_1513];

var bool: notret_isEmpty_1513 = not ret_isEmpty_1513;

var -35..20: spaceLeft_1552; %ref ref (Literal: 0 [0]).b -19.spaceLeft -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).b -19.spaceLeft -7
var 1..12: ispaceLeft_1552;
constraint [22, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853, chooseobj_906, chooseobj_959, chooseobj_1012, chooseobj_1065, chooseobj_1118, 22][ispaceLeft_1552] = 22;
constraint (true) -> ispaceLeft_1552 >= 1;
constraint ((22 = chooseobj_588)) -> ispaceLeft_1552 >= 2;
constraint ((22 = chooseobj_641)) -> ispaceLeft_1552 >= 3;
constraint ((22 = chooseobj_694)) -> ispaceLeft_1552 >= 4;
constraint ((22 = chooseobj_747)) -> ispaceLeft_1552 >= 5;
constraint ((22 = chooseobj_800)) -> ispaceLeft_1552 >= 6;
constraint ((22 = chooseobj_853)) -> ispaceLeft_1552 >= 7;
constraint ((22 = chooseobj_906)) -> ispaceLeft_1552 >= 8;
constraint ((22 = chooseobj_959)) -> ispaceLeft_1552 >= 9;
constraint ((22 = chooseobj_1012)) -> ispaceLeft_1552 >= 10;
constraint ((22 = chooseobj_1065)) -> ispaceLeft_1552 >= 11;
constraint ((22 = chooseobj_1118)) -> ispaceLeft_1552 >= 12;
constraint spaceLeft_1552 = [20, 16, Subtract_664, Subtract_717, Subtract_770, Subtract_823, Subtract_876, Subtract_929, Subtract_982, Subtract_1035, Subtract_1088, Subtract_1141, 20][ispaceLeft_1552];

var bool: Less_1554 = (spaceLeft_1552 < 0);

var bool: ret_tooFull_1558; %ref (Literal: 0 [0]).ret_tooFull -20
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_tooFull -20
var 1..1: iret_tooFull_1558;
constraint ret_tooFull_1558 = [Less_1554, false][iret_tooFull_1558];

var bool: setempty_1569 = not (((23 = items_597)) \/ ((23 = items_650)) \/ ((23 = items_703)) \/ ((23 = items_756)) \/ ((23 = items_809)) \/ ((23 = items_862)) \/ ((23 = items_915)) \/ ((23 = items_968)) \/ ((23 = items_1021)) \/ ((23 = items_1074)) \/ ((23 = items_1127)));

var bool: ret_isEmpty_1573; %ref (Literal: 0 [0]).ret_isEmpty -21
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_isEmpty -21
var 1..1: iret_isEmpty_1573;
constraint ret_isEmpty_1573 = [setempty_1569, false][iret_isEmpty_1573];

var bool: notret_isEmpty_1573 = not ret_isEmpty_1573;

var -35..20: spaceLeft_1612; %ref ref (Literal: 0 [0]).b -19.spaceLeft -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).b -19.spaceLeft -7
var 1..12: ispaceLeft_1612;
constraint [25, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853, chooseobj_906, chooseobj_959, chooseobj_1012, chooseobj_1065, chooseobj_1118, 25][ispaceLeft_1612] = 25;
constraint (true) -> ispaceLeft_1612 >= 1;
constraint ((25 = chooseobj_588)) -> ispaceLeft_1612 >= 2;
constraint ((25 = chooseobj_641)) -> ispaceLeft_1612 >= 3;
constraint ((25 = chooseobj_694)) -> ispaceLeft_1612 >= 4;
constraint ((25 = chooseobj_747)) -> ispaceLeft_1612 >= 5;
constraint ((25 = chooseobj_800)) -> ispaceLeft_1612 >= 6;
constraint ((25 = chooseobj_853)) -> ispaceLeft_1612 >= 7;
constraint ((25 = chooseobj_906)) -> ispaceLeft_1612 >= 8;
constraint ((25 = chooseobj_959)) -> ispaceLeft_1612 >= 9;
constraint ((25 = chooseobj_1012)) -> ispaceLeft_1612 >= 10;
constraint ((25 = chooseobj_1065)) -> ispaceLeft_1612 >= 11;
constraint ((25 = chooseobj_1118)) -> ispaceLeft_1612 >= 12;
constraint spaceLeft_1612 = [20, 16, Subtract_664, Subtract_717, Subtract_770, Subtract_823, Subtract_876, Subtract_929, Subtract_982, Subtract_1035, Subtract_1088, Subtract_1141, 20][ispaceLeft_1612];

var bool: Less_1614 = (spaceLeft_1612 < 0);

var bool: ret_tooFull_1618; %ref (Literal: 0 [0]).ret_tooFull -20
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_tooFull -20
var 1..1: iret_tooFull_1618;
constraint ret_tooFull_1618 = [Less_1614, false][iret_tooFull_1618];

var bool: setempty_1629 = not (((26 = items_597)) \/ ((26 = items_650)) \/ ((26 = items_703)) \/ ((26 = items_756)) \/ ((26 = items_809)) \/ ((26 = items_862)) \/ ((26 = items_915)) \/ ((26 = items_968)) \/ ((26 = items_1021)) \/ ((26 = items_1074)) \/ ((26 = items_1127)));

var bool: ret_isEmpty_1633; %ref (Literal: 0 [0]).ret_isEmpty -21
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_isEmpty -21
var 1..1: iret_isEmpty_1633;
constraint ret_isEmpty_1633 = [setempty_1629, false][iret_isEmpty_1633];

var bool: notret_isEmpty_1633 = not ret_isEmpty_1633;

var -35..20: spaceLeft_1672; %ref ref (Literal: 0 [0]).b -19.spaceLeft -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).b -19.spaceLeft -7
var 1..12: ispaceLeft_1672;
constraint [28, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853, chooseobj_906, chooseobj_959, chooseobj_1012, chooseobj_1065, chooseobj_1118, 28][ispaceLeft_1672] = 28;
constraint (true) -> ispaceLeft_1672 >= 1;
constraint ((28 = chooseobj_588)) -> ispaceLeft_1672 >= 2;
constraint ((28 = chooseobj_641)) -> ispaceLeft_1672 >= 3;
constraint ((28 = chooseobj_694)) -> ispaceLeft_1672 >= 4;
constraint ((28 = chooseobj_747)) -> ispaceLeft_1672 >= 5;
constraint ((28 = chooseobj_800)) -> ispaceLeft_1672 >= 6;
constraint ((28 = chooseobj_853)) -> ispaceLeft_1672 >= 7;
constraint ((28 = chooseobj_906)) -> ispaceLeft_1672 >= 8;
constraint ((28 = chooseobj_959)) -> ispaceLeft_1672 >= 9;
constraint ((28 = chooseobj_1012)) -> ispaceLeft_1672 >= 10;
constraint ((28 = chooseobj_1065)) -> ispaceLeft_1672 >= 11;
constraint ((28 = chooseobj_1118)) -> ispaceLeft_1672 >= 12;
constraint spaceLeft_1672 = [20, 16, Subtract_664, Subtract_717, Subtract_770, Subtract_823, Subtract_876, Subtract_929, Subtract_982, Subtract_1035, Subtract_1088, Subtract_1141, 20][ispaceLeft_1672];

var bool: Less_1674 = (spaceLeft_1672 < 0);

var bool: ret_tooFull_1678; %ref (Literal: 0 [0]).ret_tooFull -20
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_tooFull -20
var 1..1: iret_tooFull_1678;
constraint ret_tooFull_1678 = [Less_1674, false][iret_tooFull_1678];

var bool: setempty_1689 = not (((29 = items_597)) \/ ((29 = items_650)) \/ ((29 = items_703)) \/ ((29 = items_756)) \/ ((29 = items_809)) \/ ((29 = items_862)) \/ ((29 = items_915)) \/ ((29 = items_968)) \/ ((29 = items_1021)) \/ ((29 = items_1074)) \/ ((29 = items_1127)));

var bool: ret_isEmpty_1693; %ref (Literal: 0 [0]).ret_isEmpty -21
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_isEmpty -21
var 1..1: iret_isEmpty_1693;
constraint ret_isEmpty_1693 = [setempty_1689, false][iret_isEmpty_1693];

var bool: notret_isEmpty_1693 = not ret_isEmpty_1693;

var -35..20: spaceLeft_1732; %ref ref (Literal: 0 [0]).b -19.spaceLeft -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).b -19.spaceLeft -7
var 1..12: ispaceLeft_1732;
constraint [31, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853, chooseobj_906, chooseobj_959, chooseobj_1012, chooseobj_1065, chooseobj_1118, 31][ispaceLeft_1732] = 31;
constraint (true) -> ispaceLeft_1732 >= 1;
constraint ((31 = chooseobj_588)) -> ispaceLeft_1732 >= 2;
constraint ((31 = chooseobj_641)) -> ispaceLeft_1732 >= 3;
constraint ((31 = chooseobj_694)) -> ispaceLeft_1732 >= 4;
constraint ((31 = chooseobj_747)) -> ispaceLeft_1732 >= 5;
constraint ((31 = chooseobj_800)) -> ispaceLeft_1732 >= 6;
constraint ((31 = chooseobj_853)) -> ispaceLeft_1732 >= 7;
constraint ((31 = chooseobj_906)) -> ispaceLeft_1732 >= 8;
constraint ((31 = chooseobj_959)) -> ispaceLeft_1732 >= 9;
constraint ((31 = chooseobj_1012)) -> ispaceLeft_1732 >= 10;
constraint ((31 = chooseobj_1065)) -> ispaceLeft_1732 >= 11;
constraint ((31 = chooseobj_1118)) -> ispaceLeft_1732 >= 12;
constraint spaceLeft_1732 = [20, 16, Subtract_664, Subtract_717, Subtract_770, Subtract_823, Subtract_876, Subtract_929, Subtract_982, Subtract_1035, Subtract_1088, Subtract_1141, 20][ispaceLeft_1732];

var bool: Less_1734 = (spaceLeft_1732 < 0);

var bool: ret_tooFull_1738; %ref (Literal: 0 [0]).ret_tooFull -20
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_tooFull -20
var 1..1: iret_tooFull_1738;
constraint ret_tooFull_1738 = [Less_1734, false][iret_tooFull_1738];

var bool: setempty_1749 = not (((32 = items_597)) \/ ((32 = items_650)) \/ ((32 = items_703)) \/ ((32 = items_756)) \/ ((32 = items_809)) \/ ((32 = items_862)) \/ ((32 = items_915)) \/ ((32 = items_968)) \/ ((32 = items_1021)) \/ ((32 = items_1074)) \/ ((32 = items_1127)));

var bool: ret_isEmpty_1753; %ref (Literal: 0 [0]).ret_isEmpty -21
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_isEmpty -21
var 1..1: iret_isEmpty_1753;
constraint ret_isEmpty_1753 = [setempty_1749, false][iret_isEmpty_1753];

var bool: notret_isEmpty_1753 = not ret_isEmpty_1753;

var -35..20: spaceLeft_1792; %ref ref (Literal: 0 [0]).b -19.spaceLeft -7
% doing constraints for lookup query: ref ref (Literal: 0 [0]).b -19.spaceLeft -7
var 1..12: ispaceLeft_1792;
constraint [34, chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853, chooseobj_906, chooseobj_959, chooseobj_1012, chooseobj_1065, chooseobj_1118, 34][ispaceLeft_1792] = 34;
constraint (true) -> ispaceLeft_1792 >= 1;
constraint ((34 = chooseobj_588)) -> ispaceLeft_1792 >= 2;
constraint ((34 = chooseobj_641)) -> ispaceLeft_1792 >= 3;
constraint ((34 = chooseobj_694)) -> ispaceLeft_1792 >= 4;
constraint ((34 = chooseobj_747)) -> ispaceLeft_1792 >= 5;
constraint ((34 = chooseobj_800)) -> ispaceLeft_1792 >= 6;
constraint ((34 = chooseobj_853)) -> ispaceLeft_1792 >= 7;
constraint ((34 = chooseobj_906)) -> ispaceLeft_1792 >= 8;
constraint ((34 = chooseobj_959)) -> ispaceLeft_1792 >= 9;
constraint ((34 = chooseobj_1012)) -> ispaceLeft_1792 >= 10;
constraint ((34 = chooseobj_1065)) -> ispaceLeft_1792 >= 11;
constraint ((34 = chooseobj_1118)) -> ispaceLeft_1792 >= 12;
constraint spaceLeft_1792 = [20, 16, Subtract_664, Subtract_717, Subtract_770, Subtract_823, Subtract_876, Subtract_929, Subtract_982, Subtract_1035, Subtract_1088, Subtract_1141, 20][ispaceLeft_1792];

var bool: Less_1794 = (spaceLeft_1792 < 0);

var bool: ret_tooFull_1798; %ref (Literal: 0 [0]).ret_tooFull -20
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_tooFull -20
var 1..1: iret_tooFull_1798;
constraint ret_tooFull_1798 = [Less_1794, false][iret_tooFull_1798];

var bool: setempty_1809 = not (((35 = items_597)) \/ ((35 = items_650)) \/ ((35 = items_703)) \/ ((35 = items_756)) \/ ((35 = items_809)) \/ ((35 = items_862)) \/ ((35 = items_915)) \/ ((35 = items_968)) \/ ((35 = items_1021)) \/ ((35 = items_1074)) \/ ((35 = items_1127)));

var bool: ret_isEmpty_1813; %ref (Literal: 0 [0]).ret_isEmpty -21
% doing constraints for lookup query: ref (Literal: 0 [0]).ret_isEmpty -21
var 1..1: iret_isEmpty_1813;
constraint ret_isEmpty_1813 = [setempty_1809, false][iret_isEmpty_1813];

var bool: notret_isEmpty_1813 = not ret_isEmpty_1813;


array[1..34] of var 1..34: prev;

constraint prev[1] = 25;
constraint prev[2] in {2,16}; %ref (Literal: 0 [0]).numUsed -17
constraint prev[3] in {2,3,16}; %optimise.state.EndCond@6a5
constraint prev[4] in {4,31}; %ref (Literal: 0 [0]).numUsed -17
constraint prev[5] in {5,34}; %optimise.state.EndCond@529
constraint prev[6] in {5,6}; %ref (Literal: 0 [0]).numUsed -17
constraint prev[7] in {5,6,7}; %optimise.state.EndCond@53d
constraint prev[8] in {8,29}; %optimise.state.EndCond@619
constraint prev[9] in {8,9}; %ref (Literal: 0 [0]).numUsed -17
constraint prev[10] in {4,10,31}; %optimise.state.EndCond@6e1
constraint prev[11] in {7,11}; %optimise.state.EndCond@565
constraint prev[12] in {11,12}; %ref (Literal: 0 [0]).numUsed -17
constraint prev[13] in {11,12,13}; %optimise.state.EndCond@579
constraint prev[14] in {8,9,14}; %optimise.state.EndCond@62d
constraint prev[15] in {15,20}; %ref (Literal: 0 [0]).numUsed -17
constraint prev[16] in {16,30}; %optimise.state.EndCond@691
constraint prev[17] in {13,17}; %optimise.state.EndCond@5a1
constraint prev[18] in {17,18}; %ref (Literal: 0 [0]).numUsed -17
constraint prev[19] in {17,18,19}; %optimise.state.EndCond@5b5
constraint prev[20] in {10,20}; %optimise.state.EndCond@709
constraint prev[21] in {14,21}; %optimise.state.EndCond@655
constraint prev[22] in {21,22}; %ref (Literal: 0 [0]).numUsed -17
constraint prev[23] in {19,23}; %optimise.state.EndCond@5dd
constraint prev[24] in {23,24}; %ref (Literal: 0 [0]).numUsed -17
constraint prev[25] in {15,20,25}; %optimise.state.EndCond@71d
constraint prev[26] in {1,26}; %optimise.state.EndCond@4b1
constraint prev[27] in {26,27}; %ref (Literal: 0 [0]).numUsed -17
constraint prev[28] in {26,27,28}; %optimise.state.EndCond@4c5
constraint prev[29] in {23,24,29}; %optimise.state.EndCond@5f1
constraint prev[30] in {21,22,30}; %optimise.state.EndCond@669
constraint prev[31] in {3,31}; %optimise.state.EndCond@6cd
constraint prev[32] in {28,32}; %optimise.state.EndCond@4ed
constraint prev[33] in {32,33}; %ref (Literal: 0 [0]).numUsed -17
constraint prev[34] in {32,33,34}; %optimise.state.EndCond@501
constraint alldifferent (prev);
constraint (prev[26] = 1) -> not ret_tooFull_1198;
constraint (prev[32] = 28) -> not ret_tooFull_1258;
constraint (prev[5] = 34) -> not ret_tooFull_1318;
constraint (prev[11] = 7) -> not ret_tooFull_1378;
constraint (prev[17] = 13) -> not ret_tooFull_1438;
constraint (prev[23] = 19) -> not ret_tooFull_1498;
constraint (prev[8] = 29) -> not ret_tooFull_1558;
constraint (prev[21] = 14) -> not ret_tooFull_1618;
constraint (prev[16] = 30) -> not ret_tooFull_1678;
constraint (prev[31] = 3) -> not ret_tooFull_1738;
constraint (prev[20] = 10) -> not ret_tooFull_1798;
constraint (prev[27] = 26) -> notret_isEmpty_1213;
constraint (prev[28] = 26) -> not notret_isEmpty_1213;
constraint (prev[33] = 32) -> notret_isEmpty_1273;
constraint (prev[34] = 32) -> not notret_isEmpty_1273;
constraint (prev[6] = 5) -> notret_isEmpty_1333;
constraint (prev[7] = 5) -> not notret_isEmpty_1333;
constraint (prev[12] = 11) -> notret_isEmpty_1393;
constraint (prev[13] = 11) -> not notret_isEmpty_1393;
constraint (prev[18] = 17) -> notret_isEmpty_1453;
constraint (prev[19] = 17) -> not notret_isEmpty_1453;
constraint (prev[24] = 23) -> notret_isEmpty_1513;
constraint (prev[29] = 23) -> not notret_isEmpty_1513;
constraint (prev[9] = 8) -> notret_isEmpty_1573;
constraint (prev[14] = 8) -> not notret_isEmpty_1573;
constraint (prev[22] = 21) -> notret_isEmpty_1633;
constraint (prev[30] = 21) -> not notret_isEmpty_1633;
constraint (prev[2] = 16) -> notret_isEmpty_1693;
constraint (prev[3] = 16) -> not notret_isEmpty_1693;
constraint (prev[4] = 31) -> notret_isEmpty_1753;
constraint (prev[10] = 31) -> not notret_isEmpty_1753;
constraint (prev[15] = 20) -> notret_isEmpty_1813;
constraint (prev[25] = 20) -> not notret_isEmpty_1813;
solve :: seq_search([
		 int_search([chooseobj_588, chooseobj_641, chooseobj_694, chooseobj_747, chooseobj_800, chooseobj_853, chooseobj_906, chooseobj_959, chooseobj_1012, chooseobj_1065, chooseobj_1118],input_order,indomain_min,complete),
		int_search(prev, first_fail, indomain_min, complete),
		bool_search([Less_1194, ret_tooFull_1198, setempty_1209, ret_isEmpty_1213, notret_isEmpty_1213, Less_1254, ret_tooFull_1258, setempty_1269, ret_isEmpty_1273, notret_isEmpty_1273, Less_1314, ret_tooFull_1318, setempty_1329, ret_isEmpty_1333, notret_isEmpty_1333, Less_1374, ret_tooFull_1378, setempty_1389, ret_isEmpty_1393, notret_isEmpty_1393, Less_1434, ret_tooFull_1438, setempty_1449, ret_isEmpty_1453, notret_isEmpty_1453, Less_1494, ret_tooFull_1498, setempty_1509, ret_isEmpty_1513, notret_isEmpty_1513, Less_1554, ret_tooFull_1558, setempty_1569, ret_isEmpty_1573, notret_isEmpty_1573, Less_1614, ret_tooFull_1618, setempty_1629, ret_isEmpty_1633, notret_isEmpty_1633, Less_1674, ret_tooFull_1678, setempty_1689, ret_isEmpty_1693, notret_isEmpty_1693, Less_1734, ret_tooFull_1738, setempty_1749, ret_isEmpty_1753, notret_isEmpty_1753, Less_1794, ret_tooFull_1798, setempty_1809, ret_isEmpty_1813, notret_isEmpty_1813], input_order, indomain_max, complete),
		int_search([numUsed_1277, inumUsed_1277, Add_1279, numUsed_1337, inumUsed_1337, Add_1339, numUsed_1397, inumUsed_1397, Add_1399, numUsed_1457, inumUsed_1457, Add_1459, numUsed_1517, inumUsed_1517, Add_1519, numUsed_1577, inumUsed_1577, Add_1579, numUsed_1637, inumUsed_1637, Add_1639, numUsed_1697, inumUsed_1697, Add_1699, numUsed_1757, inumUsed_1757, Add_1759, numUsed_1817, inumUsed_1817, Add_1819, numUsed_1825, inumUsed_1825, objective, iobjective, chooseobj_588, items_597, iitems_597, chooseobj_641, items_650, iitems_650, spaceLeft_660, ispaceLeft_660, Subtract_664, chooseobj_694, items_703, iitems_703, spaceLeft_713, ispaceLeft_713, Subtract_717, chooseobj_747, items_756, iitems_756, spaceLeft_766, ispaceLeft_766, Subtract_770, chooseobj_800, items_809, iitems_809, spaceLeft_819, ispaceLeft_819, Subtract_823, chooseobj_853, items_862, iitems_862, spaceLeft_872, ispaceLeft_872, Subtract_876, chooseobj_906, items_915, iitems_915, spaceLeft_925, ispaceLeft_925, Subtract_929, chooseobj_959, items_968, iitems_968, spaceLeft_978, ispaceLeft_978, Subtract_982, chooseobj_1012, items_1021, iitems_1021, spaceLeft_1031, ispaceLeft_1031, Subtract_1035, chooseobj_1065, items_1074, iitems_1074, spaceLeft_1084, ispaceLeft_1084, Subtract_1088, chooseobj_1118, items_1127, iitems_1127, spaceLeft_1137, ispaceLeft_1137, Subtract_1141, spaceLeft_1192, ispaceLeft_1192, iret_tooFull_1198, iret_isEmpty_1213, spaceLeft_1252, ispaceLeft_1252, iret_tooFull_1258, iret_isEmpty_1273, spaceLeft_1312, ispaceLeft_1312, iret_tooFull_1318, iret_isEmpty_1333, spaceLeft_1372, ispaceLeft_1372, iret_tooFull_1378, iret_isEmpty_1393, spaceLeft_1432, ispaceLeft_1432, iret_tooFull_1438, iret_isEmpty_1453, spaceLeft_1492, ispaceLeft_1492, iret_tooFull_1498, iret_isEmpty_1513, spaceLeft_1552, ispaceLeft_1552, iret_tooFull_1558, iret_isEmpty_1573, spaceLeft_1612, ispaceLeft_1612, iret_tooFull_1618, iret_isEmpty_1633, spaceLeft_1672, ispaceLeft_1672, iret_tooFull_1678, iret_isEmpty_1693, spaceLeft_1732, ispaceLeft_1732, iret_tooFull_1738, iret_isEmpty_1753, spaceLeft_1792, ispaceLeft_1792, iret_tooFull_1798, iret_isEmpty_1813], first_fail, indomain_min, complete),
	])
	minimize objective;

output [
	"prev = \(prev);\n",
	"constraint Less_1194 = \(Less_1194);\n",
	"ret_tooFull_1198 = \(ret_tooFull_1198);\n",
	"constraint setempty_1209 = \(setempty_1209);\n",
	"ret_isEmpty_1213 = \(ret_isEmpty_1213);\n",
	"constraint notret_isEmpty_1213 = \(notret_isEmpty_1213);\n",
	"constraint Less_1254 = \(Less_1254);\n",
	"ret_tooFull_1258 = \(ret_tooFull_1258);\n",
	"constraint setempty_1269 = \(setempty_1269);\n",
	"ret_isEmpty_1273 = \(ret_isEmpty_1273);\n",
	"constraint notret_isEmpty_1273 = \(notret_isEmpty_1273);\n",
	"constraint Less_1314 = \(Less_1314);\n",
	"ret_tooFull_1318 = \(ret_tooFull_1318);\n",
	"constraint setempty_1329 = \(setempty_1329);\n",
	"ret_isEmpty_1333 = \(ret_isEmpty_1333);\n",
	"constraint notret_isEmpty_1333 = \(notret_isEmpty_1333);\n",
	"constraint Less_1374 = \(Less_1374);\n",
	"ret_tooFull_1378 = \(ret_tooFull_1378);\n",
	"constraint setempty_1389 = \(setempty_1389);\n",
	"ret_isEmpty_1393 = \(ret_isEmpty_1393);\n",
	"constraint notret_isEmpty_1393 = \(notret_isEmpty_1393);\n",
	"constraint Less_1434 = \(Less_1434);\n",
	"ret_tooFull_1438 = \(ret_tooFull_1438);\n",
	"constraint setempty_1449 = \(setempty_1449);\n",
	"ret_isEmpty_1453 = \(ret_isEmpty_1453);\n",
	"constraint notret_isEmpty_1453 = \(notret_isEmpty_1453);\n",
	"constraint Less_1494 = \(Less_1494);\n",
	"ret_tooFull_1498 = \(ret_tooFull_1498);\n",
	"constraint setempty_1509 = \(setempty_1509);\n",
	"ret_isEmpty_1513 = \(ret_isEmpty_1513);\n",
	"constraint notret_isEmpty_1513 = \(notret_isEmpty_1513);\n",
	"constraint Less_1554 = \(Less_1554);\n",
	"ret_tooFull_1558 = \(ret_tooFull_1558);\n",
	"constraint setempty_1569 = \(setempty_1569);\n",
	"ret_isEmpty_1573 = \(ret_isEmpty_1573);\n",
	"constraint notret_isEmpty_1573 = \(notret_isEmpty_1573);\n",
	"constraint Less_1614 = \(Less_1614);\n",
	"ret_tooFull_1618 = \(ret_tooFull_1618);\n",
	"constraint setempty_1629 = \(setempty_1629);\n",
	"ret_isEmpty_1633 = \(ret_isEmpty_1633);\n",
	"constraint notret_isEmpty_1633 = \(notret_isEmpty_1633);\n",
	"constraint Less_1674 = \(Less_1674);\n",
	"ret_tooFull_1678 = \(ret_tooFull_1678);\n",
	"constraint setempty_1689 = \(setempty_1689);\n",
	"ret_isEmpty_1693 = \(ret_isEmpty_1693);\n",
	"constraint notret_isEmpty_1693 = \(notret_isEmpty_1693);\n",
	"constraint Less_1734 = \(Less_1734);\n",
	"ret_tooFull_1738 = \(ret_tooFull_1738);\n",
	"constraint setempty_1749 = \(setempty_1749);\n",
	"ret_isEmpty_1753 = \(ret_isEmpty_1753);\n",
	"constraint notret_isEmpty_1753 = \(notret_isEmpty_1753);\n",
	"constraint Less_1794 = \(Less_1794);\n",
	"ret_tooFull_1798 = \(ret_tooFull_1798);\n",
	"constraint setempty_1809 = \(setempty_1809);\n",
	"ret_isEmpty_1813 = \(ret_isEmpty_1813);\n",
	"constraint notret_isEmpty_1813 = \(notret_isEmpty_1813);\n",
	"numUsed_1277 = \(numUsed_1277);\n",
	"inumUsed_1277 = \(inumUsed_1277);\n",
	"constraint Add_1279 = \(Add_1279);\n",
	"numUsed_1337 = \(numUsed_1337);\n",
	"inumUsed_1337 = \(inumUsed_1337);\n",
	"constraint Add_1339 = \(Add_1339);\n",
	"numUsed_1397 = \(numUsed_1397);\n",
	"inumUsed_1397 = \(inumUsed_1397);\n",
	"constraint Add_1399 = \(Add_1399);\n",
	"numUsed_1457 = \(numUsed_1457);\n",
	"inumUsed_1457 = \(inumUsed_1457);\n",
	"constraint Add_1459 = \(Add_1459);\n",
	"numUsed_1517 = \(numUsed_1517);\n",
	"inumUsed_1517 = \(inumUsed_1517);\n",
	"constraint Add_1519 = \(Add_1519);\n",
	"numUsed_1577 = \(numUsed_1577);\n",
	"inumUsed_1577 = \(inumUsed_1577);\n",
	"constraint Add_1579 = \(Add_1579);\n",
	"numUsed_1637 = \(numUsed_1637);\n",
	"inumUsed_1637 = \(inumUsed_1637);\n",
	"constraint Add_1639 = \(Add_1639);\n",
	"numUsed_1697 = \(numUsed_1697);\n",
	"inumUsed_1697 = \(inumUsed_1697);\n",
	"constraint Add_1699 = \(Add_1699);\n",
	"numUsed_1757 = \(numUsed_1757);\n",
	"inumUsed_1757 = \(inumUsed_1757);\n",
	"constraint Add_1759 = \(Add_1759);\n",
	"numUsed_1817 = \(numUsed_1817);\n",
	"inumUsed_1817 = \(inumUsed_1817);\n",
	"constraint Add_1819 = \(Add_1819);\n",
	"numUsed_1825 = \(numUsed_1825);\n",
	"inumUsed_1825 = \(inumUsed_1825);\n",
	"iobjective = \(iobjective);\n",
	"chooseobj_588 = \(chooseobj_588);\n",
	"items_597 = \(items_597);\n",
	"iitems_597 = \(iitems_597);\n",
	"chooseobj_641 = \(chooseobj_641);\n",
	"items_650 = \(items_650);\n",
	"iitems_650 = \(iitems_650);\n",
	"spaceLeft_660 = \(spaceLeft_660);\n",
	"ispaceLeft_660 = \(ispaceLeft_660);\n",
	"constraint Subtract_664 = \(Subtract_664);\n",
	"chooseobj_694 = \(chooseobj_694);\n",
	"items_703 = \(items_703);\n",
	"iitems_703 = \(iitems_703);\n",
	"spaceLeft_713 = \(spaceLeft_713);\n",
	"ispaceLeft_713 = \(ispaceLeft_713);\n",
	"constraint Subtract_717 = \(Subtract_717);\n",
	"chooseobj_747 = \(chooseobj_747);\n",
	"items_756 = \(items_756);\n",
	"iitems_756 = \(iitems_756);\n",
	"spaceLeft_766 = \(spaceLeft_766);\n",
	"ispaceLeft_766 = \(ispaceLeft_766);\n",
	"constraint Subtract_770 = \(Subtract_770);\n",
	"chooseobj_800 = \(chooseobj_800);\n",
	"items_809 = \(items_809);\n",
	"iitems_809 = \(iitems_809);\n",
	"spaceLeft_819 = \(spaceLeft_819);\n",
	"ispaceLeft_819 = \(ispaceLeft_819);\n",
	"constraint Subtract_823 = \(Subtract_823);\n",
	"chooseobj_853 = \(chooseobj_853);\n",
	"items_862 = \(items_862);\n",
	"iitems_862 = \(iitems_862);\n",
	"spaceLeft_872 = \(spaceLeft_872);\n",
	"ispaceLeft_872 = \(ispaceLeft_872);\n",
	"constraint Subtract_876 = \(Subtract_876);\n",
	"chooseobj_906 = \(chooseobj_906);\n",
	"items_915 = \(items_915);\n",
	"iitems_915 = \(iitems_915);\n",
	"spaceLeft_925 = \(spaceLeft_925);\n",
	"ispaceLeft_925 = \(ispaceLeft_925);\n",
	"constraint Subtract_929 = \(Subtract_929);\n",
	"chooseobj_959 = \(chooseobj_959);\n",
	"items_968 = \(items_968);\n",
	"iitems_968 = \(iitems_968);\n",
	"spaceLeft_978 = \(spaceLeft_978);\n",
	"ispaceLeft_978 = \(ispaceLeft_978);\n",
	"constraint Subtract_982 = \(Subtract_982);\n",
	"chooseobj_1012 = \(chooseobj_1012);\n",
	"items_1021 = \(items_1021);\n",
	"iitems_1021 = \(iitems_1021);\n",
	"spaceLeft_1031 = \(spaceLeft_1031);\n",
	"ispaceLeft_1031 = \(ispaceLeft_1031);\n",
	"constraint Subtract_1035 = \(Subtract_1035);\n",
	"chooseobj_1065 = \(chooseobj_1065);\n",
	"items_1074 = \(items_1074);\n",
	"iitems_1074 = \(iitems_1074);\n",
	"spaceLeft_1084 = \(spaceLeft_1084);\n",
	"ispaceLeft_1084 = \(ispaceLeft_1084);\n",
	"constraint Subtract_1088 = \(Subtract_1088);\n",
	"chooseobj_1118 = \(chooseobj_1118);\n",
	"items_1127 = \(items_1127);\n",
	"iitems_1127 = \(iitems_1127);\n",
	"spaceLeft_1137 = \(spaceLeft_1137);\n",
	"ispaceLeft_1137 = \(ispaceLeft_1137);\n",
	"constraint Subtract_1141 = \(Subtract_1141);\n",
	"spaceLeft_1192 = \(spaceLeft_1192);\n",
	"ispaceLeft_1192 = \(ispaceLeft_1192);\n",
	"iret_tooFull_1198 = \(iret_tooFull_1198);\n",
	"iret_isEmpty_1213 = \(iret_isEmpty_1213);\n",
	"spaceLeft_1252 = \(spaceLeft_1252);\n",
	"ispaceLeft_1252 = \(ispaceLeft_1252);\n",
	"iret_tooFull_1258 = \(iret_tooFull_1258);\n",
	"iret_isEmpty_1273 = \(iret_isEmpty_1273);\n",
	"spaceLeft_1312 = \(spaceLeft_1312);\n",
	"ispaceLeft_1312 = \(ispaceLeft_1312);\n",
	"iret_tooFull_1318 = \(iret_tooFull_1318);\n",
	"iret_isEmpty_1333 = \(iret_isEmpty_1333);\n",
	"spaceLeft_1372 = \(spaceLeft_1372);\n",
	"ispaceLeft_1372 = \(ispaceLeft_1372);\n",
	"iret_tooFull_1378 = \(iret_tooFull_1378);\n",
	"iret_isEmpty_1393 = \(iret_isEmpty_1393);\n",
	"spaceLeft_1432 = \(spaceLeft_1432);\n",
	"ispaceLeft_1432 = \(ispaceLeft_1432);\n",
	"iret_tooFull_1438 = \(iret_tooFull_1438);\n",
	"iret_isEmpty_1453 = \(iret_isEmpty_1453);\n",
	"spaceLeft_1492 = \(spaceLeft_1492);\n",
	"ispaceLeft_1492 = \(ispaceLeft_1492);\n",
	"iret_tooFull_1498 = \(iret_tooFull_1498);\n",
	"iret_isEmpty_1513 = \(iret_isEmpty_1513);\n",
	"spaceLeft_1552 = \(spaceLeft_1552);\n",
	"ispaceLeft_1552 = \(ispaceLeft_1552);\n",
	"iret_tooFull_1558 = \(iret_tooFull_1558);\n",
	"iret_isEmpty_1573 = \(iret_isEmpty_1573);\n",
	"spaceLeft_1612 = \(spaceLeft_1612);\n",
	"ispaceLeft_1612 = \(ispaceLeft_1612);\n",
	"iret_tooFull_1618 = \(iret_tooFull_1618);\n",
	"iret_isEmpty_1633 = \(iret_isEmpty_1633);\n",
	"spaceLeft_1672 = \(spaceLeft_1672);\n",
	"ispaceLeft_1672 = \(ispaceLeft_1672);\n",
	"iret_tooFull_1678 = \(iret_tooFull_1678);\n",
	"iret_isEmpty_1693 = \(iret_isEmpty_1693);\n",
	"spaceLeft_1732 = \(spaceLeft_1732);\n",
	"ispaceLeft_1732 = \(ispaceLeft_1732);\n",
	"iret_tooFull_1738 = \(iret_tooFull_1738);\n",
	"iret_isEmpty_1753 = \(iret_isEmpty_1753);\n",
	"spaceLeft_1792 = \(spaceLeft_1792);\n",
	"ispaceLeft_1792 = \(ispaceLeft_1792);\n",
	"iret_tooFull_1798 = \(iret_tooFull_1798);\n",
	"iret_isEmpty_1813 = \(iret_isEmpty_1813);\n",
	"constraint objective = \(objective);\n",
];

