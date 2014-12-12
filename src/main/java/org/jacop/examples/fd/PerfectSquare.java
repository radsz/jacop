/**
 *  PerfectSquare.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

package org.jacop.examples.fd;

import java.util.ArrayList;

import org.jacop.constraints.And;
import org.jacop.constraints.Diff2;
import org.jacop.constraints.Or;
import org.jacop.constraints.PrimitiveConstraint;
import org.jacop.constraints.Reified;
import org.jacop.constraints.Sum;
import org.jacop.constraints.XgtC;
import org.jacop.constraints.XgteqY;
import org.jacop.constraints.XlteqC;
import org.jacop.constraints.XlteqY;
import org.jacop.constraints.XmulCeqZ;
import org.jacop.constraints.XplusCeqZ;
import org.jacop.constraints.geost.DBox;
import org.jacop.constraints.geost.ExternalConstraint;
import org.jacop.constraints.geost.Geost;
import org.jacop.constraints.geost.GeostObject;
import org.jacop.constraints.geost.NonOverlapping;
import org.jacop.constraints.geost.Shape;
import org.jacop.core.IntVar;
import org.jacop.core.Store;
import org.jacop.search.DepthFirstSearch;
import org.jacop.search.IndomainMin;
import org.jacop.search.Search;
import org.jacop.search.SelectChoicePoint;
import org.jacop.search.SimpleSelect;
import org.jacop.search.SmallestDomain;
import org.jacop.search.SmallestMin;

/**
 * It specifies an example where squares of the given size must be placed within
 * a square of a given size. 
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.2
 */

public class PerfectSquare extends ExampleFD {
	
	/**
	 * It specifies which of the pre-defined problems should be solved.
	 */
	public static int problemNo = 0;

	IntVar[] varsX;
	IntVar[] varsY;
	IntVar[] size;
	
	/**
	 * The following table contains all the data for all problems instances. 
	 * Each entry (line)within a three dimensional table is one problem. 
	 * The first one element int array contains the size of the master square. 
	 * The master square is the square which must accommodate all other squares.
	 * The squares which must fit inside the master square are listed in the 
	 * second array.
	 */

	public static int[][][] squares = {
		{{20}, {2, 3, 4, 5, 6, 7, 8}},
		{{112}, {2,4,6,7,8,9,11,15,16,17,18,19,24,25,27,29,33,35,37,42,50}},
		{{110}, {2,3,4,6,7,8,12,13,14,15,16,17,18,21,22,23,24,26,27,28,50,60}},
		{{110}, {1,2,3,4,6,8,9,12,14,16,17,18,19,21,22,23,24,26,27,28,50,60}},
		{{139}, {1,2,3,4,7,8,10,17,18,20,21,22,24,27,28,29,30,31,32,38,59,80}},
		{{147}, {1,3,4,5,8,9,17,20,21,23,25,26,29,31,32,40,43,44,47,48,52,55}},
		{{147}, {2,4,8,10,11,12,15,19,21,22,23,25,26,32,34,37,41,43,45,47,55,59}},
		{{154}, {2,5,9,11,16,17,19,21,22,24,26,30,31,33,35,36,41,46,47,50,52,61}},
		{{172}, {1,2,3,4,9,11,13,16,17,18,19,22,24,33,36,38,39,42,44,53,75,97}},
		{{192}, {4,8,9,10,12,14,17,19,26,28,31,35,36,37,41,47,49,57,59,62,71,86}},
		{{110}, {1,2,3,4,5,7,8,10,12,13,14,15,16,19,21,28,29,31,32,37,38,41,44}},
		{{139}, {1,2,7,8,12,13,14,15,16,18,19,20,21,22,24,26,27,28,32,33,38,59,80}},
		{{140}, {1,2,3,4,5,8,10,13,16,19,20,23,27,28,29,31,33,38,42,45,48,53,54}},
		{{140}, {2,3,4,7,8,9,12,15,16,18,22,23,24,26,28,30,33,36,43,44,47,50,60}},
		{{145}, {1,2,3,4,6,8,9,12,15,20,22,24,25,26,27,29,30,31,32,34,36,61,84}},
		{{180}, {2,4,8,10,11,12,15,19,21,22,23,25,26,32,33,34,37,41,43,45,47,88,92}},
		{{188}, {2,4,8,10,11,12,15,19,21,22,23,25,26,32,33,34,37,45,47,49,51,92,96}},
		{{208}, {1,3,4,9,10,11,12,16,17,18,22,23,24,40,41,60,62,65,67,70,71,73,75}},
		{{215}, {1,3,4,9,10,11,12,16,17,18,22,23,24,40,41,60,66,68,70,71,74,76,79}},
		{{228}, {2,7,9,10,15,16,17,18,22,23,25,28,36,39,42,56,57,68,69,72,73,87,99}},
		{{257}, {2,3,9,11,14,15,17,20,22,24,28,29,32,33,49,55,57,60,63,66,79,123,134}},
		{{332}, {1,15,17,24,26,30,31,38,47,48,49,50,53,56,58,68,83,89,91,112,120,123,129}},
		{{120}, {3,4,5,6,8,9,10,12,13,14,15,16,17,19,20,23,25,32,33,34,40,41,46,47}},
		{{186}, {2,3,4,7,8,9,12,15,16,18,22,23,24,26,28,30,33,36,43,46,47,60,90,96}},
		{{194}, {2,3,7,9,10,16,17,18,19,20,23,25,28,34,36,37,42,53,54,61,65,68,69,72}},
		{{195}, {2,4,7,10,11,16,17,18,21,26,27,30,39,41,42,45,47,49,52,53,54,61,63,80}},
		{{196}, {1,2,5,10,11,15,17,18,20,21,24,26,29,31,32,34,36,40,44,47,48,51,91,105}},
		{{201}, {1,3,4,6,9,10,11,12,17,18,20,21,22,23,26,38,40,46,50,52,53,58,98,103}},
		{{201}, {1,4,5,8,9,10,11,15,16,18,19,20,22,24,26,39,42,44,49,52,54,56,93,108}},
		{{203}, {1,2,5,10,11,15,17,18,20,21,24,26,29,31,32,34,36,40,44,48,54,58,98,105}},
		{{247}, {3,5,6,9,12,14,19,23,24,25,28,32,34,36,40,45,46,48,56,62,63,66,111,136}},
		{{253}, {2,4,5,9,13,18,20,23,24,27,28,31,38,40,44,50,61,70,72,77,79,86,88,104}},
		{{255}, {3,5,10,11,16,17,20,22,23,25,26,27,28,32,41,44,52,53,59,63,65,74,118,137}},
		{{288}, {2,7,9,10,15,16,17,18,22,23,25,28,36,39,42,56,57,60,68,72,73,87,129,159}},
		{{288}, {1,5,7,8,9,14,17,20,21,26,30,32,34,36,48,51,54,59,64,69,72,93,123,165}},
		{{290}, {2,3,8,9,11,12,14,17,21,30,31,33,40,42,45,48,59,61,63,65,82,84,124,166}},
		{{292}, {1,2,3,8,12,15,16,17,20,22,24,26,29,33,44,54,57,60,63,67,73,102,117,175}},
		{{304}, {3,5,7,11,12,17,20,22,25,29,35,47,48,55,56,57,69,72,76,92,96,100,116,132}},
		{{304}, {3,4,7,12,16,20,23,24,27,28,30,32,33,36,37,44,53,57,72,76,85,99,129,175}},
		{{314}, {2,4,11,12,16,17,18,19,28,29,40,44,47,59,62,64,65,78,79,96,97,105,113,139}},
		{{316}, {3,9,10,12,13,14,15,23,24,33,36,37,48,52,54,55,57,65,66,78,79,93,144,172}},
		{{326}, {1,6,10,11,14,15,18,24,29,32,43,44,53,56,63,65,71,80,83,101,104,106,119,142}},
		{{423}, {2,9,15,17,27,29,31,32,33,36,47,49,50,60,62,77,105,114,123,127,128,132,168,186}},
		{{435}, {1,2,8,10,13,19,23,33,44,45,56,74,76,78,80,88,93,100,112,131,142,143,150,192}},
		{{435}, {3,5,9,11,12,21,24,27,30,44,45,50,54,55,63,95,101,112,117,123,134,140,178,200}},
		{{459}, {8,9,10,11,16,30,36,38,45,55,57,65,68,84,95,98,100,116,117,126,135,144,180,198}},
		{{459}, {4,6,9,10,17,21,23,25,31,33,36,38,45,50,83,115,117,126,133,135,144,146,180,198}},
		{{479}, {5,6,17,23,24,26,28,29,35,43,44,52,60,68,77,86,130,140,150,155,160,164,174,175}},
		{{147}, {3,4,5,6,8,9,10,12,13,14,15,16,17,19,20,23,25,27,32,33,34,40,41,73,74}},
		{{208}, {1,2,3,4,5,7,8,11,12,17,18,24,26,28,29,30,36,39,44,45,50,59,60,89,119}},
		{{213}, {3,5,6,7,13,16,17,20,21,23,24,25,26,28,31,35,36,47,49,56,58,74,76,81,90}},
		{{215}, {1,4,6,7,11,15,24,26,27,33,37,39,40,41,42,43,45,47,51,55,60,62,63,69,83}},
		{{216}, {1,2,3,4,5,7,8,11,16,17,18,19,25,30,32,33,39,41,45,49,54,59,64,103,113}},
		{{236}, {1,2,4,9,11,12,13,14,15,16,19,24,38,40,44,46,47,48,59,64,65,70,81,85,107}},
		{{242}, {1,3,6,7,9,13,14,16,17,19,23,25,26,28,30,31,47,51,54,57,60,64,67,111,131}},
		{{244}, {1,2,4,5,7,10,15,17,19,20,21,22,26,27,30,37,40,41,45,65,66,68,70,110,134}},
		{{252}, {4,7,10,11,12,13,23,25,29,31,32,34,36,37,38,40,42,44,62,67,68,71,77,108,113}},
		{{253}, {2,4,5,6,9,10,12,14,20,24,27,35,36,37,38,42,43,45,50,54,63,66,70,120,133}},
		{{260}, {1,4,6,7,10,15,24,26,27,28,29,31,33,34,37,38,44,65,70,71,77,78,83,100,112}},
		{{264}, {3,7,8,12,16,18,19,20,22,24,26,31,34,37,38,40,42,53,54,61,64,69,70,130,134}},
		{{264}, {3,8,12,13,16,18,20,21,22,24,26,29,34,38,40,42,43,47,54,59,64,70,71,130,134}},
		{{264}, {1,3,4,6,9,10,11,12,16,17,18,20,21,22,39,42,54,56,61,66,68,69,73,129,135}},
		{{265}, {1,3,4,6,9,10,11,12,16,17,18,20,21,22,39,42,54,56,62,66,68,69,74,130,135}},
		{{273}, {1,4,8,10,11,12,17,19,21,22,27,29,30,33,37,43,52,62,65,86,88,89,91,96,120}},
		{{273}, {1,6,9,14,16,17,18,21,22,23,25,31,32,38,44,46,48,50,54,62,65,68,78,133,140}},
		{{275}, {2,3,7,13,17,24,25,31,33,34,35,37,41,49,51,53,55,60,68,71,74,81,94,100,107}},
		{{276}, {1,5,8,9,11,18,19,21,30,36,41,44,45,46,47,51,53,58,63,69,71,84,87,105,120}},
		{{280}, {5,6,11,17,18,20,21,24,27,28,32,34,41,42,50,53,54,55,68,78,85,88,95,97,117}},
		{{280}, {2,3,7,8,14,18,30,36,37,39,44,50,52,54,56,60,63,64,65,72,75,78,79,96,106}},
		{{284}, {1,2,11,12,14,16,18,19,23,26,29,37,38,39,40,42,59,68,69,77,78,97,106,109,110}},
		{{286}, {1,4,5,7,10,12,15,16,20,23,28,30,32,33,35,37,53,54,64,68,74,79,80,133,153}},
		{{289}, {2,3,5,8,13,14,17,20,21,32,36,41,50,52,60,61,62,68,74,76,83,87,100,102,104}},
		{{289}, {2,3,4,5,7,12,16,17,19,21,23,25,29,31,32,44,57,64,65,68,72,76,84,140,149}},
		{{290}, {1,2,10,11,13,14,15,17,18,28,29,34,36,38,50,56,60,69,77,80,85,91,94,111,119}},
		{{293}, {5,6,11,17,18,20,21,24,27,28,32,34,41,42,50,54,55,66,68,78,85,88,95,110,130}},
		{{297}, {2,7,8,9,10,15,16,17,18,23,25,26,28,36,38,43,53,60,61,68,69,77,99,137,160}},
		{{308}, {1,3,4,7,10,12,13,23,25,34,37,38,39,43,44,45,62,77,79,85,87,108,113,115,116}},
		{{308}, {1,5,6,7,8,9,13,16,19,28,33,36,38,43,45,48,70,71,73,84,86,102,104,120,133}},
		{{309}, {7,8,14,16,23,24,25,26,31,33,34,39,48,56,59,60,62,70,76,82,92,100,101,108,117}},
		{{311}, {2,7,8,9,10,15,16,17,18,23,25,26,28,36,38,43,53,60,61,68,83,91,99,151,160}},
		{{314}, {1,6,7,11,16,22,26,29,32,36,38,44,51,53,64,69,70,73,74,75,85,87,101,116,128}},
		{{316}, {1,3,9,12,21,26,30,33,34,35,38,39,40,41,53,56,59,69,79,85,96,103,111,117,120}},
		{{317}, {1,5,6,7,8,9,16,17,19,32,37,40,42,47,49,52,59,75,81,92,94,110,112,113,126}},
		{{320}, {2,7,8,9,12,14,15,21,23,35,38,44,46,49,53,54,56,63,96,101,103,105,108,112,116}},
		{{320}, {3,8,9,11,17,18,22,25,26,27,29,30,31,33,35,49,51,67,72,73,80,85,95,152,168}},
		{{320}, {1,4,6,7,8,13,14,16,24,28,30,33,34,38,41,42,57,60,69,78,81,90,92,150,170}},
		{{320}, {3,4,6,8,9,14,15,16,24,28,30,31,34,38,39,42,59,60,71,78,79,90,92,150,170}},
		{{322}, {3,4,8,9,10,16,18,20,22,23,24,28,31,38,44,47,64,65,68,76,80,81,97,144,178}},
		{{322}, {3,4,8,10,15,16,18,19,20,22,24,28,35,38,44,53,59,64,68,76,80,85,93,144,178}},
		{{323}, {2,3,4,7,10,13,15,18,23,32,34,35,36,42,46,50,57,60,66,72,78,87,98,159,164}},
		{{323}, {3,8,9,11,17,18,22,25,26,27,29,30,31,33,35,49,51,67,72,73,83,88,95,155,168}},
		{{323}, {2,6,9,11,13,14,18,19,20,23,27,28,29,42,46,48,60,64,72,74,79,82,98,146,177}},
		{{325}, {3,5,6,11,12,13,18,23,25,28,32,37,40,43,45,46,51,79,92,99,103,108,112,114,134}},
		{{326}, {1,4,8,10,12,16,21,22,24,27,28,35,36,37,38,46,49,68,70,75,88,90,93,158,168}},
		{{327}, {2,9,10,12,13,16,19,21,23,26,36,44,46,52,55,61,62,74,84,87,100,103,104,120,140}},
		{{328}, {2,3,4,7,8,10,14,17,26,27,28,36,38,40,42,45,53,58,73,74,79,94,102,152,176}},
		{{334}, {1,4,8,10,12,16,21,22,24,27,28,35,36,37,38,46,49,68,75,78,88,93,98,166,168}},
		{{336}, {2,3,4,7,8,10,14,17,26,27,28,36,38,40,45,50,53,58,73,74,79,94,110,152,184}},
		{{338}, {1,4,8,10,12,16,19,22,24,25,28,36,37,38,39,46,53,68,70,73,94,96,101,164,174}},
		{{338}, {4,5,8,10,12,15,16,21,22,24,28,33,36,38,43,46,57,68,70,77,94,96,97,164,174}},
		{{340}, {1,4,5,6,11,13,16,17,22,24,44,46,50,51,52,53,61,64,66,79,84,85,92,169,171}},
		{{344}, {2,3,8,11,14,17,19,21,23,25,27,36,39,44,48,53,56,71,77,83,86,89,98,169,175}},
		{{359}, {7,8,9,10,14,17,18,23,25,27,29,31,40,41,43,46,69,74,82,85,90,98,102,172,187}},
		{{361}, {2,6,7,8,9,14,20,22,26,27,32,34,36,47,49,56,66,67,74,82,89,98,107,156,205}},
		{{363}, {1,4,6,12,13,20,21,25,26,27,28,32,37,41,45,53,58,64,69,91,97,102,106,155,208}},
		{{364}, {2,3,4,6,8,9,13,14,16,19,23,24,28,29,52,57,64,75,82,91,98,100,109,173,191}},
		{{367}, {1,4,6,12,13,20,21,25,26,27,28,32,37,41,49,53,58,64,69,91,97,102,110,155,212}},
		{{368}, {1,6,15,16,17,18,22,25,31,33,39,42,45,46,47,48,51,69,72,88,91,96,112,160,208}},
		{{371}, {1,2,7,8,20,21,22,24,26,28,30,38,43,46,50,51,64,65,70,90,95,102,109,160,211}},
		{{373}, {3,6,7,8,15,17,22,23,31,32,35,41,43,60,62,68,79,87,104,105,114,120,121,138,148}},
		{{378}, {2,3,10,17,18,20,21,22,24,27,31,38,41,48,51,56,68,78,80,85,87,96,117,165,213}},
		{{378}, {1,2,7,13,15,17,18,25,27,29,30,31,42,43,46,56,61,68,73,93,100,105,112,161,217}},
		{{380}, {4,7,17,18,19,20,21,26,31,33,35,40,45,48,49,60,67,73,79,81,87,107,113,186,194}},
		{{380}, {4,5,6,9,13,15,16,17,22,24,33,38,44,49,50,56,60,67,82,84,95,108,121,177,203}},
		{{381}, {12,13,21,23,25,27,35,36,42,45,54,57,59,60,79,82,84,85,92,95,96,100,110,111,186}},
		{{384}, {1,4,8,9,11,12,19,21,27,32,35,44,45,46,47,51,60,67,84,89,96,108,120,180,204}},
		{{384}, {1,4,8,9,11,12,15,17,19,25,26,31,32,37,44,57,60,81,84,96,99,108,120,180,204}},
		{{384}, {3,5,7,11,12,17,20,22,25,29,35,47,48,55,56,57,69,72,76,80,96,100,116,172,212}},
		{{385}, {1,2,7,13,15,17,18,25,27,29,30,31,43,46,49,56,61,68,73,93,100,105,119,161,224}},
		{{392}, {4,7,8,15,23,26,29,30,31,32,34,43,48,55,56,68,77,88,98,106,116,135,141,151,153}},
		{{392}, {10,12,14,16,19,21,25,27,31,35,39,41,51,52,54,55,73,92,98,115,121,123,129,148,171}},
		{{392}, {1,4,5,8,11,14,16,21,22,24,27,28,30,31,52,64,81,83,96,97,98,99,114,195,197}},
		{{393}, {4,8,16,20,23,24,25,27,29,37,44,45,50,53,64,66,68,69,73,85,91,101,116,186,207}},
		{{396}, {1,4,5,14,16,32,35,36,46,47,48,49,68,69,73,93,94,97,99,104,110,111,125,126,160}},
		{{396}, {1,4,5,8,11,14,16,21,22,24,27,28,30,31,52,64,81,83,98,99,100,101,114,197,199}},
		{{396}, {3,8,9,11,14,16,17,18,31,32,41,45,48,56,60,66,73,75,81,82,98,99,117,180,216}},
		{{398}, {2,6,7,11,15,17,23,28,29,39,44,46,53,56,58,65,68,99,100,119,120,134,144,145,154}},
		{{400}, {3,6,21,23,24,26,29,35,37,40,41,47,53,55,64,76,79,81,99,100,121,122,137,142,179}},
		{{404}, {3,6,7,14,17,20,21,26,28,31,32,39,46,53,54,68,71,80,88,92,100,111,113,199,205}},
		{{404}, {4,7,10,11,12,13,16,18,20,23,25,28,29,32,47,62,70,88,93,96,101,114,127,189,215}},
		{{408}, {2,3,7,13,16,18,20,27,30,33,41,43,46,52,54,57,72,79,84,100,105,108,116,195,213}},
		{{412}, {3,11,12,15,21,26,32,39,43,47,54,60,68,73,83,85,86,87,89,99,114,129,139,144,169}},
		{{413}, {5,7,17,20,34,38,39,48,56,57,59,60,64,65,70,72,75,81,105,106,110,125,148,153,155}},
		{{416}, {2,4,7,11,13,24,25,30,35,37,39,40,44,58,62,65,82,104,112,120,128,135,143,153,169}},
		{{416}, {1,2,3,8,12,15,16,17,20,22,24,26,29,31,64,75,85,88,91,94,98,104,133,179,237}},
		{{421}, {1,2,4,5,7,9,12,16,20,22,23,35,38,48,56,83,94,104,116,118,128,140,150,153,177}},
		{{421}, {5,11,12,17,18,20,23,26,29,36,38,40,44,51,55,59,72,92,97,102,105,107,117,199,222}},
		{{422}, {2,4,7,13,16,18,20,23,28,29,38,43,46,51,59,68,74,79,86,93,100,111,132,179,243}},
		{{425}, {3,4,5,9,10,12,13,14,16,19,20,31,46,48,56,79,102,104,116,126,128,140,142,157,181}},
		{{441}, {5,6,7,16,18,23,24,27,38,39,47,51,52,62,66,72,80,84,92,101,102,118,120,219,222}},
		{{454}, {1,2,11,17,29,34,35,46,48,51,53,55,63,69,79,87,88,91,109,134,136,143,150,161,184}},
		{{456}, {5,7,10,11,13,15,18,19,31,49,50,52,59,60,63,72,77,115,128,129,135,142,148,179,193}},
		{{465}, {6,9,13,14,19,21,24,25,31,32,53,56,64,73,74,82,91,111,125,127,137,139,153,173,201}},
		{{472}, {7,9,13,15,26,34,35,44,47,51,58,61,65,81,87,103,104,115,118,123,128,133,136,148,221}},
		{{477}, {3,5,12,16,19,22,25,26,37,41,49,72,76,77,82,86,87,115,117,135,141,149,167,169,193}},
		{{492}, {2,9,15,17,27,29,31,32,33,36,47,49,50,60,62,69,77,105,114,123,127,128,132,237,255}},
		{{492}, {3,5,9,11,12,21,24,27,30,44,45,50,54,55,57,63,95,101,112,117,123,134,140,235,257}},
		{{503}, {4,15,16,19,22,23,25,27,33,34,50,62,67,87,88,93,100,113,135,143,149,157,167,179,211}},
		{{506}, {1,7,24,26,33,35,40,45,47,51,55,69,87,90,93,96,117,125,134,145,146,147,160,162,199}},
		{{507}, {2,3,7,11,13,15,28,34,43,50,57,64,80,83,86,89,107,115,116,127,149,163,175,183,217}},
		{{512}, {1,7,8,9,10,15,22,32,34,46,51,65,69,71,91,105,109,111,136,139,152,157,173,200,203}},
		{{512}, {1,6,7,8,9,13,17,19,35,45,47,57,62,73,88,93,104,107,128,130,151,163,184,198,221}},
		{{513}, {6,9,10,17,19,24,28,29,37,39,64,65,68,81,98,99,102,115,145,147,153,159,165,189,201}},
		{{517}, {5,6,7,16,20,24,28,33,38,43,63,71,80,83,86,92,98,122,132,148,164,166,173,180,205}},
		{{524}, {9,12,20,21,33,35,37,39,54,55,61,62,87,90,98,101,125,132,135,141,145,159,163,164,220}},
		{{527}, {11,12,13,14,19,30,41,47,50,52,59,68,71,81,94,97,107,132,147,151,155,169,175,183,197}},
		{{528}, {2,9,15,17,27,29,31,32,33,36,47,49,50,60,62,69,77,123,127,128,132,141,150,255,273}},
		{{529}, {9,12,20,21,33,35,37,39,54,55,61,62,87,90,98,101,125,132,140,141,145,159,163,169,225}},
		{{531}, {6,9,10,17,19,24,29,31,39,40,67,68,71,84,101,102,105,118,151,153,159,165,171,195,207}},
		{{532}, {16,18,26,27,33,39,41,50,51,55,69,71,84,87,91,94,132,133,141,143,164,168,169,173,195}},
		{{534}, {11,13,15,17,18,27,38,44,49,52,60,61,68,81,87,94,107,135,149,153,159,171,174,189,210}},
		{{535}, {2,8,26,27,36,41,45,57,62,77,88,95,97,99,101,102,109,114,117,118,141,147,168,192,226}},
		{{536}, {1,8,21,30,31,32,33,41,44,46,49,55,57,61,84,91,113,134,137,139,150,155,176,205,247}},
		{{536}, {3,5,9,11,12,21,24,27,30,44,45,50,54,55,57,63,95,117,123,134,140,145,156,257,279}},
		{{540}, {1,7,8,9,10,14,19,34,36,51,58,69,81,83,97,109,111,115,136,149,152,167,183,208,221}},
		{{540}, {6,13,15,25,28,36,43,47,55,57,58,59,60,65,82,89,91,107,124,127,144,163,183,233,250}},
		{{540}, {8,9,10,11,16,30,36,38,45,55,57,65,68,81,84,95,98,100,116,117,126,135,144,261,279}},
		{{540}, {8,9,10,11,16,30,36,38,45,55,57,65,68,81,84,95,98,100,116,117,126,135,144,261,279}},
		{{540}, {4,6,9,10,17,21,23,25,31,33,36,38,45,50,81,83,115,117,126,133,135,144,146,261,279}},
		{{540}, {4,6,9,10,17,21,23,25,31,33,36,38,45,50,81,83,115,117,126,133,135,144,146,261,279}},
		{{541}, {3,4,11,13,16,17,21,25,26,44,46,64,75,86,87,97,106,109,133,141,165,185,191,215,217}},
		{{541}, {3,5,27,32,33,37,47,50,53,56,57,69,71,78,97,98,109,111,126,144,165,169,183,189,232}},
		{{544}, {1,7,24,26,33,35,40,45,47,51,55,69,87,90,93,96,117,125,134,145,147,184,198,199,200}},
		{{544}, {6,8,20,21,23,41,42,48,59,61,77,80,81,85,90,92,93,102,115,132,139,168,198,207,244}},
		{{547}, {3,5,16,22,26,27,35,47,49,59,67,71,72,85,87,102,103,111,137,144,150,197,200,203,207}},
		{{549}, {4,10,14,24,26,31,34,36,38,40,43,48,59,63,74,89,97,105,117,124,136,152,156,241,308}},
		{{550}, {1,2,5,13,19,20,25,30,39,43,58,59,73,75,76,90,95,103,116,128,130,132,172,262,288}},
		{{550}, {1,11,16,23,24,27,29,36,41,43,44,47,59,70,71,80,99,103,111,116,128,156,167,227,323}},
		{{551}, {3,5,24,25,26,30,35,36,39,40,42,57,68,76,94,109,120,128,152,162,166,175,176,200,223}},
		{{552}, {5,17,18,22,25,27,32,33,39,59,62,87,91,100,102,111,112,135,137,149,165,168,183,201,204}},
		{{552}, {1,3,4,7,8,9,10,15,18,19,21,41,52,54,73,93,95,123,125,136,138,153,168,261,291}},
		{{556}, {6,8,10,13,19,25,32,37,49,54,58,76,84,91,92,100,107,128,145,156,165,185,195,205,206}},
		{{556}, {3,12,13,15,19,23,27,34,35,39,42,45,48,52,53,87,140,145,158,166,171,184,189,201,227}},
		{{556}, {3,12,13,15,19,23,27,34,35,39,42,45,48,52,53,87,140,145,158,166,171,184,189,201,227}},
		{{556}, {1,5,7,8,9,10,12,14,20,27,31,43,47,50,74,93,97,121,125,139,143,153,167,264,292}},
		{{562}, {2,3,5,8,13,19,20,29,33,47,53,54,64,65,76,93,119,123,142,157,161,180,184,221,259}},
		{{570}, {3,9,10,33,36,38,40,42,50,51,60,69,72,75,77,90,113,140,141,151,152,189,200,229,230}},
		{{575}, {4,6,14,16,31,39,63,69,74,81,88,103,107,111,115,120,131,132,133,147,156,159,164,198,218}},
		{{576}, {1,4,9,11,15,19,22,34,36,53,60,76,82,84,104,126,127,128,153,156,165,174,183,219,237}},
		{{576}, {8,9,10,11,16,30,36,38,45,55,57,65,68,81,84,95,98,100,116,135,144,153,162,279,297}},
		{{576}, {4,6,9,10,17,21,23,25,31,33,36,38,45,50,81,83,115,133,135,144,146,153,162,279,297}},
		{{580}, {2,5,7,10,12,13,19,21,22,29,36,40,61,65,74,101,135,139,161,179,183,192,205,209,236}},
		{{580}, {5,6,11,13,16,17,21,25,34,44,54,68,80,88,100,112,120,135,142,145,170,173,195,215,265}},
		{{580}, {11,12,16,17,29,32,39,41,53,55,59,60,68,70,81,84,92,124,125,128,129,156,171,280,300}},
		{{593}, {13,14,15,35,48,51,55,67,73,79,83,91,94,105,109,116,119,124,133,150,171,173,196,217,226}},
		{{595}, {4,13,18,19,22,35,40,48,58,61,62,77,78,82,83,86,118,149,163,168,187,192,202,206,240}},
		{{601}, {7,8,25,34,41,42,46,48,54,55,62,70,71,74,98,103,116,143,168,169,190,192,193,218,240}},
		{{603}, {7,11,12,14,21,25,32,40,52,56,60,67,68,81,91,92,132,144,149,163,177,191,196,235,263}},
		{{603}, {13,23,26,27,35,44,45,49,53,54,57,66,75,99,101,110,122,126,144,158,175,180,189,234,270}},
		{{607}, {6,8,10,13,19,25,32,37,49,54,58,76,84,91,92,100,107,128,156,185,196,205,206,216,246}},
		{{609}, {9,14,15,17,32,45,47,58,67,74,76,79,80,83,97,111,125,126,150,170,186,188,215,224,235}},
		{{611}, {1,10,22,26,32,41,45,54,57,61,62,66,85,86,87,95,97,101,119,132,136,167,176,268,343}},
		{{614}, {15,22,24,31,33,49,53,54,57,60,63,68,74,81,83,104,109,151,155,163,167,217,229,230,234}},
		{{634}, {15,17,24,26,33,43,44,54,57,60,63,73,79,81,88,109,119,160,161,172,173,227,234,235,239}},
		{{643}, {2,9,21,29,38,40,41,42,58,62,67,76,82,83,85,96,104,166,172,186,192,201,207,250,270}},
		{{644}, {7,9,13,18,19,22,31,49,53,61,66,68,71,87,93,94,119,164,178,192,199,206,227,239,253}},
		{{655}, {10,14,15,21,25,26,31,40,51,53,54,57,65,83,84,86,151,152,173,193,194,215,216,246,288}},
		{{661}, {5,7,17,18,23,31,36,38,41,64,73,77,83,84,102,106,111,161,175,196,203,210,238,248,262}}
	};

	/**
	 * It runs a perfect square problem. If no problemNo specified as input 
	 * argument it will solve all the problems given in square matrix.
	 * 
	 * @param args program parameters, the first one denotes the problem no to be solved.
	 */
	public static void test(String args[]) {

		if (args.length == 0) {
				
			for( int i = 0; i < squares.length; i++) {

				problemNo = i;

				System.out.println("Problem no. " + i);
				
				PerfectSquare example = new PerfectSquare();

				example.model();
				example.search();

//				example = new PerfectSquare();
//				example.modelGeost();
//				example.search();
				
			}

			return;
		}

	
		PerfectSquare example = new PerfectSquare();
	
		if (args.length == 1) {

			String number = args[0];
			Integer i = new Integer(number);
			problemNo = i.intValue();
			
		}
				
		example.model();
		example.search();

		example = new PerfectSquare();

		example.modelBasic();
		example.search();
		
		example = new PerfectSquare();
		example.modelGeost();
		example.search();
		
	}

	
	/**
	 * It runs a perfect square problem. If no problemNo specified as input 
	 * argument it will solve all the problems given in square matrix.
	 * 
	 * @param args program parameters, the first one denotes the problem no to be solved.
	 */
	public static void main(String args[]) {

	
		PerfectSquare example = new PerfectSquare();
	
		if (args.length == 1) {

			String number = args[0];
			Integer i = new Integer(number);
			problemNo = i.intValue();
			
		}
		else 
			problemNo = squares.length - 1;
				
		example.model();
		example.search();
		
	}

	
	/**
	 * It specifies the model using mostly PrimitiveConstraints. It does
	 * not use diff2 constraint which is very useful for placing 2-dimensional
	 * rectangles.
	 */
	public void modelBasic() {

		store = new Store();

		int numberOfRectangles = squares[problemNo][1].length;
		int masterSize = squares[problemNo][0][0];

		varsX = new IntVar[numberOfRectangles];
		varsY = new IntVar[numberOfRectangles];
		size = new IntVar[numberOfRectangles];

		System.out.print("Constraint model without use of Diff2 constraint");
		System.out.println("No squares = " + numberOfRectangles + " Size = " + masterSize);
		System.out.print("Square size = [");

		for (int j = numberOfRectangles - 1; j >= 0; j--) {

			int sqSize = squares[problemNo][1][j];

			IntVar X = new IntVar(store, "x"+j, 0, masterSize-sqSize);
			
			IntVar Y = new IntVar(store, "y"+j, 0, masterSize-sqSize);
			
			size[j] = new IntVar(store, sqSize, sqSize);

			varsX[j] = X; varsY[j] = Y;
			
			System.out.print(sqSize + " ");
		}
		
		System.out.println("]");

		IntVar[] endX = new IntVar[varsX.length];
		IntVar[] endY = new IntVar[varsY.length];

		for (int i=0; i<varsX.length; i++) {
			endX[i] = new IntVar(store, 0, masterSize);
			endY[i] = new IntVar(store, 0, masterSize);
			store.impose(new XplusCeqZ(varsX[i], squares[problemNo][1][i], endX[i]));
			store.impose(new XplusCeqZ(varsY[i], squares[problemNo][1][i], endY[i]));
		}

		for (int i = 0; i < varsX.length; i++) 
			for (int j = 0; j < varsY.length; j++)
				if (i != j) {
					PrimitiveConstraint[] orArray = {
							new XlteqY(endX[i], varsX[j]),
							new XgteqY(varsX[i], endX[j]),
							new XlteqY(endY[i], varsY[j]),
							new XgteqY(varsY[i], endY[j]) };
					
					store.impose(new Or(orArray));
				}

		IntVar limit = new IntVar(store, masterSize, masterSize);

		for (int i = 0; i < masterSize - 1; i++) {
			
			ArrayList<IntVar> sumList = new ArrayList<IntVar>();
			
			for (int j = 0; j<varsX.length; j++) {
				IntVar b = new IntVar(store, 0, 1);
				store.impose(new Reified(new And(new XlteqC(varsX[j], i), new XgtC(endX[j], i)), b));
				IntVar s = new IntVar(store, 0, masterSize);
				store.impose(new XmulCeqZ(b, squares[problemNo][1][j], s));
				sumList.add(s);
			}
			
			store.impose(new Sum(sumList, limit));
		
		}

		for (int i=0; i<masterSize-1; i++) {
			
			ArrayList<IntVar> sumList = new ArrayList<IntVar>();
			
			for (int j=0; j<varsY.length; j++) {
				IntVar b = new IntVar(store, 0, 1);
				store.impose(new Reified(new And(new XlteqC(varsY[j], i), new XgtC(endY[j], i)), b));
				IntVar s = new IntVar(store, 0, masterSize);
				store.impose(new XmulCeqZ(b, squares[problemNo][1][j], s));
				sumList.add(s);
			}
			store.impose(new Sum(sumList, limit));
		}

		System.out.println("Number of variables: " + store.size());
		System.out.println("Number of constraints: " + store.numberConstraints());		

	}
	
	@Override
	public void model() {
		
		store = new Store();

		int noRectangles = squares[problemNo][1].length;
		
		int masterSize = squares[problemNo][0][0];

		varsX = new IntVar[noRectangles];
		varsY = new IntVar[noRectangles];
		size = new IntVar[noRectangles];

		IntVar[][] rectangles = new IntVar[noRectangles][4];

		System.out.print("Constraint model based on Diff2 constraint");
		System.out.println("Example " + problemNo + "  No squares = " + noRectangles + " Size = " + masterSize);
		System.out.print("Square size = [");

		for (int j = noRectangles - 1; j >= 0; j--) {
			
			int sqSize = squares[problemNo][1][j];
			
			IntVar X = new IntVar(store, "x"+j, 0, masterSize - sqSize);
			
			IntVar Y = new IntVar(store, "y"+j, 0, masterSize - sqSize);
			
			size[j] = new IntVar(store, sqSize, sqSize);
			
			IntVar[] jthRectangle = {X, Y, size[j], size[j]};

			rectangles[j] = jthRectangle;

			varsX[j] = X; varsY[j] = Y;
	
			System.out.print(sqSize + " ");
		
		}
		
		System.out.println("]");

		store.impose(new Diff2(rectangles));

		System.out.println("Number of variables: " + store.size());
		System.out.println("Number of constraints: " + store.numberConstraints());

		
	}

	
	public void modelGeost() {
		
		store = new Store();

		int noRectangles = squares[problemNo][1].length;
		
		int masterSize = squares[problemNo][0][0];

		varsX = new IntVar[noRectangles];
		varsY = new IntVar[noRectangles];
		size = new IntVar[noRectangles];

		IntVar[][] rectangles = new IntVar[noRectangles][4];

		ArrayList<GeostObject> objects = new ArrayList<GeostObject>();
		ArrayList<ExternalConstraint> constraints = new ArrayList<ExternalConstraint>(); 
		ArrayList<Shape> shapes = new ArrayList<Shape>();
		
		System.out.print("Constraint model based on Geost and Diff2 constraint");
		System.out.println("Example " + problemNo + "  No squares = " + noRectangles + " Size = " + masterSize);
		System.out.print("Square size = [");

		for (int j = noRectangles - 1; j >= 0; j--) {
			
			int sqSize = squares[problemNo][1][j];
			
			IntVar X = new IntVar(store, "x"+j, 0, masterSize - sqSize);
			IntVar Y = new IntVar(store, "y"+j, 0, masterSize - sqSize);
			IntVar S = new IntVar(store, "s"+j, j, j);

			IntVar startGeost = new IntVar(store, "start"+j, 0, 0);
			IntVar durationGeost = new IntVar(store, "duration"+j, 1, 1);
			IntVar endGeost = new IntVar(store, "end"+j, 1, 1);

			size[j] = new IntVar(store, sqSize, sqSize);
			
			IntVar[] jthRectangle = {X, Y, size[j], size[j]};

			rectangles[j] = jthRectangle;

			varsX[j] = X; varsY[j] = Y;
	
			System.out.print(sqSize + " ");
		
			IntVar[] coords = {X, Y};
			
			GeostObject o = new GeostObject(j, coords, S, startGeost, durationGeost, endGeost);
			objects.add(o);
			
			int[] origin = {0, 0};
			int[] length = {sqSize, sqSize};
			
			Shape shape = new Shape(j, new DBox(origin, length));
			shapes.add(shape);
			
		}
		
		int[] dimensions = {0, 1};
		
		NonOverlapping constraint = new NonOverlapping(objects, dimensions);
		constraints.add(constraint);
		
		System.out.println("]");

		// objects, constraints, shapes.
		// Geost does not employ area reasoning and it is loosing greatly 
		// unless employed with Diff2. Geost can not prune significantly
		// more than Diff2. 
		store.impose(new Geost(objects, constraints, shapes));
		// the main pruning component still.
		store.impose(new Diff2(rectangles));
		
		/*
		// starts, durations, resources, limit
		// Not really useful implied constraints
		// Variable limit = new Variable(store, "limit", masterSize, masterSize);
		// store.impose(new Cumulative(varsX, size, size, limit));
		// store.impose(new Cumulative(varsY, size, size, limit));

		// {above, below, left, right}
		int [][] relation = { {1, 0, 1, 0}, {0, 1, 1, 0}, {0, 0, 1, 0}, 
							{1, 0, 0, 1}, {0, 1, 0, 1}, {0, 0, 0, 1},
							{1, 0, 0, 0}, {0, 1, 0, 0}};

		vars = new ArrayList<Var>();
		
		for (int i = noRectangles - 1; i > 0; i--)
			for (int j = i - 1; j >= 0; j--) {

			IntVar above = new IntVar(store, i+"-th-above-"+(j)+"-th", 0, 1);			
			store.impose(new Reified(new XplusClteqZ(varsY[j], size[j].value(), varsY[i]), above));

			IntVar below = new IntVar(store, i+"-th-below-"+(j)+"-th", 0, 1);
			store.impose(new Reified(new XplusClteqZ(varsY[i], size[i].value(), varsY[j]), below));
			
			IntVar right = new IntVar(store, i+"-th-right-"+(j)+"-th", 0, 1);
			store.impose(new Reified(new XplusClteqZ(varsX[j], size[j].value(), varsX[i]), right));

			IntVar left = new IntVar(store, i+"-th-left-"+(j)+"-th", 0, 1);
			store.impose(new Reified(new XplusClteqZ(varsX[i], size[i].value(), varsX[j]), above));

			IntVar [] positions = {above, below, right, left}; 
			store.impose(new ExtensionalSupportSTR(positions, relation));
			
			
			//vars.add(above);
			//vars.add(below);
			//vars.add(right);
			//vars.add(left);
			
		}
		
		for (int i = noRectangles - 1; i >= 0; i--) {
			vars.add(varsX[i]);
			vars.add(varsY[i]);			
		}
		
		*/
		
		System.out.println("Number of variables: " + store.size());
		System.out.println("Number of constraints: " + store.numberConstraints());
		
	}

	@Override
	public boolean search() {

		long T1, T2, T;
		T1 = System.currentTimeMillis();

		boolean result = store.consistency();

		Search<IntVar> labelSlave1 = new DepthFirstSearch<IntVar>();
		SelectChoicePoint<IntVar> selectSlave1 = 
			new SimpleSelect<IntVar>(varsY, new SmallestMin<IntVar>(), new SmallestDomain<IntVar>(),
					new IndomainMin<IntVar>());
		
		labelSlave1.setSelectChoicePoint(selectSlave1);
		labelSlave1.setPrintInfo(false);

		Search<IntVar> labelMaster = new DepthFirstSearch<IntVar>();
		SelectChoicePoint<IntVar> selectMaster = 
			new SimpleSelect<IntVar>(varsX, new SmallestMin<IntVar>(), new SmallestDomain<IntVar>(),
					new IndomainMin<IntVar>());

		labelMaster.addChildSearch(labelSlave1);
		
		result = labelMaster.labeling(store, selectMaster);

		T2 = System.currentTimeMillis();
		T = T2 - T1;

		String s = String.format("%.2f", (float)T/1000);
		System.out.println("\n\t*** Execution time = "+ s + " s");

		if (result) {

			System.out.print("Positions of rectangles : (");
			
			for (int i = 0; i < varsX.length; i++)
				if (i < varsX.length -1)
					System.out.print("(" + varsX[i] + ", " + varsY[i] + "), ");
				else
					System.out.print("(" + varsX[i] + ", " + varsY[i] + ")");
			
			System.out.println(")");
			
		// If needed a latex representation of the solution can be generated.	
		//	System.out.println( printLaTex(T) );
			
		}
		
		return result;
		
	}




	/**
	 * Enclose the output of this function inside a simple latex document like the one 
	 * below. Remove additional "\" before usepackage as it was added to avoid conflict
	 * with Doxygen. 
	 * 
	  \documentclass[]{article}
	  \\usepackage{color}
	  \hyphenation{}
	  \makeatother
	  \begin{document}
	  \thispagestyle{empty}
	  \include{figure}
	  \end{document}
	 * 
	 * @param runtime it specifies the time required to find a solution.
	 * @return latex representation of the solution in a single string.
	 */

	public String printLaTex(long runtime) {

		StringBuffer result = new StringBuffer();

		result.append ("Solution to PerfectSquare problem of master size equal to " + squares[problemNo][0][0] + "\n\n");

		IntVar[] xl = size; 
		IntVar[] yl = size;

		// Print the geometry information latex format:
		int xlen = 0, ylen=0;

		float picxsize, picysize;
		
		for (int i = 0; i < xl.length; i++)
			xlen = (xlen < varsX[i].value() + xl[i].value()) ?	varsX[i].value() + xl[i].value() : xlen;
					
		for (int i = 0; i < yl.length; i++)
			ylen = (ylen < varsY[i].value() + yl[i].value()) ?	varsY[i].value() + yl[i].value() : ylen;

		float scalefac = 300/(float)xlen;

		picxsize=xlen*scalefac; 
		picysize=ylen*scalefac;
		result.append("\\begin{picture}(").append(picxsize).append(",");
		result.append( picysize ).append(")(0,0)\n");
		
		result.append("\\thicklines\n");
		result.append("\\put(0,0){\\framebox(").append(xlen*scalefac);
		result.append(",").append(ylen*scalefac).append("){}}\n");
		result.append("\\thinlines\n");

		result.append("\\setlength{\\fboxrule}{0pt}\n");
		result.append("\\setlength{\\fboxsep}{0pt}\n");
		result.append("\\tiny\n");

		for (int i = 0; i < varsX.length; i++) {
			
			int bnr, xc, yc, sizex, sizey;
			bnr = i;   // block number
			xc = varsX[i].value();
			yc = varsY[i].value();    // slot y coordinate
			sizex = xl[bnr].value(); // x size of block
			sizey = yl[bnr].value(); // y size of block

			// If the block has been rotated, we exchange x and y size:
			float blockx, blocky;
			blockx = sizex * scalefac;
			blocky = sizey * scalefac;

			// Print the colored block:
			result.append("\\put(").append( xc*scalefac ).append(",").append(yc*scalefac);
			result.append("){\\colorbox{yellow}{\\framebox(").append( blockx );
			result.append(",").append( blocky ).append( ")" ).append( "{" );
			result.append( bnr ).append( "}}}\n" );
		}

		// Write somewhere the area and lost area:
		result.append("\n");
		result.append("\\normalsize\n");
		result.append("\\put(").append( xlen*scalefac+5 ).append( ",10){Run time: ");
		result.append( runtime ).append(" ms}\n");
		result.append ("\\end{picture}\n");
		// End printing picture environment

		return result.toString();

	}
}
