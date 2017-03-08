/**
 * ExampleBasedTest.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop;

import static org.junit.Assert.*;

import org.jacop.examples.fd.*;
import org.jacop.examples.fd.carsequencing.CarSequencing;
import org.junit.Test;
import scala.tools.nsc.transform.patmat.Logic;


/**
 *
 * It is performing testing based on the examples present in the library.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.4
 */
public class ExampleBasedTest {


    @Test public void testCarSequencing() {

        CarSequencing example = new CarSequencing();

        CarSequencing.readFromArray(CarSequencing.problem, example);

        example.model();

        String[] description = CarSequencing.toStringArray(example);

        for (String line : description)
            System.out.println(line);

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(6, example.search.getSolutionListener().solutionsNo());
    }


    @Test public void testArchFriends() {

        ArchFriends example = new ArchFriends();
        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(1, example.search.getSolutionListener().solutionsNo());

    }

    @Test public void testBabySitting() {

        BabySitting example = new BabySitting();

        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(1, example.search.getSolutionListener().solutionsNo());

    }

    @Test public void testBasicLogicPascal() {

        BasicLogicPascal example = new BasicLogicPascal();

        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(1, example.search.getSolutionListener().solutionsNo());

    }

    @Test public void testBIBD() {

        BIBD example = new BIBD();

        example.v = 7;
        example.b = 7;
        example.r = 3;
        example.k = 3;
        example.lambda = 1;

        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(151200, example.search.getSolutionListener().solutionsNo());

    }


    @Test public void testBlueberryMuffins() {

        BlueberryMuffins example = new BlueberryMuffins();

        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(24, example.search.getSolutionListener().solutionsNo());

    }


    @Test public void testBreakingNews() {

        BreakingNews example = new BreakingNews();

        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(480, example.search.getSolutionListener().solutionsNo());
    }

    @Test public void testBuildingBlocks() {

        BuildingBlocks example = new BuildingBlocks();

        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(24, example.search.getSolutionListener().solutionsNo());
    }

    @Test public void testCalendarMenBasicModel() {

        CalendarMen exampleBasic = new CalendarMen();

        exampleBasic.modelBasic();

        assertEquals(true, exampleBasic.searchAllAtOnce());
        assertEquals(1, exampleBasic.search.getSolutionListener().solutionsNo());

        exampleBasic.getSearch().assignSolution();

        assertEquals("[Antonio = 3,Brett = 10,Cliff = 2,Dabney = 6,Ed = 9,Francisco = 7,Griff = 5,Harry = 11,Ivor = 12,John = 1,Karl = 4,Lorentzo = 8,Moross = 6,Nelsen = 4,ORourke = 9,Paulos = 5,Quarello = 8,Reede = 1,Sheldon = 10,Taylor = 7,Uhler = 11,Vickers = 12,Wang = 2,Xiao = 3,archery = 9,badmington = 11,croquet = 10,football = 12,golf = 1,hockey = 5,lacrosse = 8,offset1 = 3,offset2 = 6,p_vauliting = 3,rowing = 7,squash = 2,tennis = 6,volleyball = 4]",
            exampleBasic.store.toStringOrderedVars() );
    }

    @Test public void testCalendarMen() {

        CalendarMen example = new CalendarMen();

        example.model();

        assertEquals(true, example.searchAllAtOnce());

        assertEquals(1, example.search.getSolutionListener().solutionsNo());

        example.getSearch().assignSolution();
        
        assertEquals("[Antonio = 3,Brett = 10,Cliff = 2,Dabney = 6,Ed = 9,Francisco = 7,Griff = 5,Harry = 11,Ivor = 12,John = 1,Karl = 4,Lorenzo = 8,Moross = 6,Nelsen = 4,O_Rourke = 9,Paulos = 5,Quarello = 8,Reede = 1,Sheldon = 10,Taylor = 7,Uhler = 11,Vickers = 12,Wang = 2,Xiao = 3,archery = 9,badminton = 11,c10_1_m = 3,c10_1_x = 8,c10_2_m = 2,c10_2_x = 9,c10_3_m = 1,c10_3_x = 10,c11_1_m = 1,c11_1_x = 9,c11_2_m = 3,c11_2_x = 10,c11_3_m = 2,c11_3_x = 11,c12_1_m = 2,c12_2_m = 1,c12_3_m = 3,c1_1_m = 2,c1_2_m = 3,c1_3_m = 1,c2_1_m = 1,c2_1_x = 4,c2_2_m = 3,c2_2_x = 5,c2_3_m = 2,c2_3_x = 6,c4_1_m = 3,c4_2_m = 2,c4_3_m = 1,c9_1_m = 2,c9_2_m = 1,c9_3_m = 3,croquet = 10,even = 6,football = 12,golf = 1,hockey = 5,lacrosse = 8,rowing = 7,squash = 2,tennis = 6,vaulting = 3,volleyball = 4]",
            example.store.toStringOrderedVars());

    }

    @Test public void testConference() {

        Conference example = new Conference();

        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(2, example.search.getSolutionListener().solutionsNo());

    }

    @Test public void testCryptogram() {

        String lines[][] =
            {{"CRACK", "HACK", "ERROR"}, {"PEAR", "APPLE", "GRAPE"}, {"CRACKS", "TRACKS", "RACKET"}, {"TRIED", "RIDE", "STEER"},
                {"DEEMED", "SENSE", "SYSTEM"}, {"DOWN", "WWW", "ERROR"}, {"BARREL", "BROOMS", "SHOVELS"}, {"LYNNE", "LOOKS", "SLEEPY"},
                {"STARS", "RATE", "TREAT"}, {"DAYS", "TOO", "SHORT"}, {"BASE", "BALL", "GAMES"}, {"MEMO", "FROM", "HOMER"},
                {"IS", "THIS", "HERE"}};

        int noSol[] = {1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1};

        for (int i = 0; i < lines.length; i++) {

            Cryptogram exampleLeft = new Cryptogram();
            exampleLeft.lines[0] = lines[i][0] + "+" + lines[i][1] + "=" + lines[i][2];
            exampleLeft.noLines = 1;

            exampleLeft.model();

            assertEquals(true, exampleLeft.searchAllAtOnce());

            assertEquals(noSol[i], exampleLeft.search.getSolutionListener().solutionsNo());

        }

    }

    @Test public void testDebruijnSequence() {

        DeBruijn example = new DeBruijn();
        example.base = 2;
        example.n = 4;
        example.m = 9;

        example.model();

        assertEquals(true, example.searchAllAtOnce());

        // prints then de Bruijn sequences
        System.out.print("de Bruijn sequence:");

        System.out.print("decimal values: ");
        for (int i = 0; i < example.m; i++) {
            System.out.print(example.x[i].value() + " ");
        }
        System.out.println();

        System.out.println("\nbinary:");

        for (int i = 0; i < example.m; i++) {
            for (int j = 0; j < example.n; j++) {
                System.out.print(example.binary[i][j].value() + " ");
            }
            System.out.println(" : " + example.x[i].value());
        }

        assertEquals(14, example.search.getSolutionListener().solutionsNo());

    }


    @Test public void testDietSumWeight() {

        System.out.println("Searching for all solutions using sum weight constraints");

        Diet exampleSumWeight = new Diet();

        exampleSumWeight.model();

        assertEquals(exampleSumWeight.searchAllAtOnce(), true);

        Diet.printLastSolution(exampleSumWeight);

        assertEquals(6, exampleSumWeight.search.getSolutionListener().solutionsNo());

    }


    @Test public void testDiet() {

        System.out.println("Searching for all solutions using knapsack constraints");
        Diet exampleKnapsack = new Diet();

        exampleKnapsack.modelKnapsack();

        assertEquals(exampleKnapsack.searchAllAtOnce(), true);

        Diet.printLastSolution(exampleKnapsack);

        assertEquals(6, exampleKnapsack.search.getSolutionListener().solutionsNo());
    }



    @Test public void testDolarAndTicket() {

        DollarAndTicket example = new DollarAndTicket();

        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(36, example.search.getSolutionListener().solutionsNo());
    }


    @Test public void testDonaldGeraldRobert() {

        DonaldGeraldRobert example = new DonaldGeraldRobert();

        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(1, example.search.getSolutionListener().solutionsNo());

    }

    @Test public void testExodus() {

        Exodus example = new Exodus();

        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(6, example.search.getSolutionListener().solutionsNo());
    }

    @Test public void testFittingNumbers() {

        FittingNumbers example = new FittingNumbers();

        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(6967, example.search.getSolutionListener().solutionsNo());
    }



    @Test public void testFlowers() {

        Flowers example = new Flowers();
        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(1, example.search.getSolutionListener().solutionsNo());
    }

    @Test public void testFourIslands() {

        FourIslands example = new FourIslands();
        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(1, example.search.getSolutionListener().solutionsNo());
    }

    @Test public void testFurnitureMoving() {

        FurnitureMoving example = new FurnitureMoving();
        example.model();

        assertEquals(true, example.searchSpecific());
        assertEquals(36, example.search.getSolutionListener().solutionsNo());

    }


    @Test public void testGates() {

        Gates example = new Gates();
        example.model();

        assertEquals(true, example.searchSpecific());
        assertEquals(8, example.search.getSolutionListener().solutionsNo());

    }

    @Test public void testGolf() {

        Golf example = new Golf();
        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(1, example.search.getSolutionListener().solutionsNo());
    }

    @Test public void testGolomb() {

        Golomb example = new Golomb();
        example.model();

        assertEquals(true, example.searchOptimalInfo());

        int optimalCost = example.cost.value();

        example = new Golomb();
        example.bound = optimalCost;
        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(1, example.search.getSolutionListener().solutionsNo());

    }

    @Test public void testHistoricHomes() {

        HistoricHomes example = new HistoricHomes();
        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(1, example.search.getSolutionListener().solutionsNo());
    }



    @Test public void testKakro() {

        Kakro example = new Kakro();

        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(1, example.search.getSolutionListener().solutionsNo());

    }


    @Test public void testKnapsack() {

        KnapsackExample example = new KnapsackExample();

        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(18, example.search.getSolutionListener().solutionsNo());
    }

    @Test public void testLangford() {

        Langford example = new Langford();
        example.n = 3;
        example.m = 10;
        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(10, example.search.getSolutionListener().solutionsNo());
    }


    @Test public void testLectureSeries() {

        LectureSeries example = new LectureSeries();

        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(120, example.search.getSolutionListener().solutionsNo());
    }

    @Test public void testMagicSquares() {

        MagicSquares example = new MagicSquares();

        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(1760, example.search.getSolutionListener().solutionsNo());
    }

    @Test public void testMasterClass() {

        MasterClass example = new MasterClass();
        example.model();

        assertEquals(true, example.searchAllAtOnce());
        assertEquals(12, example.search.getSolutionListener().solutionsNo());
    }


    @Test public void testMineSweeper() {

        MineSweeper minesweeper = new MineSweeper();

        String[] results = {"[m_0_0=1,m_0_1=0,m_0_2=0,m_0_3=0,m_0_4=0,m_0_5=1,m_1_0=0,m_1_1=1,m_1_2=0,m_1_3=1,m_1_4=1,m_1_5=0,m_2_0=0,m_2_1=0,m_2_2=0,m_2_3=0,m_2_4=1,m_2_5=0,m_3_0=0,m_3_1=0,m_3_2=0,m_3_3=0,m_3_4=1,m_3_5=0,m_4_0=0,m_4_1=1,m_4_2=1,m_4_3=1,m_4_4=0,m_4_5=0,m_5_0=1,m_5_1=0,m_5_2=0,m_5_3=0,m_5_4=1,m_5_5=1,g_0_0::{-1..8},g_0_1::{-1..8},g_0_2 = 2,g_0_3::{-1..8},g_0_4 = 3,g_0_5::{-1..8},g_1_0 = 2,g_1_1::{-1..8},g_1_2::{-1..8},g_1_3::{-1..8},g_1_4::{-1..8},g_1_5::{-1..8},g_2_0::{-1..8},g_2_1::{-1..8},g_2_2 = 2,g_2_3 = 4,g_2_4::{-1..8},g_2_5 = 3,g_3_0 = 1,g_3_1::{-1..8},g_3_2 = 3,g_3_3 = 4,g_3_4::{-1..8},g_3_5::{-1..8},g_4_0::{-1..8},g_4_1::{-1..8},g_4_2::{-1..8},g_4_3::{-1..8},g_4_4::{-1..8},g_4_5 = 3,g_5_0::{-1..8},g_5_1 = 3,g_5_2::{-1..8},g_5_3 = 3,g_5_4::{-1..8},g_5_5::{-1..8}]",
                            "[m_0_0=0,m_0_1=0,m_0_2=1,m_0_3=0,m_0_4=0,m_0_5=0,m_0_6=1,m_0_7=0,m_1_0=1,m_1_1=0,m_1_2=0,m_1_3=1,m_1_4=0,m_1_5=0,m_1_6=0,m_1_7=0,m_2_0=0,m_2_1=1,m_2_2=1,m_2_3=0,m_2_4=0,m_2_5=1,m_2_6=0,m_2_7=1,m_3_0=0,m_3_1=0,m_3_2=0,m_3_3=0,m_3_4=0,m_3_5=0,m_3_6=1,m_3_7=0,m_4_0=1,m_4_1=0,m_4_2=0,m_4_3=0,m_4_4=1,m_4_5=0,m_4_6=0,m_4_7=1,m_5_0=0,m_5_1=0,m_5_2=1,m_5_3=0,m_5_4=0,m_5_5=1,m_5_6=1,m_5_7=0,m_6_0=0,m_6_1=0,m_6_2=0,m_6_3=0,m_6_4=0,m_6_5=0,m_6_6=0,m_6_7=1,m_7_0=0,m_7_1=1,m_7_2=0,m_7_3=0,m_7_4=1,m_7_5=0,m_7_6=0,m_7_7=0,g_0_0::{-1..8},g_0_1 = 2,g_0_2::{-1..8},g_0_3 = 2,g_0_4 = 1,g_0_5 = 1,g_0_6::{-1..8},g_0_7::{-1..8},g_1_0::{-1..8},g_1_1::{-1..8},g_1_2 = 4,g_1_3::{-1..8},g_1_4 = 2,g_1_5::{-1..8},g_1_6::{-1..8},g_1_7 = 2,g_2_0 = 2,g_2_1::{-1..8},g_2_2::{-1..8},g_2_3 = 2,g_2_4::{-1..8},g_2_5::{-1..8},g_2_6 = 3,g_2_7::{-1..8},g_3_0 = 2,g_3_1::{-1..8},g_3_2 = 2,g_3_3 = 2,g_3_4::{-1..8},g_3_5 = 3,g_3_6::{-1..8},g_3_7 = 3,g_4_0::{-1..8},g_4_1::{-1..8},g_4_2 = 1,g_4_3::{-1..8},g_4_4::{-1..8},g_4_5::{-1..8},g_4_6 = 4,g_4_7::{-1..8},g_5_0 = 1,g_5_1::{-1..8},g_5_2::{-1..8},g_5_3::{-1..8},g_5_4 = 2,g_5_5::{-1..8},g_5_6::{-1..8},g_5_7 = 3,g_6_0::{-1..8},g_6_1 = 2,g_6_2::{-1..8},g_6_3 = 2,g_6_4 = 2,g_6_5::{-1..8},g_6_6 = 3,g_6_7::{-1..8},g_7_0 = 1,g_7_1::{-1..8},g_7_2 = 1,g_7_3::{-1..8},g_7_4::{-1..8},g_7_5 = 1,g_7_6::{-1..8},g_7_7 = 1]",
                            "[m_0_0=0,m_0_1=0,m_0_2=0,m_0_3=0,m_0_4=1,m_0_5=0,m_0_6=0,m_0_7=0,m_0_8=0,m_0_9=0,m_1_0=1,m_1_1=0,m_1_2=0,m_1_3=1,m_1_4=0,m_1_5=1,m_1_6=0,m_1_7=1,m_1_8=1,m_1_9=0,m_2_0=1,m_2_1=1,m_2_2=0,m_2_3=0,m_2_4=0,m_2_5=1,m_2_6=0,m_2_7=1,m_2_8=0,m_2_9=0,m_3_0=0,m_3_1=0,m_3_2=0,m_3_3=0,m_3_4=0,m_3_5=0,m_3_6=0,m_3_7=0,m_3_8=1,m_3_9=0,m_4_0=1,m_4_1=0,m_4_2=0,m_4_3=0,m_4_4=0,m_4_5=0,m_4_6=1,m_4_7=0,m_4_8=1,m_4_9=0,m_5_0=0,m_5_1=0,m_5_2=1,m_5_3=0,m_5_4=1,m_5_5=0,m_5_6=0,m_5_7=0,m_5_8=0,m_5_9=0,m_6_0=0,m_6_1=1,m_6_2=0,m_6_3=0,m_6_4=0,m_6_5=0,m_6_6=1,m_6_7=0,m_6_8=0,m_6_9=0,m_7_0=1,m_7_1=0,m_7_2=0,m_7_3=0,m_7_4=1,m_7_5=0,m_7_6=0,m_7_7=0,m_7_8=1,m_7_9=0,m_8_0=0,m_8_1=1,m_8_2=0,m_8_3=1,m_8_4=0,m_8_5=0,m_8_6=1,m_8_7=0,m_8_8=1,m_8_9=1,m_9_0=0,m_9_1=0,m_9_2=1,m_9_3=0,m_9_4=0,m_9_5=1,m_9_6=0,m_9_7=0,m_9_8=0,m_9_9=0,g_0_0 = 1,g_0_1::{-1..8},g_0_2::{-1..8},g_0_3 = 2,g_0_4::{-1..8},g_0_5 = 2,g_0_6::{-1..8},g_0_7 = 2,g_0_8::{-1..8},g_0_9::{-1..8},g_1_0::{-1..8},g_1_1 = 3,g_1_2 = 2,g_1_3::{-1..8},g_1_4::{-1..8},g_1_5::{-1..8},g_1_6 = 4,g_1_7::{-1..8},g_1_8::{-1..8},g_1_9 = 1,g_2_0::{-1..8},g_2_1::{-1..8},g_2_2::{-1..8},g_2_3 = 1,g_2_4 = 3,g_2_5::{-1..8},g_2_6::{-1..8},g_2_7::{-1..8},g_2_8 = 4,g_2_9::{-1..8},g_3_0 = 3,g_3_1::{-1..8},g_3_2 = 1,g_3_3::{-1..8},g_3_4::{-1..8},g_3_5::{-1..8},g_3_6 = 3,g_3_7::{-1..8},g_3_8::{-1..8},g_3_9::{-1..8},g_4_0::{-1..8},g_4_1 = 2,g_4_2 = 1,g_4_3::{-1..8},g_4_4 = 1,g_4_5::{-1..8},g_4_6::{-1..8},g_4_7 = 3,g_4_8::{-1..8},g_4_9 = 2,g_5_0::{-1..8},g_5_1 = 3,g_5_2::{-1..8},g_5_3 = 2,g_5_4::{-1..8},g_5_5::{-1..8},g_5_6 = 2,g_5_7::{-1..8},g_5_8 = 1,g_5_9::{-1..8},g_6_0 = 2,g_6_1::{-1..8},g_6_2::{-1..8},g_6_3 = 3,g_6_4 = 2,g_6_5::{-1..8},g_6_6::{-1..8},g_6_7 = 2,g_6_8::{-1..8},g_6_9::{-1..8},g_7_0::{-1..8},g_7_1 = 3,g_7_2::{-1..8},g_7_3::{-1..8},g_7_4::{-1..8},g_7_5 = 3,g_7_6 = 2,g_7_7::{-1..8},g_7_8::{-1..8},g_7_9 = 3,g_8_0::{-1..8},g_8_1::{-1..8},g_8_2 = 3,g_8_3::{-1..8},g_8_4 = 3,g_8_5 = 3,g_8_6::{-1..8},g_8_7::{-1..8},g_8_8::{-1..8},g_8_9::{-1..8},g_9_0::{-1..8},g_9_1 = 2,g_9_2::{-1..8},g_9_3 = 2,g_9_4::{-1..8},g_9_5::{-1..8},g_9_6::{-1..8},g_9_7 = 2,g_9_8 = 2,g_9_9::{-1..8}]",
                            "[m_0_0=0,m_0_1=1,m_0_2=0,m_0_3=1,m_0_4=0,m_0_5=0,m_0_6=0,m_0_7=0,m_1_0=1,m_1_1=0,m_1_2=1,m_1_3=0,m_1_4=1,m_1_5=1,m_1_6=0,m_1_7=0,m_2_0=1,m_2_1=1,m_2_2=0,m_2_3=1,m_2_4=0,m_2_5=0,m_2_6=1,m_2_7=0,m_3_0=0,m_3_1=0,m_3_2=1,m_3_3=1,m_3_4=0,m_3_5=1,m_3_6=0,m_3_7=1,m_4_0=0,m_4_1=0,m_4_2=0,m_4_3=0,m_4_4=0,m_4_5=1,m_4_6=1,m_4_7=0,m_5_0=0,m_5_1=1,m_5_2=0,m_5_3=1,m_5_4=1,m_5_5=0,m_5_6=0,m_5_7=0,m_6_0=0,m_6_1=1,m_6_2=1,m_6_3=1,m_6_4=0,m_6_5=1,m_6_6=0,m_6_7=1,m_7_0=0,m_7_1=0,m_7_2=1,m_7_3=0,m_7_4=0,m_7_5=1,m_7_6=1,m_7_7=0,g_0_0 = 2,g_0_1::{-1..8},g_0_2::{-1..8},g_0_3::{-1..8},g_0_4 = 3,g_0_5::{-1..8},g_0_6 = 1,g_0_7::{-1..8},g_1_0::{-1..8},g_1_1 = 5,g_1_2::{-1..8},g_1_3 = 4,g_1_4::{-1..8},g_1_5::{-1..8},g_1_6::{-1..8},g_1_7 = 1,g_2_0::{-1..8},g_2_1::{-1..8},g_2_2 = 5,g_2_3::{-1..8},g_2_4::{-1..8},g_2_5 = 4,g_2_6::{-1..8},g_2_7::{-1..8},g_3_0 = 2,g_3_1::{-1..8},g_3_2::{-1..8},g_3_3::{-1..8},g_3_4 = 4,g_3_5::{-1..8},g_3_6 = 5,g_3_7::{-1..8},g_4_0::{-1..8},g_4_1 = 2,g_4_2::{-1..8},g_4_3 = 4,g_4_4::{-1..8},g_4_5::{-1..8},g_4_6::{-1..8},g_4_7 = 2,g_5_0::{-1..8},g_5_1::{-1..8},g_5_2 = 5,g_5_3::{-1..8},g_5_4::{-1..8},g_5_5 = 4,g_5_6::{-1..8},g_5_7::{-1..8},g_6_0 = 2,g_6_1::{-1..8},g_6_2::{-1..8},g_6_3::{-1..8},g_6_4 = 5,g_6_5::{-1..8},g_6_6 = 4,g_6_7::{-1..8},g_7_0::{-1..8},g_7_1 = 3,g_7_2::{-1..8},g_7_3 = 3,g_7_4::{-1..8},g_7_5::{-1..8},g_7_6::{-1..8},g_7_7 = 2]",
                            "[m_0_0=0,m_0_1=0,m_0_2=0,m_0_3=0,m_0_4=0,m_0_5=0,m_0_6=1,m_0_7=0,m_0_8=0,m_0_9=0,m_1_0=0,m_1_1=0,m_1_2=0,m_1_3=0,m_1_4=0,m_1_5=1,m_1_6=0,m_1_7=0,m_1_8=0,m_1_9=1,m_2_0=0,m_2_1=1,m_2_2=0,m_2_3=1,m_2_4=0,m_2_5=0,m_2_6=0,m_2_7=0,m_2_8=1,m_2_9=0,m_3_0=0,m_3_1=0,m_3_2=0,m_3_3=0,m_3_4=0,m_3_5=0,m_3_6=1,m_3_7=0,m_3_8=0,m_3_9=0,m_4_0=0,m_4_1=0,m_4_2=1,m_4_3=0,m_4_4=0,m_4_5=0,m_4_6=0,m_4_7=0,m_4_8=0,m_4_9=0,m_5_0=0,m_5_1=0,m_5_2=0,m_5_3=0,m_5_4=0,m_5_5=1,m_5_6=0,m_5_7=0,m_5_8=1,m_5_9=0,m_6_0=1,m_6_1=1,m_6_2=0,m_6_3=0,m_6_4=1,m_6_5=0,m_6_6=0,m_6_7=0,m_6_8=0,m_6_9=0,m_7_0=1,m_7_1=0,m_7_2=0,m_7_3=0,m_7_4=0,m_7_5=0,m_7_6=1,m_7_7=0,m_7_8=1,m_7_9=0,m_8_0=1,m_8_1=0,m_8_2=1,m_8_3=0,m_8_4=0,m_8_5=1,m_8_6=0,m_8_7=1,m_8_8=0,m_8_9=0,m_9_0=0,m_9_1=0,m_9_2=0,m_9_3=0,m_9_4=0,m_9_5=0,m_9_6=0,m_9_7=0,m_9_8=0,m_9_9=0,g_0_0 = 0,g_0_1::{-1..8},g_0_2 = 0,g_0_3::{-1..8},g_0_4 = 1,g_0_5::{-1..8},g_0_6::{-1..8},g_0_7 = 1,g_0_8 = 1,g_0_9::{-1..8},g_1_0 = 1,g_1_1::{-1..8},g_1_2 = 2,g_1_3::{-1..8},g_1_4 = 2,g_1_5::{-1..8},g_1_6 = 2,g_1_7 = 2,g_1_8::{-1..8},g_1_9::{-1..8},g_2_0::{-1..8},g_2_1::{-1..8},g_2_2::{-1..8},g_2_3::{-1..8},g_2_4::{-1..8},g_2_5::{-1..8},g_2_6 = 2,g_2_7::{-1..8},g_2_8::{-1..8},g_2_9 = 2,g_3_0::{-1..8},g_3_1 = 2,g_3_2 = 3,g_3_3::{-1..8},g_3_4 = 1,g_3_5 = 1,g_3_6::{-1..8},g_3_7::{-1..8},g_3_8::{-1..8},g_3_9::{-1..8},g_4_0 = 0,g_4_1::{-1..8},g_4_2::{-1..8},g_4_3::{-1..8},g_4_4::{-1..8},g_4_5::{-1..8},g_4_6::{-1..8},g_4_7 = 2,g_4_8::{-1..8},g_4_9 = 1,g_5_0::{-1..8},g_5_1::{-1..8},g_5_2::{-1..8},g_5_3 = 2,g_5_4 = 2,g_5_5::{-1..8},g_5_6 = 1,g_5_7::{-1..8},g_5_8::{-1..8},g_5_9::{-1..8},g_6_0::{-1..8},g_6_1::{-1..8},g_6_2::{-1..8},g_6_3::{-1..8},g_6_4::{-1..8},g_6_5 = 3,g_6_6::{-1..8},g_6_7 = 3,g_6_8 = 2,g_6_9::{-1..8},g_7_0::{-1..8},g_7_1 = 5,g_7_2::{-1..8},g_7_3 = 2,g_7_4::{-1..8},g_7_5::{-1..8},g_7_6::{-1..8},g_7_7 = 3,g_7_8::{-1..8},g_7_9 = 1,g_8_0::{-1..8},g_8_1 = 3,g_8_2::{-1..8},g_8_3 = 1,g_8_4::{-1..8},g_8_5::{-1..8},g_8_6 = 3,g_8_7::{-1..8},g_8_8::{-1..8},g_8_9::{-1..8},g_9_0::{-1..8},g_9_1 = 2,g_9_2::{-1..8},g_9_3::{-1..8},g_9_4::{-1..8},g_9_5 = 1,g_9_6 = 2,g_9_7::{-1..8},g_9_8::{-1..8},g_9_9 = 0]",
                            "[m_0_0=1,m_0_1=0,m_0_2=0,m_0_3=1,m_0_4=0,m_0_5=0,m_0_6=0,m_0_7=0,m_0_8=1,m_0_9=1,m_1_0=1,m_1_1=0,m_1_2=0,m_1_3=0,m_1_4=0,m_1_5=1,m_1_6=0,m_1_7=1,m_1_8=0,m_1_9=0,m_2_0=1,m_2_1=0,m_2_2=1,m_2_3=0,m_2_4=1,m_2_5=0,m_2_6=0,m_2_7=1,m_2_8=1,m_2_9=0,m_3_0=0,m_3_1=1,m_3_2=0,m_3_3=1,m_3_4=1,m_3_5=0,m_3_6=1,m_3_7=0,m_3_8=1,m_3_9=1,m_4_0=1,m_4_1=1,m_4_2=0,m_4_3=0,m_4_4=1,m_4_5=0,m_4_6=1,m_4_7=1,m_4_8=0,m_4_9=0,m_5_0=0,m_5_1=0,m_5_2=1,m_5_3=0,m_5_4=1,m_5_5=1,m_5_6=0,m_5_7=0,m_5_8=1,m_5_9=1,m_6_0=0,m_6_1=1,m_6_2=0,m_6_3=0,m_6_4=0,m_6_5=1,m_6_6=1,m_6_7=0,m_6_8=1,m_6_9=0,m_7_0=0,m_7_1=1,m_7_2=1,m_7_3=0,m_7_4=0,m_7_5=1,m_7_6=0,m_7_7=1,m_7_8=1,m_7_9=1,m_8_0=0,m_8_1=0,m_8_2=1,m_8_3=1,m_8_4=0,m_8_5=0,m_8_6=1,m_8_7=1,m_8_8=0,m_8_9=0,m_9_0=1,m_9_1=1,m_9_2=1,m_9_3=0,m_9_4=1,m_9_5=0,m_9_6=0,m_9_7=0,m_9_8=0,m_9_9=0,g_0_0::{-1..8},g_0_1 = 2,g_0_2 = 1,g_0_3::{-1..8},g_0_4 = 2,g_0_5::{-1..8},g_0_6 = 2,g_0_7::{-1..8},g_0_8::{-1..8},g_0_9::{-1..8},g_1_0::{-1..8},g_1_1 = 4,g_1_2::{-1..8},g_1_3::{-1..8},g_1_4 = 3,g_1_5::{-1..8},g_1_6::{-1..8},g_1_7::{-1..8},g_1_8 = 5,g_1_9 = 3,g_2_0::{-1..8},g_2_1::{-1..8},g_2_2::{-1..8},g_2_3 = 4,g_2_4::{-1..8},g_2_5 = 4,g_2_6 = 4,g_2_7::{-1..8},g_2_8::{-1..8},g_2_9 = 3,g_3_0 = 4,g_3_1::{-1..8},g_3_2 = 4,g_3_3::{-1..8},g_3_4::{-1..8},g_3_5 = 5,g_3_6::{-1..8},g_3_7 = 6,g_3_8::{-1..8},g_3_9::{-1..8},g_4_0::{-1..8},g_4_1::{-1..8},g_4_2 = 4,g_4_3 = 5,g_4_4::{-1..8},g_4_5::{-1..8},g_4_6::{-1..8},g_4_7::{-1..8},g_4_8 = 5,g_4_9 = 4,g_5_0 = 3,g_5_1 = 4,g_5_2::{-1..8},g_5_3::{-1..8},g_5_4::{-1..8},g_5_5::{-1..8},g_5_6 = 5,g_5_7 = 5,g_5_8::{-1..8},g_5_9::{-1..8},g_6_0::{-1..8},g_6_1::{-1..8},g_6_2 = 4,g_6_3::{-1..8},g_6_4 = 4,g_6_5::{-1..8},g_6_6::{-1..8},g_6_7 = 5,g_6_8::{-1..8},g_6_9 = 5,g_7_0 = 2,g_7_1::{-1..8},g_7_2::{-1..8},g_7_3 = 3,g_7_4 = 3,g_7_5::{-1..8},g_7_6 = 6,g_7_7::{-1..8},g_7_8::{-1..8},g_7_9::{-1..8},g_8_0 = 3,g_8_1 = 6,g_8_2::{-1..8},g_8_3::{-1..8},g_8_4::{-1..8},g_8_5 = 3,g_8_6::{-1..8},g_8_7::{-1..8},g_8_8 = 4,g_8_9::{-1..8},g_9_0::{-1..8},g_9_1::{-1..8},g_9_2::{-1..8},g_9_3 = 4,g_9_4::{-1..8},g_9_5 = 2,g_9_6::{-1..8},g_9_7 = 2,g_9_8 = 1,g_9_9::{-1..8}]",
                            "[m_0_0=1,m_0_1=0,m_0_2=0,m_0_3=0,m_0_4=0,m_0_5=0,m_0_6=0,m_0_7=1,m_1_0=0,m_1_1=1,m_1_2=1,m_1_3=0,m_1_4=0,m_1_5=0,m_1_6=1,m_1_7=0,m_2_0=0,m_2_1=1,m_2_2=0,m_2_3=0,m_2_4=0,m_2_5=1,m_2_6=1,m_2_7=0,m_3_0=1,m_3_1=0,m_3_2=1,m_3_3=0,m_3_4=0,m_3_5=0,m_3_6=1,m_3_7=1,m_4_0=1,m_4_1=1,m_4_2=0,m_4_3=1,m_4_4=1,m_4_5=1,m_4_6=0,m_4_7=1,m_5_0=0,m_5_1=1,m_5_2=1,m_5_3=1,m_5_4=0,m_5_5=0,m_5_6=1,m_5_7=0,m_6_0=0,m_6_1=0,m_6_2=1,m_6_3=0,m_6_4=0,m_6_5=1,m_6_6=1,m_6_7=1,m_7_0=1,m_7_1=0,m_7_2=0,m_7_3=1,m_7_4=1,m_7_5=0,m_7_6=0,m_7_7=1,g_0_0::{-1..8},g_0_1 = 3,g_0_2 = 2,g_0_3::{-1..8},g_0_4::{-1..8},g_0_5 = 1,g_0_6::{-1..8},g_0_7::{-1..8},g_1_0::{-1..8},g_1_1::{-1..8},g_1_2::{-1..8},g_1_3::{-1..8},g_1_4 = 1,g_1_5::{-1..8},g_1_6::{-1..8},g_1_7 = 3,g_2_0 = 3,g_2_1::{-1..8},g_2_2::{-1..8},g_2_3 = 2,g_2_4::{-1..8},g_2_5::{-1..8},g_2_6::{-1..8},g_2_7 = 4,g_3_0::{-1..8},g_3_1 = 5,g_3_2::{-1..8},g_3_3::{-1..8},g_3_4::{-1..8},g_3_5 = 5,g_3_6::{-1..8},g_3_7::{-1..8},g_4_0::{-1..8},g_4_1::{-1..8},g_4_2 = 6,g_4_3::{-1..8},g_4_4::{-1..8},g_4_5::{-1..8},g_4_6 = 5,g_4_7::{-1..8},g_5_0 = 3,g_5_1::{-1..8},g_5_2::{-1..8},g_5_3::{-1..8},g_5_4 = 5,g_5_5::{-1..8},g_5_6::{-1..8},g_5_7 = 4,g_6_0 = 2,g_6_1::{-1..8},g_6_2::{-1..8},g_6_3 = 5,g_6_4::{-1..8},g_6_5::{-1..8},g_6_6::{-1..8},g_6_7::{-1..8},g_7_0::{-1..8},g_7_1::{-1..8},g_7_2 = 2,g_7_3::{-1..8},g_7_4::{-1..8},g_7_5 = 3,g_7_6 = 4,g_7_7::{-1..8}]",
                            "[m_0_0=0,m_0_1=0,m_0_2=0,m_0_3=1,m_0_4=0,m_0_5=1,m_0_6=0,m_0_7=0,m_0_8=1,m_1_0=0,m_1_1=0,m_1_2=1,m_1_3=0,m_1_4=0,m_1_5=0,m_1_6=1,m_1_7=1,m_1_8=0,m_2_0=0,m_2_1=0,m_2_2=0,m_2_3=1,m_2_4=0,m_2_5=1,m_2_6=0,m_2_7=0,m_2_8=0,m_3_0=1,m_3_1=1,m_3_2=1,m_3_3=0,m_3_4=1,m_3_5=0,m_3_6=0,m_3_7=1,m_3_8=1,m_4_0=0,m_4_1=0,m_4_2=0,m_4_3=0,m_4_4=1,m_4_5=0,m_4_6=1,m_4_7=0,m_4_8=1,m_5_0=0,m_5_1=0,m_5_2=1,m_5_3=0,m_5_4=0,m_5_5=0,m_5_6=0,m_5_7=1,m_5_8=1,m_6_0=0,m_6_1=0,m_6_2=0,m_6_3=1,m_6_4=1,m_6_5=0,m_6_6=0,m_6_7=0,m_6_8=0,m_7_0=0,m_7_1=1,m_7_2=0,m_7_3=0,m_7_4=0,m_7_5=0,m_7_6=0,m_7_7=0,m_7_8=1,m_8_0=0,m_8_1=0,m_8_2=1,m_8_3=0,m_8_4=0,m_8_5=0,m_8_6=1,m_8_7=0,m_8_8=1,g_0_0::{-1..8},g_0_1 = 1,g_0_2::{-1..8},g_0_3::{-1..8},g_0_4::{-1..8},g_0_5::{-1..8},g_0_6::{-1..8},g_0_7 = 3,g_0_8::{-1..8},g_1_0::{-1..8},g_1_1::{-1..8},g_1_2::{-1..8},g_1_3 = 3,g_1_4 = 4,g_1_5 = 3,g_1_6::{-1..8},g_1_7::{-1..8},g_1_8::{-1..8},g_2_0 = 2,g_2_1 = 4,g_2_2 = 4,g_2_3::{-1..8},g_2_4::{-1..8},g_2_5::{-1..8},g_2_6 = 4,g_2_7 = 4,g_2_8 = 3,g_3_0::{-1..8},g_3_1::{-1..8},g_3_2::{-1..8},g_3_3 = 4,g_3_4::{-1..8},g_3_5 = 4,g_3_6::{-1..8},g_3_7::{-1..8},g_3_8::{-1..8},g_4_0::{-1..8},g_4_1 = 4,g_4_2::{-1..8},g_4_3 = 4,g_4_4::{-1..8},g_4_5 = 3,g_4_6::{-1..8},g_4_7 = 6,g_4_8::{-1..8},g_5_0::{-1..8},g_5_1::{-1..8},g_5_2::{-1..8},g_5_3 = 4,g_5_4::{-1..8},g_5_5 = 3,g_5_6::{-1..8},g_5_7::{-1..8},g_5_8::{-1..8},g_6_0 = 1,g_6_1 = 2,g_6_2 = 3,g_6_3::{-1..8},g_6_4::{-1..8},g_6_5::{-1..8},g_6_6 = 1,g_6_7 = 3,g_6_8 = 3,g_7_0::{-1..8},g_7_1::{-1..8},g_7_2::{-1..8},g_7_3 = 3,g_7_4 = 2,g_7_5 = 2,g_7_6::{-1..8},g_7_7::{-1..8},g_7_8::{-1..8},g_8_0::{-1..8},g_8_1 = 2,g_8_2::{-1..8},g_8_3::{-1..8},g_8_4::{-1..8},g_8_5::{-1..8},g_8_6::{-1..8},g_8_7 = 3,g_8_8::{-1..8}]",
                            "[m_0_0=0,m_0_1=1,m_0_2=1,m_0_3=0,m_0_4=1,m_0_5=0,m_0_6=1,m_1_0=0,m_1_1=0,m_1_2=0,m_1_3=0,m_1_4=0,m_1_5=0,m_1_6=1,m_2_0=0,m_2_1=0,m_2_2=0,m_2_3=1,m_2_4=1,m_2_5=0,m_2_6=1,m_3_0=0,m_3_1=0,m_3_2=1,m_3_3=0,m_3_4=0,m_3_5=0,m_3_6=0,m_4_0=0,m_4_1=0,m_4_2=0,m_4_3=1,m_4_4=1,m_4_5=0,m_4_6=1,m_5_0=0,m_5_1=0,m_5_2=0,m_5_3=0,m_5_4=0,m_5_5=0,m_5_6=1,m_6_0=0,m_6_1=1,m_6_2=0,m_6_3=0,m_6_4=0,m_6_5=1,m_6_6=0,g_0_0::{-1..8},g_0_1::{-1..8},g_0_2::{-1..8},g_0_3::{-1..8},g_0_4::{-1..8},g_0_5::{-1..8},g_0_6::{-1..8},g_1_0::{-1..8},g_1_1 = 2,g_1_2 = 3,g_1_3 = 4,g_1_4 = 3,g_1_5 = 5,g_1_6::{-1..8},g_2_0::{-1..8},g_2_1 = 1,g_2_2::{-1..8},g_2_3::{-1..8},g_2_4::{-1..8},g_2_5 = 3,g_2_6::{-1..8},g_3_0::{-1..8},g_3_1::{-1..8},g_3_2::{-1..8},g_3_3 = 5,g_3_4::{-1..8},g_3_5::{-1..8},g_3_6::{-1..8},g_4_0::{-1..8},g_4_1 = 1,g_4_2::{-1..8},g_4_3::{-1..8},g_4_4::{-1..8},g_4_5 = 3,g_4_6::{-1..8},g_5_0::{-1..8},g_5_1 = 1,g_5_2 = 2,g_5_3 = 2,g_5_4 = 3,g_5_5 = 4,g_5_6::{-1..8},g_6_0::{-1..8},g_6_1::{-1..8},g_6_2::{-1..8},g_6_3::{-1..8},g_6_4::{-1..8},g_6_5::{-1..8},g_6_6::{-1..8}]",
                            "[m_0_0=0,m_0_1=1,m_0_2=0,m_0_3=1,m_0_4=0,m_0_5=0,m_0_6=1,m_0_7=1,m_0_8=0,m_1_0=1,m_1_1=0,m_1_2=1,m_1_3=0,m_1_4=1,m_1_5=0,m_1_6=0,m_1_7=0,m_1_8=1,m_2_0=0,m_2_1=1,m_2_2=0,m_2_3=1,m_2_4=0,m_2_5=1,m_2_6=0,m_2_7=0,m_2_8=1,m_3_0=0,m_3_1=0,m_3_2=1,m_3_3=0,m_3_4=0,m_3_5=0,m_3_6=0,m_3_7=0,m_3_8=1,m_4_0=0,m_4_1=1,m_4_2=1,m_4_3=0,m_4_4=0,m_4_5=1,m_4_6=1,m_4_7=1,m_4_8=0,m_5_0=1,m_5_1=0,m_5_2=1,m_5_3=0,m_5_4=1,m_5_5=0,m_5_6=0,m_5_7=0,m_5_8=0,m_6_0=0,m_6_1=1,m_6_2=0,m_6_3=0,m_6_4=1,m_6_5=1,m_6_6=0,m_6_7=1,m_6_8=1,m_7_0=1,m_7_1=0,m_7_2=1,m_7_3=0,m_7_4=1,m_7_5=0,m_7_6=1,m_7_7=0,m_7_8=1,m_8_0=0,m_8_1=1,m_8_2=0,m_8_3=0,m_8_4=0,m_8_5=0,m_8_6=1,m_8_7=1,m_8_8=0,g_0_0 = 2,g_0_1::{-1..8},g_0_2::{-1..8},g_0_3::{-1..8},g_0_4 = 2,g_0_5::{-1..8},g_0_6::{-1..8},g_0_7::{-1..8},g_0_8 = 2,g_1_0::{-1..8},g_1_1 = 4,g_1_2::{-1..8},g_1_3 = 4,g_1_4::{-1..8},g_1_5 = 3,g_1_6::{-1..8},g_1_7 = 4,g_1_8::{-1..8},g_2_0::{-1..8},g_2_1::{-1..8},g_2_2 = 4,g_2_3::{-1..8},g_2_4::{-1..8},g_2_5::{-1..8},g_2_6 = 1,g_2_7::{-1..8},g_2_8::{-1..8},g_3_0::{-1..8},g_3_1 = 4,g_3_2::{-1..8},g_3_3 = 3,g_3_4::{-1..8},g_3_5 = 3,g_3_6::{-1..8},g_3_7 = 4,g_3_8::{-1..8},g_4_0 = 2,g_4_1::{-1..8},g_4_2::{-1..8},g_4_3::{-1..8},g_4_4::{-1..8},g_4_5::{-1..8},g_4_6::{-1..8},g_4_7::{-1..8},g_4_8 = 2,g_5_0::{-1..8},g_5_1 = 5,g_5_2::{-1..8},g_5_3 = 4,g_5_4::{-1..8},g_5_5 = 5,g_5_6::{-1..8},g_5_7 = 4,g_5_8::{-1..8},g_6_0::{-1..8},g_6_1::{-1..8},g_6_2 = 3,g_6_3::{-1..8},g_6_4::{-1..8},g_6_5::{-1..8},g_6_6 = 3,g_6_7::{-1..8},g_6_8::{-1..8},g_7_0::{-1..8},g_7_1 = 4,g_7_2::{-1..8},g_7_3 = 3,g_7_4::{-1..8},g_7_5 = 5,g_7_6::{-1..8},g_7_7 = 6,g_7_8::{-1..8},g_8_0 = 2,g_8_1::{-1..8},g_8_2::{-1..8},g_8_3::{-1..8},g_8_4 = 1,g_8_5::{-1..8},g_8_6::{-1..8},g_8_7::{-1..8},g_8_8 = 2]"
                            };
        
        for (int i = 0; i < minesweeper.problems.length; i++) {

            minesweeper.problem = MineSweeper.readFromArray(minesweeper.problems[i]);

            minesweeper.model();

            minesweeper.searchSpecific(true);

            minesweeper.getSearch().assignSolution();

            assertEquals("Sol " + i, results[i], minesweeper.store.toStringOrderedVars() );
        }

    }

    @Test public void testNewspaper() {

        Newspaper example = new Newspaper();

        example.model();

        example.searchSmallestMin();

        example.getSearch().assignSolution();

        assertEquals("[algy[0] = 110,algy[1] = 45,algy[2] = 140,algy[3] = 165,bertie[0] = 35,bertie[1] = 113,bertie[2] = 110,bertie[3] = 170,charlie[0] = 20,charlie[1] = 35,charlie[2] = 15,charlie[3] = 45,digby[0] = 166,digby[1] = 165,digby[2] = 167,digby[3] = 75,durationAlgyExpress = 2,durationAlgyFT = 60,durationAlgyGuardian = 30,durationAlgySun = 5,durationBertieExpress = 3,durationBertieFT = 25,durationBertieGuardian = 75,durationBertieSun = 10,durationCharlieExpress = 5,durationCharlieFT = 10,durationCharlieGuardian = 15,durationCharlieSun = 30,durationDigbyExpress = 1,durationDigbyFT = 1,durationDigbyGuardian = 1,durationDigbySun = 90,makespan = 180,one = 1]",
                     example.store.toStringOrderedVars());
    }

    @Test public void testNonTransitiveDice() {

        boolean firstSolutionFound = false;

        int noDices = 4;
        int noSides = 7;
        int currentBest;

        if (noSides * noSides % 2 == 0)
            currentBest = noSides * noSides / 2 - 1;
        else
            currentBest = noSides * noSides / 2;

        String solution = "";

        while (true) {

            NonTransitiveDice example = new NonTransitiveDice();

            example.noDices = noDices;
            example.noSides = noSides;
            example.currentBest = currentBest;

            example.model();

            boolean result = example.shavingSearch(example.shavingConstraints, false);

            System.out.print(noDices + "\t");
            System.out.print(noSides + "\t");
            System.out.print(currentBest + "\t");
            System.out.print(result + "\t");
            System.out.print(example.search.getNodes() + "\t");
            System.out.print(example.search.getDecisions() + "\t");
            System.out.print(example.search.getWrongDecisions() + "\t");
            System.out.print(example.search.getBacktracks() + "\t");
            System.out.println(example.search.getMaximumDepth() + "\t");

            currentBest--;

            if (result) {
                firstSolutionFound = true;
            }

            if (!result && firstSolutionFound)
                break;
            
            // Store previous solution and not a proof of optimality ( no solution ).
            example.getSearch().assignSolution();
            solution = example.store.toStringOrderedVars();
        }

        assertEquals("[win_D1->2F00=0,win_D1->2F01=0,win_D1->2F02=0,win_D1->2F03=0,win_D1->2F04=0,win_D1->2F05=0,win_D1->2F06=0,win_D1->2F10=1,win_D1->2F11=1,win_D1->2F12=1,win_D1->2F13=1,win_D1->2F14=0,win_D1->2F15=0,win_D1->2F16=0,win_D1->2F20=1,win_D1->2F21=1,win_D1->2F22=1,win_D1->2F23=1,win_D1->2F24=0,win_D1->2F25=0,win_D1->2F26=0,win_D1->2F30=1,win_D1->2F31=1,win_D1->2F32=1,win_D1->2F33=1,win_D1->2F34=0,win_D1->2F35=0,win_D1->2F36=0,win_D1->2F40=1,win_D1->2F41=1,win_D1->2F42=1,win_D1->2F43=1,win_D1->2F44=1,win_D1->2F45=1,win_D1->2F46=0,win_D1->2F50=1,win_D1->2F51=1,win_D1->2F52=1,win_D1->2F53=1,win_D1->2F54=1,win_D1->2F55=1,win_D1->2F56=0,win_D1->2F60=1,win_D1->2F61=1,win_D1->2F62=1,win_D1->2F63=1,win_D1->2F64=1,win_D1->2F65=1,win_D1->2F66=0,win_D2->3F00=1,win_D2->3F01=1,win_D2->3F02=1,win_D2->3F03=0,win_D2->3F04=0,win_D2->3F05=0,win_D2->3F06=0,win_D2->3F10=1,win_D2->3F11=1,win_D2->3F12=1,win_D2->3F13=1,win_D2->3F14=0,win_D2->3F15=0,win_D2->3F16=0,win_D2->3F20=1,win_D2->3F21=1,win_D2->3F22=1,win_D2->3F23=1,win_D2->3F24=0,win_D2->3F25=0,win_D2->3F26=0,win_D2->3F30=1,win_D2->3F31=1,win_D2->3F32=1,win_D2->3F33=1,win_D2->3F34=0,win_D2->3F35=0,win_D2->3F36=0,win_D2->3F40=1,win_D2->3F41=1,win_D2->3F42=1,win_D2->3F43=1,win_D2->3F44=0,win_D2->3F45=0,win_D2->3F46=0,win_D2->3F50=1,win_D2->3F51=1,win_D2->3F52=1,win_D2->3F53=1,win_D2->3F54=0,win_D2->3F55=0,win_D2->3F56=0,win_D2->3F60=1,win_D2->3F61=1,win_D2->3F62=1,win_D2->3F63=1,win_D2->3F64=1,win_D2->3F65=1,win_D2->3F66=1,win_D3->0F00=1,win_D3->0F01=1,win_D3->0F02=0,win_D3->0F03=0,win_D3->0F04=0,win_D3->0F05=0,win_D3->0F06=0,win_D3->0F10=1,win_D3->0F11=1,win_D3->0F12=1,win_D3->0F13=0,win_D3->0F14=0,win_D3->0F15=0,win_D3->0F16=0,win_D3->0F20=1,win_D3->0F21=1,win_D3->0F22=1,win_D3->0F23=0,win_D3->0F24=0,win_D3->0F25=0,win_D3->0F26=0,win_D3->0F30=1,win_D3->0F31=1,win_D3->0F32=1,win_D3->0F33=0,win_D3->0F34=0,win_D3->0F35=0,win_D3->0F36=0,win_D3->0F40=1,win_D3->0F41=1,win_D3->0F42=1,win_D3->0F43=1,win_D3->0F44=1,win_D3->0F45=0,win_D3->0F46=0,win_D3->0F50=1,win_D3->0F51=1,win_D3->0F52=1,win_D3->0F53=1,win_D3->0F54=1,win_D3->0F55=1,win_D3->0F56=1,win_D3->0F60=1,win_D3->0F61=1,win_D3->0F62=1,win_D3->0F63=1,win_D3->0F64=1,win_D3->0F65=1,win_D3->0F66=1,win_D4->1F00=1,win_D4->1F01=0,win_D4->1F02=0,win_D4->1F03=0,win_D4->1F04=0,win_D4->1F05=0,win_D4->1F06=0,win_D4->1F10=1,win_D4->1F11=0,win_D4->1F12=0,win_D4->1F13=0,win_D4->1F14=0,win_D4->1F15=0,win_D4->1F16=0,win_D4->1F20=1,win_D4->1F21=0,win_D4->1F22=0,win_D4->1F23=0,win_D4->1F24=0,win_D4->1F25=0,win_D4->1F26=0,win_D4->1F30=1,win_D4->1F31=1,win_D4->1F32=1,win_D4->1F33=1,win_D4->1F34=1,win_D4->1F35=1,win_D4->1F36=0,win_D4->1F40=1,win_D4->1F41=1,win_D4->1F42=1,win_D4->1F43=1,win_D4->1F44=1,win_D4->1F45=1,win_D4->1F46=1,win_D4->1F50=1,win_D4->1F51=1,win_D4->1F52=1,win_D4->1F53=1,win_D4->1F54=1,win_D4->1F55=1,win_D4->1F56=1,win_D4->1F60=1,win_D4->1F61=1,win_D4->1F62=1,win_D4->1F63=1,win_D4->1F64=1,win_D4->1F65=1,win_D4->1F66=1,MinDominance = 30,d1f1 = 1,d1f2 = 13,d1f3 = 14,d1f4 = 15,d1f5 = 18,d1f6 = 19,d1f7 = 21,d2f1 = 8,d2f2 = 10,d2f3 = 11,d2f4 = 12,d2f5 = 16,d2f6 = 17,d2f7 = 28,d3f1 = 4,d3f2 = 6,d3f3 = 7,d3f4 = 9,d3f5 = 23,d3f6 = 26,d3f7 = 27,d4f1 = 2,d4f2 = 3,d4f3 = 5,d4f4 = 20,d4f5 = 22,d4f6 = 24,d4f7 = 25,diff = 19,maxNo = 28,noWins-d1->d2 = 30,noWins-d2->d3 = 30,noWins-d3->d0 = 30,noWins-d4->d1 = 30]",
                     solution);

    }


    @Test public void testParcel() {

        Parcel example = new Parcel();

        example.model();

        if (example.searchMaxRegretOptimal())
            System.out.println("Solution(s) found");

        example.getSearch().assignSolution();

        assertEquals("[Cost = 355,cities[0] = 8,cities[1] = 3,cities[2] = 4,cities[3] = 6,cities[4] = 10,cities[5] = 7,cities[6] = 1,cities[7] = 9,cities[8] = 5,cities[9] = 2,costs[0] = 56,costs[1] = 26,costs[2] = 71,costs[3] = 19,costs[4] = 13,costs[5] = 65,costs[6] = 25,costs[7] = 23,costs[8] = 8,costs[9] = 49,nextLoad[0] = 2,nextLoad[1] = 1,nextLoad[2] = 4,nextLoad[3] = -3,nextLoad[4] = 1,nextLoad[5] = 5,nextLoad[6] = -6,nextLoad[7] = 3,nextLoad[8] = -5,nextLoad[9] = 0,nextTown[0] = 9,nextTown[1] = 5,nextTown[2] = 10,nextTown[3] = 2,nextTown[4] = 3,nextTown[5] = 4,nextTown[6] = 6,nextTown[7] = 7,nextTown[8] = 1,nextTown[9] = 8,partialLoad[0-0] = 2,partialLoad[0-1] = 3,partialLoad[0-2] = 7,partialLoad[0-3] = 4,partialLoad[0-4] = 5,partialLoad[0-5] = 10,partialLoad[0-6] = 4,partialLoad[0-7] = 7,partialLoad[0-8] = 2,partialLoad[0-9] = 2,MutableVar[0] (0)[8, 7],MutableVar[1] (0)[3, 10],MutableVar[2] (0)[4, 2],MutableVar[3] (0)[6, 3],MutableVar[4] (0)[10, 9],MutableVar[5] (0)[7, 4],MutableVar[6] (0)[1, 6],MutableVar[7] (0)[9, 1],MutableVar[8] (0)[5, 8],MutableVar[9] (0)[2, 5]]",
                     example.store.toStringOrderedVars());
    }

}
