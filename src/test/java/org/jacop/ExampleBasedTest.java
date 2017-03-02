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

import org.jacop.examples.fd.ArchFriends;
import org.jacop.examples.fd.BIBD;
import org.jacop.examples.fd.BabySitting;
import org.jacop.examples.fd.BasicLogicPascal;
import org.jacop.examples.fd.BlueberryMuffins;
import org.jacop.examples.fd.BreakingNews;
import org.jacop.examples.fd.BuildingBlocks;
import org.jacop.examples.fd.CalendarMen;
import org.jacop.examples.fd.Conference;
import org.jacop.examples.fd.Cryptogram;
import org.jacop.examples.fd.DeBruijn;
import org.jacop.examples.fd.Diet;
import org.jacop.examples.fd.DollarAndTicket;
import org.jacop.examples.fd.DonaldGeraldRobert;
import org.jacop.examples.fd.Exodus;
import org.jacop.examples.fd.FittingNumbers;
import org.jacop.examples.fd.Flowers;
import org.jacop.examples.fd.FourIslands;
import org.jacop.examples.fd.FurnitureMoving;
import org.jacop.examples.fd.Gates;
import org.jacop.examples.fd.Golf;
import org.jacop.examples.fd.Golomb;
import org.jacop.examples.fd.HistoricHomes;
import org.jacop.examples.fd.Kakro;
import org.jacop.examples.fd.KnapsackExample;
import org.jacop.examples.fd.Langford;
import org.jacop.examples.fd.LectureSeries;
import org.jacop.examples.fd.MagicSquares;
import org.jacop.examples.fd.MasterClass;
import org.jacop.examples.fd.carsequencing.CarSequencing;
import org.junit.Test;


/**
 *
 * It is performing testing based on the examples present in the library.
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.4
 */
public class ExampleBasedTest {


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

    }

    @Test public void testCalendarMen() {

        CalendarMen example = new CalendarMen();

        example.model();

        assertEquals(true, example.searchAllAtOnce());

        assertEquals(1, example.search.getSolutionListener().solutionsNo());

    }



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



    @Test public void test() {

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

}
