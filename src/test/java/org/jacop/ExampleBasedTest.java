package org.jacop;

import static org.junit.Assert.*;
import junit.framework.Assert;

import org.jacop.constraints.XeqC;
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
import org.jacop.examples.fd.ExampleFD;
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
import org.jacop.examples.fd.LeastDiff;
import org.jacop.examples.fd.LectureSeries;
import org.jacop.examples.fd.MagicSquares;
import org.jacop.examples.fd.MasterClass;
import org.jacop.examples.fd.carsequencing.CarSequencing;
import org.junit.Test;

public class ExampleBasedTest {


	@Test
	public void testArchFriends() {

		ArchFriends example = new ArchFriends();
		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 1);

	}

	@Test
	public void testBabySitting() {

		BabySitting example = new BabySitting();

		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 1);		

	}

	@Test
	public void testBasicLogicPascal() {

		BasicLogicPascal example = new BasicLogicPascal();

		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 1);		

	}

	@Test
	public void testBIBD() {

		BIBD example = new BIBD();

		example.v = 7;
		example.b = 7;
		example.r = 3;
		example.k = 3;
		example.lambda = 1;

		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 151200);		

	}


	@Test
	public void testBlueberryMuffins() {

		BlueberryMuffins example = new BlueberryMuffins();

		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 24);	

	}


	@Test
	public void testBreakingNews() {

		BreakingNews example = new BreakingNews();

		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 480);	
	}

	@Test
	public void testBuildingBlocks() {

		BuildingBlocks example = new BuildingBlocks();

		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 24);	
	}


	@Test
	public void testCalendarMen() {

		CalendarMen example = new CalendarMen();

		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);

		CalendarMen exampleBasic = new CalendarMen();

		exampleBasic.modelBasic();

		Assert.assertEquals(exampleBasic.searchAllAtOnce(), true);

		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 
							exampleBasic.search.getSolutionListener().solutionsNo() );

	}


	@Test
	public void testCarSequencing() {

		CarSequencing example = new CarSequencing();

		CarSequencing.readFromArray(CarSequencing.problem, example);

		example.model();

		String[] description = CarSequencing.toStringArray(example);

		for (String line : description)
			System.out.println(line);

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 6);	
	}

	@Test
	public void testConference() {

		Conference example = new Conference();

		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 2);	

	}

	@Test
	public void testCryptogram() {

		String lines[][] = { {"CRACK", "HACK", "ERROR"}, {"PEAR", "APPLE", "GRAPE"}, {"CRACKS", "TRACKS", "RACKET"}, 
				{"TRIED", "RIDE", "STEER"}, {"DEEMED", "SENSE", "SYSTEM"}, {"DOWN", "WWW", "ERROR"}, 
				{"BARREL", "BROOMS", "SHOVELS"}, {"LYNNE", "LOOKS", "SLEEPY"}, {"STARS", "RATE", "TREAT"}, 
				{"DAYS", "TOO", "SHORT"}, {"BASE", "BALL", "GAMES"}, {"MEMO", "FROM", "HOMER"}, {"IS", "THIS", "HERE"}};

		int noSol[] = {1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1};

		for (int i = 0; i < lines.length; i++) {

			Cryptogram exampleLeft = new Cryptogram();
			exampleLeft.lines[0] = lines[i][0] + "+" + lines[i][1] + "=" + lines[i][2];
			exampleLeft.noLines = 1;

			exampleLeft.model();

			Assert.assertEquals(exampleLeft.searchAllAtOnce(), true);

			Assert.assertEquals(exampleLeft.search.getSolutionListener().solutionsNo(), noSol[i]);	

		}

	}


	@Test
	public void testDebruijnSequence() {

		DeBruijn example = new DeBruijn();
		example.base = 2;
		example.n = 4;
		example.m = 9;

		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);

		// prints then de Bruijn sequences
		System.out.print("de Bruijn sequence:");            

		System.out.print("decimal values: ");
		for(int i = 0; i < example.m; i++) {
			System.out.print(example.x[i].value() + " ");
		}
		System.out.println();

		System.out.println("\nbinary:");

		for(int i = 0; i < example.m; i++) {
			for(int j = 0; j < example.n; j++) {
				System.out.print(example.binary[i][j].value() + " ");
			}
			System.out.println(" : " + example.x[i].value());
		}

		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 14);	

	}


	@Test
	public void testDiet() {

		  Diet exampleSumWeight = new Diet();
	      exampleSumWeight.model();
		  System.out.println("Searching for all solutions using sum weight constraints");
		  Assert.assertEquals(exampleSumWeight.searchAllAtOnce(), true);
	      Diet.printLastSolution(exampleSumWeight);

	      Diet exampleKnapsack = new Diet();
	      exampleKnapsack.modelKnapsack();
		  System.out.println("Searching for all solutions using knapsack constraints");
		  Assert.assertEquals(exampleKnapsack.searchAllAtOnce(), true);
		  Diet.printLastSolution(exampleKnapsack);

		  Assert.assertEquals(exampleSumWeight.search.getSolutionListener().solutionsNo(), 
				  			  exampleKnapsack.search.getSolutionListener().solutionsNo() );	
	}


	@Test
	public void testDolarAndTicket() {

		DollarAndTicket example = new DollarAndTicket();

		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 36);	
	}


	@Test
	public void testDonaldGeraldRobert() {

		DonaldGeraldRobert example = new DonaldGeraldRobert();

		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 1);	

	}

	@Test
	public void testExodus() {

		Exodus example = new Exodus();

		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 6);	
	}

	@Test
	public void testFittingNumbers() {

		FittingNumbers example = new FittingNumbers();

		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 6967);	
	}



	@Test
	public void testFlowers() {

		Flowers example = new Flowers();
		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 1);	
	}

	@Test
	public void testFourIslands() {

		FourIslands example = new FourIslands();
		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 1);	
	}

	@Test
	public void testFurnitureMoving() {

		FurnitureMoving example = new FurnitureMoving();
		example.model();

		Assert.assertEquals(example.searchSpecific(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 36);	

	}


	@Test
	public void testGates() {

		Gates example = new Gates();
		example.model();

		Assert.assertEquals(example.searchSpecific(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 8);	

	}

	@Test
	public void testGolf() {

		Golf example = new Golf();
		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 1);	
	}

	@Test
	public void testGolomb() {

		Golomb example = new Golomb();
		example.model();

		Assert.assertEquals(example.searchOptimalInfo(), true);

		int optimalCost = example.cost.value();

		example = new Golomb();
		example.bound = optimalCost;
		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 1);	

	}

	@Test
	public void testHistoricHomes() {

		HistoricHomes example = new HistoricHomes();
		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 1);	
	}



	@Test
	public void test() {

		Kakro example = new Kakro();

		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 1);	

	}
	

	@Test
	public void testKnapsack() {

		KnapsackExample example = new KnapsackExample();

		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 18);	
	}

	@Test
	public void testLangford() {

		Langford example = new Langford();
		example.n = 3;
		example.m = 10;
		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 10);	
	}

	
	@Test
	public void testLectureSeries() {

		LectureSeries example = new LectureSeries();
		
		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 120);	
	}
	
	@Test
	public void testMagicSquares() {

		MagicSquares example = new MagicSquares();
		
		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 1760);	
	}

	@Test
	public void testMasterClass() {
		
		MasterClass example = new MasterClass();
		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 12);	
	}

	
	/*



	@Test
	public void test() {

		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 151200);	
	}

	@Test
	public void test() {

		example.model();

		Assert.assertEquals(example.searchAllAtOnce(), true);
		Assert.assertEquals(example.search.getSolutionListener().solutionsNo(), 151200);	
	}
	 */
}