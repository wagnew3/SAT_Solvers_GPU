package MLSAT;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.Arrays;
import java.util.List;

import nDimensionalMatrices.GPUMemoryManager;
import SATProblem.SAT;
import SATProblem.Variable;
import SATProblemGeneration.RandomArgumentation;
import SATProblemGeneration.RandomPseudoIndustrialSAT;
import SATProblemGeneration.RandomRandomPI;
import SATProblemGeneration.RandomSATGenerator;
import SATProblemGeneration.SATProblemGenerator;
import SATSolver.DPLL;
import SATSolver.SATSolver;
import SATSolver.SATSolverSAT4J;

public class TestMLSATSAT4J 
{
	
	public static String dataDir="/home/willie/workspace/SAT_Solvers_GPU/data/";
	
	public static String testName="PIndusFixConfClausesInformed60c30v8";
	
	public static void main(String[] args) throws IOException
	{
		//testDPLLMLSAT();
		//testArgumentationMLSAT();
		testPIndustiralMLSAT();
		//testRandomPIndustiralMLSAT();
		//solvePIndus();
	}
	
	private static void testDPLLMLSAT()
	{
		//RandomSATGenerator threeSAT=new RandomSATGenerator(1500, 3, 500);
		SATProblemGenerator threeSAT=new RandomSATGenerator(105, 3, 30);
		MLSATSAT4J mlSATS4J=new MLSATSAT4J(false, threeSAT, 8);
		
		testName="Random"+threeSAT.getNumberClauses()+"c"+threeSAT.getNumberVariables()+"v"+mlSATS4J.alg+"a";
		
		SAT sat=threeSAT.generateSAT();
		/*
		boolean[] result=mlSATS4J.solve(sat.toCNF());
		System.out.println(sat);
	    System.out.println("MLSAT result: "+(result!=null));
	    System.out.println(Arrays.toString(result));
	    */
		
	    SATSolverSAT4J vanillaSolver=new SATSolverSAT4J();
	    boolean[] result=vanillaSolver.solve(sat.toCNF());
	    System.out.println("vanillaSolver result: "+(result!=null));
	    System.out.println(Arrays.toString(result));
	    
		/*
		SAT sat=SATGen.generateSAT();
		String cnf=sat.toCNF();
	    MLSAT mlSAT=new MLSAT(SATGen);
		mlSAT.trainNetwork(10000, false, true);
		//testAgainstVanillaOrig(mlSAT, SATGen);
		
		
		mlSAT.solve(sat);
		*/
	    
		mlSATS4J.trainNetwork(60000, false, true);
		//mlSATS4J.solve(cnf);
		testAgainstVanilla(mlSATS4J, threeSAT);
	}
	
	private static void testArgumentationMLSAT()
	{
		RandomArgumentation SATGen=new RandomArgumentation(500, 50);
		
		MLSATSAT4J mlSATS4J=new MLSATSAT4J(false, SATGen, 8);
		
		testName="RandomArgumentation"+500+"_"+50;
		
		if(true)
		{
			int numberCreated=0;
			while(numberCreated<1000)
			{
				SAT satProb=SATGen.generateSAT();
				int[] used=new int[SATGen.getNumberVariables()];
				for(int varInd=0; varInd<used.length; varInd++)
				{
					for(int clauseInd=0; clauseInd<satProb.clauses.size(); clauseInd++)
					{
						for(int clauseVarInd=0; clauseVarInd<satProb.clauses.get(clauseInd).variables.size(); clauseVarInd++)
						{
							used[satProb.variables.indexOf(satProb.clauses.get(clauseInd).variables.get(clauseVarInd))]=1;
						}
					}
				}

				if(used[0]==1 && used[used.length-1]==1)
				{
					SATGen.generateSAT().toCNF(new File("/home/willie/Software_Verification/cbmc-cbmc-5.4/minisat-2.2.1/"+testName+""+numberCreated+".cnf"));
					numberCreated++;
					System.out.println(numberCreated);
				}
			}
		}
		
		SAT sat=SATGen.generateSAT();
		/*
		boolean[] result=mlSATS4J.solve(sat.toCNF());
		System.out.println(sat);
	    System.out.println("MLSAT result: "+(result!=null));
	    System.out.println(Arrays.toString(result));
	    */
		
	    SATSolverSAT4J vanillaSolver=new SATSolverSAT4J();
	    boolean[] result=vanillaSolver.solve(sat.toCNF());
	    System.out.println("vanillaSolver result: "+(result!=null));
	    System.out.println(Arrays.toString(result));
	    
		/*
		SAT sat=SATGen.generateSAT();
		String cnf=sat.toCNF();
	    MLSAT mlSAT=new MLSAT(SATGen);
		mlSAT.trainNetwork(10000, false, true);
		//testAgainstVanillaOrig(mlSAT, SATGen);
		
		
		mlSAT.solve(sat);
		*/
	    
		//mlSATS4J.trainNetwork(60000, false, false);
		//mlSATS4J.solve(cnf);
		//testAgainstVanilla(mlSATS4J, argueSAT);
	}
	
	static boolean generate=true;
	
	/**
	 * @throws IOException 
	 * 
	 */
	private static void testPIndustiralMLSAT() throws IOException
	{
		//RandomPseudoIndustrialSAT SATGen=new RandomPseudoIndustrialSAT(1032, 250, 3, 40, 0.8);
		//SATProblemGenerator SATGen=new RandomPseudoIndustrialSAT(124, 30, 3, 10, 0.8);
		//SATProblemGenerator SATGen=new RandomPseudoIndustrialSAT(248, 60, 3, 10, 0.8);
		//SATProblemGenerator SATGen=new RandomPseudoIndustrialSAT(2021, 650, 3, 30, 0.8);
		//SATProblemGenerator SATGen=new RandomPseudoIndustrialSAT(4043, 1100, 3, 40, 0.8);
		SATProblemGenerator SATGen=new RandomPseudoIndustrialSAT(6065, 1650, 3, 40, 0.8);
		//SATProblemGenerator SATGen=new RandomPseudoIndustrialSAT(9086, 2200, 3, 40, 0.8);
		int numberSamples=750000;
		int alg=9;
		//avgVanilla(SATGen);
		
		//SATGen.generateSAT().toCNF(new File("/home/willie/Software_Verification/cbmc-cbmc-5.4/minisat-2.2.1/PIndus4043c1100.cnf"));
		
		
		testName="PIndusFixConfClausesInformed"+SATGen.getNumberClauses()+"c"+SATGen.getNumberVariables()+"v"+alg+"a"+numberSamples+"ns";
		
		if(generate)
		{
			int numberCreated=200;
			while(numberCreated<1000)
			{
				SAT satProb=SATGen.generateSAT();
				int[] used=new int[SATGen.getNumberVariables()];
				for(int varInd=0; varInd<used.length; varInd++)
				{
					for(int clauseInd=0; clauseInd<satProb.clauses.size(); clauseInd++)
					{
						for(int clauseVarInd=0; clauseVarInd<satProb.clauses.get(clauseInd).variables.size(); clauseVarInd++)
						{
							used[satProb.variables.indexOf(satProb.clauses.get(clauseInd).variables.get(clauseVarInd))]=1;
						}
					}
				}

				if(used[0]==1 && used[used.length-1]==1)
				{
					SATGen.generateSAT().toCNF(new File("/home/willie/Software_Verification/cbmc-cbmc-5.4/minisat-2.2.1/"+testName+""+numberCreated+".cnf"));
					numberCreated++;
					System.out.println(numberCreated);
				}
			}
		}
		else
		{
			/*
			SAT sat=SATGen.generateSAT();
			boolean[] result=mlSATS4J.solve(sat.toCNF());
			System.out.println(sat);
		    System.out.println("MLSAT result: "+(result!=null));
		    System.out.println(Arrays.toString(result));
		    
			
		    SATSolverSAT4J vanillaSolver=new SATSolverSAT4J();
		    result=vanillaSolver.solve(sat.toCNF());
		    System.out.println("vanillaSolver result: "+(result!=null));
		    System.out.println(Arrays.toString(result));
			*/
		    
			/*
			SAT sat=SATGen.generateSAT();
			String cnf=sat.toCNF();
		    MLSAT mlSAT=new MLSAT(SATGen);
			mlSAT.trainNetwork(10000, false, true);
			//testAgainstVanillaOrig(mlSAT, SATGen);
			
			
			mlSAT.solve(sat);
			*/
			SATSolverSAT4J mlSATS4J_1=new SATSolverSAT4J();
			SATSolverSAT4J mlSATS4J_2=new MLSATSAT4J(false, SATGen, alg);
			
			for(int iteration=0; iteration<1; iteration++)
			{
				System.out.println("Iteration: "+iteration);
				((MLSATSAT4J)mlSATS4J_2).trainNetwork(numberSamples, false, false, mlSATS4J_1);
				//mlSATS4J_2.solve("/home/willie/Software_Verification/cbmc-cbmc-5.4/minisat-2.2.1/PIndusFixConfClausesInformed2021c650v9a100000ns1.cnf");
				testAgainstVanilla(mlSATS4J_2, SATGen);
				//mlSATS4J_1=mlSATS4J_2;
			}
			
			//mlSATS4J.solve(cnf);
			
			
			//printMathematica(mlSATS4J.nonePoints);
			//printMathematica(mlSATS4J.vsidsPoints);
			//printMathematica(mlSATS4J.dlisPoints);
		}
	}
	
	private static void printMathematica(List<int[]> points)
	{
		System.out.print("{");
		for(int[] point: points)
		{
			System.out.print("{"+point[0]+", "+point[1]+"},");
		}
		System.out.println("}");
	}
	
	private static void testRandomPIndustiralMLSAT()
	{
		//RandomPseudoIndustrialSAT SATGen=new RandomPseudoIndustrialSAT(2065, 500, 3, 40, 0.8);
		SATProblemGenerator bothSPG=new RandomRandomPI(new RandomPseudoIndustrialSAT(124, 30, 3, 10, 0.8), new RandomSATGenerator(105, 3, 30));
		
		//avgVanilla(SATGen);
		MLSATSAT4J mlSATS4J=new MLSATSAT4J(false, bothSPG, 8);
		
		testName="RandomAndPIndusFixConfClausesInformed"+bothSPG.getNumberClauses()+"c"+bothSPG.getNumberVariables()+"v"+mlSATS4J.alg+"a";
		mlSATS4J.trainNetwork(120000, false, true);
		//mlSATS4J.solve(cnf);
		testAgainstVanilla(mlSATS4J, bothSPG);
	}
	
	static final int numberTests=100;
	
	public static void testAgainstVanilla(SATSolverSAT4J solver, SATProblemGenerator spg)
	{
		long totalSolverSteps=0;
		long totalSolverTime=0;
		
		long totalDPLLSteps=0;
		long totalDPLLTime=0;
		
		SATSolverSAT4J vanillaSolver=new SATSolverSAT4J();
		
		for(int testNumber=0; testNumber<numberTests; testNumber++)
		{
			SAT testInstance=null;
			
			while(testInstance==null)
			{
				testInstance=spg.generateSAT();
			}
			
			//testInstance.toCNF(new File("/home/c/workspace/MiniSAT/SAT_Problems/Argue/PIndustrial120c30vNewProbNots"+testNumber+".cnf"));
			testInstance.toCNF(new File("C:\\Users\\C\\workspace\\SAT_Solvers_GPU\\SAT_Problems\\Arguementation\\PIndus4043c1100v"+testNumber+".cnf"));
			
			SAT testInstanceDPLL=testInstance.cloneSATVariables();
			
			String cnf=testInstance.toCNF();
			
			boolean[] solverRes;
			boolean[] dpllRes;
			
			long startTime=System.nanoTime();
			solverRes=solver.solve(cnf);
			startTime=System.nanoTime()-startTime;
			totalSolverSteps+=solver.getNumberOfSteps();
			totalSolverTime+=startTime;
			((MLSATSAT4J)solver).reset();
			
			startTime=System.nanoTime();
			dpllRes=vanillaSolver.solve(cnf);
			startTime=System.nanoTime()-startTime;
			totalDPLLSteps+=vanillaSolver.getNumberOfSteps();
			totalDPLLTime+=startTime;
			vanillaSolver.reset();
			
			if(solverRes==null && dpllRes!=null)
			{
				System.out.println("solverRes==null && dpllRes!=null");
			}
			if(solverRes!=null && dpllRes==null)
			{
				System.out.println("solverRes!=null && dpllRes==null");
			}
		}
		
		System.out.println("Solver Steps: "+totalSolverSteps+" Solver Time "+totalSolverTime);
		System.out.println("DPLL Steps: "+totalDPLLSteps+" DPLL Time "+totalDPLLTime);
	}
	
	public static void testAgainstVanillaOrig(SATSolver solver, SATProblemGenerator spg)
	{
		long totalSolverSteps=0;
		long totalSolverTime=0;
		
		long totalDPLLSteps=0;
		long totalDPLLTime=0;
		
		SATSolverSAT4J vanillaSolver=new SATSolverSAT4J();
		
		for(int testNumber=0; testNumber<numberTests; testNumber++)
		{
			SAT testInstance=null;
			
			while(testInstance==null)
			{
				testInstance=spg.generateSAT();
			}
			
			//testInstance.toCNF(new File("/home/c/workspace/MiniSAT/SAT_Problems/Argue/PIndustrial120c30vNewProbNots"+testNumber+".cnf"));
			testInstance.toCNF(new File("C:\\Users\\C\\workspace\\SAT_Solvers_GPU\\SAT_Problems\\Arguementation\\PIndus4043c1100v"+testNumber+".cnf"));
			
			SAT testInstanceDPLL=testInstance.cloneSATVariables();
			
			String cnf=testInstance.toCNF();
			
			long startTime=System.nanoTime();
			boolean sat=(solver.solve(testInstanceDPLL)[0]!=null);
			startTime=System.nanoTime()-startTime;
			totalSolverSteps+=solver.numberSteps;
			totalSolverTime+=startTime;
			((MLSAT)solver).reset();
			
			boolean[] result;
			startTime=System.nanoTime();
			result=vanillaSolver.solve(cnf);
			startTime=System.nanoTime()-startTime;
			totalDPLLSteps+=vanillaSolver.getNumberOfSteps();
			totalDPLLTime+=startTime;
			vanillaSolver.reset();
			
			if(sat && result==null)
			{
				System.out.println("sat && result==null");
			}
			if(!sat && result!=null)
			{
				System.out.println("!sat && result!=null");
			}
		}
		
		System.out.println("Solver Steps: "+totalSolverSteps+" Solver Time "+totalSolverTime);
		System.out.println("DPLL Steps: "+totalDPLLSteps+" DPLL Time "+totalDPLLTime);
	}

	static final int numberDPLLTests=10;
	
	public static void avgVanilla(SATProblemGenerator spg)
	{
		SATSolverSAT4J vanillaSolver=new SATSolverSAT4J();
		
		long totalDPLLSteps=0;
		long totalDPLLTime=0;
		
		for(int testNumber=0; testNumber<numberDPLLTests; testNumber++)
		{
			long startTime;
			SAT testInstanceDPLL=spg.generateSAT();
			String satcnf=testInstanceDPLL.toCNF();
			startTime=System.nanoTime();
			vanillaSolver.solve(satcnf);
			startTime=System.nanoTime()-startTime;
			totalDPLLSteps+=vanillaSolver.getNumberOfSteps();
			totalDPLLTime+=startTime;
			vanillaSolver.reset();
		}
		
		System.out.println("DPLL Steps: "+totalDPLLSteps+" DPLL Time "+totalDPLLTime);
	}
	
	public static void solvePIndus() throws IOException
	{
		SATProblemGenerator SATGen=new RandomPseudoIndustrialSAT(2021, 650, 3, 30, 0.8);
		SATSolverSAT4J vanillaSolver=new SATSolverSAT4J(false, SATGen, 9);
        String file=new String(Files.readAllBytes(new File("/home/c/workspace2/cbmc-cbmc-5.4/minisat-2.2.1/PIndusFixConfClausesInformed2021c650v9a100000ns1.cnf").toPath()));
		vanillaSolver.solve(file);
	}

}
