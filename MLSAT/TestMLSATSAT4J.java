package MLSAT;

import java.io.File;
import java.util.Arrays;
import java.util.List;

import SATProblem.SAT;
import SATProblem.Variable;
import SATProblemGeneration.RandomArgumentation;
import SATProblemGeneration.RandomPseudoIndustrialSAT;
import SATProblemGeneration.RandomSATGenerator;
import SATProblemGeneration.SATProblemGenerator;
import SATSolver.DPLL;
import SATSolver.SATSolver;
import SATSolver.SATSolverSAT4J;

public class TestMLSATSAT4J 
{
	
	public static String dataDir="C:\\Users\\C\\workspace\\SAT_Solvers_GPU\\data\\";
	
	public static String testName="PIndus60c30v";
	
	public static void main(String[] args)
	{
		//testDPLLMLSAT();
		//testArgumentationMLSAT();
		testPIndustiralMLSAT();
	}
	
	private static void testDPLLMLSAT()
	{
		RandomSATGenerator threeSAT=new RandomSATGenerator(100, 3, 70);
		avgVanilla(threeSAT);
		MLSATSAT4J mlSATS4J=new MLSATSAT4J(true, threeSAT);
		
		SAT sat=threeSAT.generateSAT();
		boolean[] result=mlSATS4J.solve(sat.toCNF());
		System.out.println(sat);
	    System.out.println(result!=null);
	    System.out.println(Arrays.toString(result));
		
	    /*
	    MLSAT mlSAT=new MLSAT(threeSAT);
		mlSAT.trainNetwork(1000);
		testAgainstVanillaOrig(mlSAT, threeSAT);
		*/
	    
		/*
		mlSATS4J.trainNetwork(5000);
		testAgainstVanilla(mlSATS4J, threeSAT);
		*/
	}
	
	private static void testArgumentationMLSAT()
	{
		RandomArgumentation argueSAT=new RandomArgumentation(6000, 300);
		avgVanilla(argueSAT);
		MLSATSAT4J mlSAT=new MLSATSAT4J(true, argueSAT);
		
		SAT sat=argueSAT.generateSAT();
		boolean[] result=mlSAT.solve(sat.toCNF());
		System.out.println(sat);
	    System.out.println(result!=null);
	    System.out.println(Arrays.toString(result));
		
		mlSAT.trainNetwork(10000);
		
		testAgainstVanilla(mlSAT, argueSAT);
	}
	
	private static void testPIndustiralMLSAT()
	{
		//RandomPseudoIndustrialSAT SATGen=new RandomPseudoIndustrialSAT(4063, 1110, 3, 30, 0.8);
		RandomPseudoIndustrialSAT SATGen=new RandomPseudoIndustrialSAT(120, 60, 3, 5, 0.8);
		//avgVanilla(SATGen);
		MLSATSAT4J mlSATS4J=new MLSATSAT4J(false, SATGen, 1);
		
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
	    
		mlSATS4J.trainNetwork(250000, false, false);
		//mlSATS4J.solve(cnf);
		testAgainstVanilla(mlSATS4J, SATGen);
		
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
			
			while(testInstance==null || vanillaSolver.solve(testInstance)==null)
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
			
			while(testInstance==null || vanillaSolver.solve(testInstance.toCNF())==null)
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

}
