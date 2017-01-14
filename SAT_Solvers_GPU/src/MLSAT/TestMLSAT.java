package MLSAT;

import java.io.File;
import java.util.List;

import SATProblem.SAT;
import SATProblem.Variable;
import SATProblemGeneration.RandomArgumentation;
import SATProblemGeneration.RandomPseudoIndustrialSAT;
import SATProblemGeneration.RandomSATGenerator;
import SATProblemGeneration.SATProblemGenerator;
import SATSolver.DPLL;
import SATSolver.SATSolver;

public class TestMLSAT 
{
	
	public static void main(String[] args)
	{
		//testDPLLMLSAT();
		testArgumentationMLSAT();
		//testPIndustiralMLSAT();
	}
	
	private static void testDPLLMLSAT()
	{
		RandomSATGenerator twoSAT=new RandomSATGenerator(500, 3, 100);
		//avgDPLL(twoSAT);
		MLSAT mlSAT=new MLSAT(twoSAT);
		
		SAT sat=twoSAT.generateSAT();
		Object[] result=mlSAT.solve(sat);
		System.out.println(sat);
	    System.out.println(sat.isSAT());
	    for(int varInd=0; varInd<((List<Variable>)result[1]).size(); varInd++)
	    {
	    	System.out.print(varInd+":"+((List<Variable>)result[1]).get(varInd).value+" ");
	    }
	    System.out.println();
	    System.out.println();
		
		mlSAT.trainNetwork(5000);
		testAgainstDPLL(mlSAT, twoSAT);
	}
	
	private static void testArgumentationMLSAT()
	{
		RandomArgumentation twoSAT=new RandomArgumentation(6000, 300);
		avgDPLL(twoSAT);
		MLSAT mlSAT=new MLSAT(twoSAT);
		
		SAT sat=twoSAT.generateSAT();
		Object[] result=mlSAT.solve(sat);
		System.out.println(sat);
	    System.out.println(sat.isSAT());
	    for(int varInd=0; varInd<((List<Variable>)result[1]).size(); varInd++)
	    {
	    	System.out.print(varInd+":"+((List<Variable>)result[1]).get(varInd).value+" ");
	    }
	    System.out.println();
	    System.out.println();
		
		mlSAT.trainNetwork(10000);
		testAgainstDPLL(mlSAT, twoSAT);
	}
	
	private static void testPIndustiralMLSAT()
	{
		RandomPseudoIndustrialSAT SATGen=new RandomPseudoIndustrialSAT(120, 30, 
				3, 10, 0.8);
		
		//avgDPLL(SATGen);
		MLSAT mlSAT=new MLSAT(SATGen);
		
		SAT sat=SATGen.generateSAT();
		Object[] result=mlSAT.solve(sat);
		System.out.println(sat);
	    System.out.println(sat.isSAT());
	    for(int varInd=0; varInd<((List<Variable>)result[1]).size(); varInd++)
	    {
	    	System.out.print(varInd+":"+((List<Variable>)result[1]).get(varInd).value+" ");
	    }
	    System.out.println();
	    System.out.println();
		
		mlSAT.trainNetwork(50000);
		testAgainstDPLL(mlSAT, SATGen);
	}
	
	static final int numberTests=100;
	
	public static void testAgainstDPLL(SATSolver solver, SATProblemGenerator spg)
	{
		long totalSolverSteps=0;
		long totalSolverTime=0;
		
		long totalDPLLSteps=0;
		long totalDPLLTime=0;
		
		DPLL dpll=new DPLL();
		
		for(int testNumber=0; testNumber<numberTests; testNumber++)
		{
			SAT testInstance=null;
			
			while(testInstance==null || ((SAT)dpll.solve(testInstance.cloneSATVariables())[0]).isSAT()!=1)
			{
				testInstance=spg.generateSAT();
			}
			
			//testInstance.toCNF(new File("/home/c/workspace/MiniSAT/SAT_Problems/Argue/PIndustrial120c30vNewProbNots"+testNumber+".cnf"));
			testInstance.toCNF(new File("C:\\Users\\C\\workspace\\SAT_Solvers_GPU\\SAT_Problems\\Arguementation\\Arguementation6000c300v"+testNumber+".cnf"));
			
			SAT testInstanceDPLL=testInstance.cloneSATVariables();
			
			long startTime=System.nanoTime();
			solver.solve(testInstance);
			startTime=System.nanoTime()-startTime;
			totalSolverSteps+=solver.numberSteps;
			totalSolverTime+=startTime;
			((MLSAT)solver).reset();
			
			startTime=System.nanoTime();
			dpll.solve(testInstanceDPLL);
			startTime=System.nanoTime()-startTime;
			totalDPLLSteps+=dpll.numberSteps;
			totalDPLLTime+=startTime;
		}
		
		System.out.println("Solver Steps: "+totalSolverSteps+" Solver Time "+totalSolverTime);
		System.out.println("DPLL Steps: "+totalDPLLSteps+" DPLL Time "+totalDPLLTime);
	}

	static final int numberDPLLTests=10;
	
	public static void avgDPLL(SATProblemGenerator spg)
	{
		long totalDPLLSteps=0;
		long totalDPLLTime=0;
		
		DPLL dpll=new DPLL();
		
		for(int testNumber=0; testNumber<numberDPLLTests; testNumber++)
		{
			long startTime;
			SAT testInstanceDPLL=spg.generateSAT();
			startTime=System.nanoTime();
			dpll.solve(testInstanceDPLL);
			startTime=System.nanoTime()-startTime;
			totalDPLLSteps+=dpll.numberSteps;
			totalDPLLTime+=startTime;
		}
		
		System.out.println("DPLL Steps: "+totalDPLLSteps+" DPLL Time "+totalDPLLTime);
	}
	
}
