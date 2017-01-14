package test;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import SATProblem.SAT;
import SATProblem.Variable;
import SATProblemGeneration.RandomArgumentation;
import SATProblemGeneration.RandomSATGenerator;
import SATProblemGeneration.SATProblemGenerator;
import SATSolver.DPLL;
import SATSolver.SATSolver;

public class Test 
{
    
    public static void main(String[] args)
    {
    	//testRandomSat();
    	saveRandomArgumentation();
    }

    public static void testRandomSat()
    {
		SATProblemGenerator satProb=new RandomSATGenerator(50, 3, 10);
		satProb.generateSAT().toCNF(new File("/home/c/workspace/MiniSAT/SAT_Problems/3SAT250c50v.cnf"));
		SATSolver satSolver=new DPLL();
		while(true)
		{
		    SAT sat=satProb.generateSAT();
		    Object[] result=satSolver.solve(sat);
		    System.out.println(sat);
		    System.out.println(result[0]);
		    for(int varInd=0; varInd<((List<Variable>)result[1]).size(); varInd++)
		    {
		    	System.out.print(varInd+":"+((List<Variable>)result[1]).get(varInd).value+" ");
		    }
		    System.out.println();
		    System.out.println();
		    int u=0;
		}
    }
    
    public static void saveRandomArgumentation()
    {
    	SATProblemGenerator satProb=new RandomArgumentation(25000, 500);
    	SAT sat=satProb.generateSAT();
    	SATSolver satSolver=new DPLL();
    	satSolver.solve(sat);
    	System.out.println(satSolver.numberSteps);
    	sat.toCNF(new File("/home/c/workspace/MiniSAT/SAT_Problems/Argumentation50c10v.cnf"));
    }
    
    public static void testRandomSat()
    {
		SATProblemGenerator satProb=new RandomArgumentation(1000, 100);
		satProb.generateSAT().toCNF(new File("/home/c/workspace/MiniSAT/SAT_Problems/3SAT250c50v.cnf"));
		SATSolver satSolver=new DPLL();
		while(true)
		{
		    SAT sat=satProb.generateSAT();
		    Object[] result=satSolver.solve(sat);
		    System.out.println(sat);
		    System.out.println(result[0]);
		    for(int varInd=0; varInd<((List<Variable>)result[1]).size(); varInd++)
		    {
		    	System.out.print(varInd+":"+((List<Variable>)result[1]).get(varInd).value+" ");
		    }
		    System.out.println();
		    System.out.println();
		    int u=0;
		}
    }
    
}
