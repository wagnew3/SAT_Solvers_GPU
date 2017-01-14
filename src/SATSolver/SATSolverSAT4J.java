package SATSolver;

import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.util.HashMap;
import java.util.Map.Entry;

import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.minisat.constraints.cnf.OriginalWLClause;
import org.sat4j.minisat.core.Solver;
import org.sat4j.reader.LecteurDimacs;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.ISolverService;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ModelIterator;
import org.sat4j.tools.RupSearchListener;

import MLSAT.TestMLSATSAT4J;
import SATProblem.Clause;
import SATProblem.SAT;
import SATProblem.Variable;
import SATProblemGeneration.SATProblemGenerator;
import filters.ScaleFilter;
import network.SplitNetwork;

public class SATSolverSAT4J 
{
	
	protected boolean verbose;
	protected ISolver solver;
	protected ModelIterator mi;
	protected Reader dimacsReader;
	public int alg;
	public ScaleFilter scaleFilterInputs;
	public SplitNetwork network;
	
	public SATSolverSAT4J()
	{
		this(false);
	}
	
	public SATSolverSAT4J(boolean verbose)
	{
		this.verbose=verbose;
		solver=SolverFactory.newDefault();
        mi=new ModelIterator(solver);
        solver.setTimeout(3600); // 1 hour timeout
        dimacsReader=new LecteurDimacs(mi);
	}
	
	public SATSolverSAT4J(boolean verbose, SATProblemGenerator satProblem, int alg)
	{
		this.verbose=verbose;
		this.alg=alg;
		solver=SolverFactory.newDefaultML(this, satProblem.getNumberVariables());
        mi=new ModelIterator(solver);
        solver.setTimeout(3600); // 1 hour timeout
        dimacsReader=new LecteurDimacs(mi);
	}
	
	public boolean[] solve(String cnf)
	{
		try 
        {
            boolean unsat = true;
            IProblem problem = dimacsReader.parseInstance(new ByteArrayInputStream(cnf.getBytes(StandardCharsets.UTF_8)));
            //IProblem problem = reader.parseInstance("C:\\Users\\C\\workspace\\SAT_Solvers_GPU\\SAT_Problems\\MD5-27-4.cnf");
            
            String proofFile = TestMLSATSAT4J.dataDir+"testResult" + ".rupproof";
            this.solver.setSearchListener(new RupSearchListener<ISolverService>(
                            proofFile));
            
            long time=System.nanoTime();
            int[] model=problem.findModel();
            time=System.nanoTime()-time;
            if(verbose)
            {
	            System.out.println("time: "+time);
	            for(Entry<String, Number> stat:((org.sat4j.minisat.core.Solver)solver).getStats().toMap().entrySet())
	            {
	            	System.out.println(stat.getKey()+": "+stat.getValue());
	            }
            }
            if(model!=null)
            {
               model=problem.model();
               if(verbose)
               {
            	   String result="";
                   for(int varInd=0; varInd<model.length; varInd++)
                   {
                	   result+=model[varInd]+": "+problem.model(Math.abs(model[varInd]))+", ";
                   }
            	   System.out.println("SAT "+result);
               }
               boolean[] resultSettings=new boolean[model.length];
               for(int varInd=0; varInd<model.length; varInd++)
               {
            	   resultSettings[varInd]=problem.model(Math.abs(model[varInd]));
               }
               return resultSettings;
            }
            else
            {
        		//System.out.println("UNSAT");
            	return null;
            }
        } 
        catch (FileNotFoundException e) 
		{
            e.printStackTrace();
        } 
		catch (ParseFormatException e) 
		{
            e.printStackTrace();
        } 
		catch (IOException e) 
		{
            e.printStackTrace();
        } 
		catch (ContradictionException e) 
		{
            System.out.println("Unsatisfiable (trivial)!");
        } 
		catch (TimeoutException e) 
		{
            System.out.println("Timeout, sorry!");
        }
		return null;
	}
	
	public boolean[] solve(SAT sat)
	{
		try 
        {
			setFromSAT(sat);
            boolean unsat = true;
            long time=System.nanoTime();
            int[] model=solver.findModel();
            time=System.nanoTime()-time;
            if(verbose)
            {
	            System.out.println("time: "+time);
	            for(Entry<String, Number> stat:((org.sat4j.minisat.core.Solver)solver).getStats().toMap().entrySet())
	            {
	            	System.out.println(stat.getKey()+": "+stat.getValue());
	            }
            }
            if(model!=null)
            {
               model=solver.model();
               if(verbose)
               {
            	   String result="";
                   for(int varInd=0; varInd<model.length; varInd++)
                   {
                	   result+=model[varInd]+": "+solver.model(Math.abs(model[varInd]))+", ";
                   }
            	   System.out.println("SAT "+result);
               }
               boolean[] resultSettings=new boolean[sat.variables.size()];
               for(int varInd=0; varInd<model.length; varInd++)
               {
            	   resultSettings[varInd]=solver.model(Math.abs(model[varInd]));
               }
               return resultSettings;
            }
            else
            {
            	if(verbose)
            	{
            		System.out.println("UNSAT");
            	}
            	return null;
            }
        } 
		catch (TimeoutException e) 
		{
            System.out.println("Timeout, sorry!");
        }
		return null;
	}
	
	public long getNumberOfSteps()
	{
		return ((org.sat4j.minisat.core.Solver)solver).getStats().decisions;
	}
	
	public void reset()
	{
		solver.reset();
	}
	
	public void setFromSAT(SAT sat)
	{
		reset();
		solver.newVar(sat.variables.size());
		solver.setExpectedNumberOfClauses(sat.clauses.size());
		
		HashMap<Variable, Integer> variablePositions=new HashMap<>();
		for(int variableIndex=0; variableIndex<sat.variables.size(); variableIndex++)
		{
			variablePositions.put(sat.variables.get(variableIndex), variableIndex);
		}
		
		IVecInt literals = new VecInt();
		for(Clause clause: sat.clauses)
		{
			literals.clear();
			for(int varInd=0; varInd<clause.variables.size(); varInd++)
			{
				if(clause.nots.get(varInd)==0)
				{
					literals.push(variablePositions.get(clause.variables.get(varInd))+1);
				}
				else
				{
					literals.push(-(variablePositions.get(clause.variables.get(varInd))+1));
				}
			}
			for(int litInd=0; litInd<literals.size(); litInd++)
			{
				if(clause.nots.get(litInd)==1 && literals.get(litInd)>0)
				{
					int u=0;
				}
			}
			try 
			{
				solver.addClause(literals);
			} 
			catch (ContradictionException e) 
			{
				e.printStackTrace();
			}
		}
	}
	
	public ISolver getSolver()
	{
		return solver;
	}

}
