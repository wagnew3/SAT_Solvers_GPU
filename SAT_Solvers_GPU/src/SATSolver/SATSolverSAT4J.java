package SATSolver;

import java.io.ByteArrayInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.util.Map.Entry;

import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.LecteurDimacs;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ModelIterator;

public class SATSolverSAT4J 
{
	
	protected boolean verbose;
	protected ISolver solver;
	protected ModelIterator mi;
	protected Reader reader;
	
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
        reader=new LecteurDimacs(mi);
	}
	
	public boolean[] solve(String cnf)
	{
		try 
        {
            boolean unsat = true;
            IProblem problem = reader.parseInstance(new ByteArrayInputStream(cnf.getBytes(StandardCharsets.UTF_8)));
            //IProblem problem = reader.parseInstance("C:\\Users\\C\\workspace\\SAT_Solvers_GPU\\SAT_Problems\\MD5-27-4.cnf");
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
            	if(verbose)
            	{
            		System.out.println("UNSAT");
            	}
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
	
	public long getNumberOfSteps()
	{
		return ((org.sat4j.minisat.core.Solver)solver).getStats().decisions;
	}
	
	public void reset()
	{
		solver.reset();
	}

}
