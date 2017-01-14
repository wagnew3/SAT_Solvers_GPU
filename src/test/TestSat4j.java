package test;

import java.io.ByteArrayInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.Arrays;
import java.util.Map.Entry;

import org.sat4j.minisat.SolverFactory;
import org.sat4j.reader.InstanceReader;
import org.sat4j.reader.LecteurDimacs;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.reader.Reader;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IProblem;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.TimeoutException;
import org.sat4j.tools.ModelIterator;

import SATProblem.SAT;
import SATProblemGeneration.RandomArgumentation;
import SATProblemGeneration.RandomPseudoIndustrialSAT;
import SATProblemGeneration.RandomSATGenerator;

public class TestSat4j 
{
	
	public static void main(String[] args)
	{
		//RandomPseudoIndustrialSAT SATGen=new RandomPseudoIndustrialSAT(9086, 2200, 3, 40, 0.8); 
		RandomPseudoIndustrialSAT SATGen=new RandomPseudoIndustrialSAT(4043, 1100, 3, 20, 0.8);  
		SAT sat=SATGen.generateSAT();
		
		
		ISolver solver = SolverFactory.newDefault();
        ModelIterator mi = new ModelIterator(solver);
        solver.setTimeout(3600); // 1 hour timeout
        Reader reader = new LecteurDimacs(mi);
        //Reader reader = new InstanceReader(mi);

        // filename is given on the command line
        try 
        {
            boolean unsat = true;
            IProblem problem = reader.parseInstance(new ByteArrayInputStream(sat.toCNF().getBytes(StandardCharsets.UTF_8)));
            //IProblem problem = reader.parseInstance("C:\\Users\\C\\workspace\\SAT_Solvers_GPU\\SAT_Problems\\MD5-27-4.cnf");
            long time=System.nanoTime();
            int[] model=problem.findModel();
            time=System.nanoTime()-time;
            System.out.println("time: "+time);
            for(Entry<String, Number> stat:((org.sat4j.minisat.core.Solver)solver).getStats().toMap().entrySet())
            {
            	System.out.println(stat.getKey()+": "+stat.getValue());
            }
            if(model!=null)
            {
               model = problem.model();
               String result="";
               for(int varInd=0; varInd<model.length; varInd++)
               {
            	   result+=model[varInd]+": "+problem.model(Math.abs(model[varInd]))+", ";
               }
               System.out.println("SAT "+result);
            }
            else
            {
            	System.out.println("UNSAT");
            }
                // do something for unsat case
        } 
        catch (FileNotFoundException e) {
            e.printStackTrace();
        } catch (ParseFormatException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        } catch (ContradictionException e) {
            System.out.println("Unsatisfiable (trivial)!");
        } catch (TimeoutException e) {
            System.out.println("Timeout, sorry!");
        }
	}

}
