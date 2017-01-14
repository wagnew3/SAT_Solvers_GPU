package SATProblem;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

public class SAT 
{
    
    public List<Clause> clauses;
    public List<Variable> variables;
    public List<Integer> setVariables;
    public HashMap<Variable, Integer> variableFreq;
    public HashMap<Variable, Integer> variableLoc;
    
    public SAT parent;
    
    public SAT(List<Clause> clauses, List<Variable> variables)
    {
		this.clauses=clauses;
		this.variables=variables;
		parent=null;
		variableFreq=new HashMap<>();
		for(Clause clause: clauses)
		{
			for(Variable variable: clause.variables)
			{
				Integer val=variableFreq.get(variable);
				if(val==null)
				{
					variableFreq.put(variable, 1);
				}
				else
				{
					variableFreq.put(variable, val+1);
				}
			}
		}
		
		variableLoc=new HashMap<>();
		for(int varInd=0; varInd<variables.size(); varInd++)
		{
			variableLoc.put(variables.get(varInd), varInd);
		}
		
		for(Clause clause: clauses)
		{
			clause.sort(variableLoc);
		}
    }
    
    public SAT(List<Clause> clauses, List<Variable> variables, HashMap<Variable, Integer> variableLoc)
    {
		this.clauses=clauses;
		this.variables=variables;
		this.variableLoc=variableLoc;
		parent=null;
		variableFreq=new HashMap<>();
		for(Clause clause: clauses)
		{
			for(Variable variable: clause.variables)
			{
				Integer val=variableFreq.get(variable);
				if(val==null)
				{
					variableFreq.put(variable, 1);
				}
				else
				{
					variableFreq.put(variable, val+1);
				}
			}
		}
    }
    
    //-1 unsat, 0 more vars need to be assigned, 1 sat
    public int isSAT()
    {
    	if(clauses.isEmpty())
    	{
    		int u=0;
    	}
		boolean varUnassigned=false;
		for(Clause clause: clauses)
		{
		    int clauseState=clause.isSAT();
		    if(clauseState==0)
		    {
		    	varUnassigned=true;
		    }
		    if(clauseState==-1)
		    {
		    	return -1;
		    }
		}
		if(varUnassigned)
		{
		    return 0;
		}
		else
		{
		    return 1;
		}
    }
    
    public SAT cloneSAT()
    {
		List<Clause> newClauses=new ArrayList<>();
		for(Clause clause: clauses)
		{
		    newClauses.add(clause.cloneClause());
		}
		SAT sat=new SAT(newClauses, variables, variableLoc);
		return sat;
    }
    
    public SAT cloneSATVariables()
    {
		List<Variable> newVariables=new ArrayList<>();
		for(int varInd=0; varInd<variables.size(); varInd++)
		{
			Variable newVariable=new Variable();
			newVariable.value=variables.get(varInd).value;
			newVariables.add(newVariable);
		}
		
		List<Clause> newClauses=new ArrayList<>();
		for(Clause clause: clauses)
		{
			Clause newClause=clause.cloneClause();
			for(int varInd=0; varInd<newClause.variables.size(); varInd++)
			{
				newClause.variables.set(varInd, newVariables.get(variables.indexOf(newClause.variables.get(varInd))));
			}
			
		    newClauses.add(newClause);
		}
		
		SAT sat=new SAT(newClauses, newVariables);
		return sat;
    }
    
    public boolean unsetVariables()
    {
		for(Variable variable: variables)
		{
		    if(variable.value==0)
		    {
		    	return true;
		    }
		}
		return false;
    }
    
    @Override
    public String toString()
    {
		String string="";
		for(Clause clause: clauses)
		{
		    string+="("+clause.toString(variables)+")&";
		}
		if(string.length()>0)
		{
		    string=string.substring(0, string.length()-1);
		}
		return string;
    }
    
    public String toCNF()
    {
    	HashMap<Variable, Integer> variableIndices=new HashMap<>();
    	for(int varInd=0; varInd<variables.size(); varInd++)
    	{
    		variableIndices.put(variables.get(varInd), varInd);
    	}

    	String cdf="p cnf "+variables.size()+" "+clauses.size()+"\n";
    	for(Clause clause: clauses)
    	{
    		for(int varInd=0; varInd<clause.variables.size(); varInd++)
    		{
    			if(clause.nots.get(varInd)==1)
    			{
    				cdf+="-";
    			}
    			cdf+=variableIndices.get(clause.variables.get(varInd))+1;
    			cdf+=" ";
    		}
    		cdf+="0\n";
    	}
    	return cdf;
    }
    
    public void toCNF(File saveLocation)
    {
    	try 
    	{
			Files.write(saveLocation.toPath(), toCNF().getBytes());
		} 
    	catch (IOException e) 
    	{
			e.printStackTrace();
		}
    }

}
