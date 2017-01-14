package SATProblem;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;

public class Clause 
{
    
    public List<Variable> variables;
    public List<Integer> nots;
    
    public Clause(List<Variable> variables, List<Integer> nots)
    {
		this.variables=variables;
		this.nots=nots;
    }
    
    public int isSAT()
    {
		boolean varUnassigned=false;
		for(int variableInd=0; variableInd<variables.size(); variableInd++)
		{
		    int varValue=variables.get(variableInd).value;
		    if(nots.get(variableInd)==1)
		    {
				if(varValue==1)
				{
				    varValue=-1;
				}
				else if(varValue==-1)
				{
				    varValue=1;
				}
		    }
		    if(varValue==0)
		    {
		    	varUnassigned=true;
		    }
		    if(varValue==1)
		    {
		    	return 1;
		    }
		}
		if(varUnassigned)
		{
		    return 0;
		}
		else
		{
		    return -1;
		}
    }
    
    public Clause cloneClause()
    {
		List<Variable> newVariables=new ArrayList<>();
		for(Variable variable: variables)
		{
		    newVariables.add(variable);
		}
		
		List<Integer> newNots=new ArrayList<>();
		for(Integer not: nots)
		{
		    newNots.add(not);
		}
		
		return new Clause(newVariables, newNots);
    }
    
    public void setVariableNot(int varInd, int value)
    {
		if(nots.get(varInd)==1)
		{
		    if(value==-1)
		    {
			value=1;
		    }
		    else if(value==1)
		    {
			value=-1;
		    }
		}
		variables.get(varInd).value=value;
    }
    
    public String toString(List<Variable> variables)
    {
		String string="";
		for(int variableInd=0; variableInd<this.variables.size(); variableInd++)
		{
		    if(nots.get(variableInd)==1)
		    {
			string+="~";
		    }
		    string+=variables.indexOf(this.variables.get(variableInd))+"|";
		}
		if(string.length()>0)
		{
		    string=string.substring(0, string.length()-1);
		}
		return string;
    }
    
    public void sort(HashMap<Variable, Integer> variableLoc)
    {
    	List<VarNot> varNots=new ArrayList<>();
    	for(int varInd=0; varInd<variables.size(); varInd++)
    	{
    		varNots.add(new VarNot(nots.get(varInd), variableLoc.get(variables.get(varInd)), 
    				variables.get(varInd)));
    	}
    	Collections.sort(varNots);
    	List<Variable> newVariables=new ArrayList<>();
		List<Integer> newNots=new ArrayList<>();
		for(VarNot varNot: varNots)
		{
			newVariables.add(varNot.variable);
		    newNots.add(varNot.not);
		}
		variables=newVariables;
		nots=newNots;
    }

}

class VarNot implements Comparable<VarNot>
{
	
	int not;
	int var;
	Variable variable;
	
	public VarNot(int not, int var, Variable variable)
	{
		this.not=not;
		this.var=var;
		this.variable=variable;
	}

	@Override
	public int compareTo(VarNot o)
	{
		return var-o.var;
	}	
	
}
