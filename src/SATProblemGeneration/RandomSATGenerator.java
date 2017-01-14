package SATProblemGeneration;

import java.util.ArrayList;
import java.util.List;

import SATProblem.Clause;
import SATProblem.SAT;
import SATProblem.Variable;

public class RandomSATGenerator extends SATProblemGenerator
{

    protected int numberClauses;
    protected int numberVariablesPerClause;
    protected int numberVariables;
    
    public RandomSATGenerator(int numberClauses, int numberVariablesPerClause, int numberVariables)
    {
		this.numberClauses=numberClauses;
		this.numberVariablesPerClause=numberVariablesPerClause;
		this.numberVariables=numberVariables;
		
		if(numberClauses*numberVariablesPerClause<numberVariables)
		{
		    System.out.println("Warning: numberClauses*numberVariablesPerClause<numberVariable");
		}
    }

    @Override
    public SAT generateSAT() 
    {
		List<Variable> variables=new ArrayList<>();
		for(int varInd=0; varInd<numberVariables; varInd++)
		{
		    variables.add(new Variable());
		}
		
		//create clauses
		List<Clause> clauses=new ArrayList<>();
		for(int clauseInd=0; clauseInd<numberClauses; clauseInd++)
		{
		    clauses.add(new Clause(new ArrayList<>(), new ArrayList<>()));
		}
		
		//assign all variables
		for(Variable variable: variables)
		{
		    int clauseNumber=(int)(Math.random()*clauses.size());
		    while(clauses.get(clauseNumber).variables.size()==numberVariablesPerClause)
		    {
			clauseNumber=(int)(Math.random()*clauses.size());
		    }
		    clauses.get(clauseNumber).variables.add(variable);
		    clauses.get(clauseNumber).nots.add((int)Math.round(Math.random()));
		}
		
		//assign all variables
		for(Clause clause: clauses)
		{
		    while(clause.variables.size()<numberVariablesPerClause)
		    {
	    	    	int varNumber=(int)(Math.random()*variables.size());
	    	    	clause.variables.add(variables.get(varNumber));
	    	    	clause.nots.add((int)Math.round(Math.random()));
		    }
		}
		
		return new SAT(clauses, variables);
    }

	@Override
	public int getNumberVariables() 
	{
		return numberVariables;
	}

	@Override
	public int getNumberClauses() 
	{
		return numberClauses;
	}
    
}
