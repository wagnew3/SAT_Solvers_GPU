package SATProblemGeneration;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import SATProblem.Clause;
import SATProblem.SAT;
import SATProblem.Variable;

public class RandomPseudoIndustrialSAT extends SATProblemGenerator
{

	protected int numberClauses; 
	protected int numberVariables;
	protected int numberCommunities;
	protected int clauseLength;
	protected double inCommunityChance;
	
	//Q>=0.7, c in (10, 100), P=inCommunityChance+1/numberCommunities, clauseLength=3
	public RandomPseudoIndustrialSAT(int numberClauses, int numberVariables, 
			int clauseLength, int numberCommunities, double q)
	{
		this.numberClauses=numberClauses;
		if(numberVariables%numberCommunities!=0)
		{
			System.out.println("RandomPseudoIndustrialSAT Error: numberVariables%numberCommunities!=0");
		}
		this.numberVariables=numberVariables;
		this.numberCommunities=numberCommunities;
		this.clauseLength=clauseLength;
		inCommunityChance=q+1.0/numberCommunities;
	}
	
	@Override
	public SAT generateSAT() 
	{
		List<Variable> variables=new ArrayList<>();
		for(int variableInd=0; variableInd<numberVariables; variableInd++)
		{
			variables.add(new Variable());
		}
		
		List<Clause> clauses=new ArrayList<>();
		
		List<Variable> variablesCopy=copyList(variables);
		List<List<Variable>> communities=new ArrayList<>();
		for(int communityInd=0; communityInd<numberCommunities; communityInd++)
		{
			communities.add(new ArrayList<Variable>());
			for(int communityVariableInd=0; communityVariableInd<numberVariables/numberCommunities; communityVariableInd++)
			{
				communities.get(communityInd).add(variablesCopy.remove((int)(Math.random()*variablesCopy.size())));
			}
		}
		
		for(int clauseInd=0; clauseInd<numberClauses; clauseInd++)
		{
			List<Variable> clauseVariables=new ArrayList<>();
			
			if(Math.random()<=inCommunityChance)
			{
				int communityInd=(int)(Math.random()*communities.size());
				List<Variable> communityVariablesCopy=copyList(communities.get(communityInd));
				for(int variableInd=0; variableInd<clauseLength; variableInd++)
				{
					clauseVariables.add(communityVariablesCopy.remove((int)(Math.random()*communityVariablesCopy.size())));
				}
			}
			else
			{
				HashMap<List<Variable>, List<Variable>> choosenCommunities=new HashMap<>();
				int addedVars=0;
				while(addedVars<clauseLength)
				{
					int communityInd=(int)(Math.random()*communities.size());
					if(choosenCommunities.get(communities.get(communityInd))==null)
					{
						clauseVariables.add(communities.get(communityInd).get((int)(Math.random()*communities.get(communityInd).size())));
						choosenCommunities.put(communities.get(communityInd), communities.get(communityInd));
						addedVars++;
					}
				}
			}
			
			List<Integer> nots=new ArrayList<>();
			for(int notInd=0; notInd<clauseVariables.size(); notInd++)
			{
				if(Math.random()>=0.5)
				{
					nots.add(1);
				}
				else
				{
					nots.add(0);
				}
			}
			clauses.add(new Clause(clauseVariables, nots));
		}
		
		SAT sat=new SAT(clauses, variables);
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
	
	public <T> List<T> copyList(List<T> toCopy)
	{
		List<T> copied=new ArrayList<>();
		for(T t: toCopy)
		{
			copied.add(t);
		}
		return copied;
	}

}
