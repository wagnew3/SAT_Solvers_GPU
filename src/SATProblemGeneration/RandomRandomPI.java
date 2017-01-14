package SATProblemGeneration;

import SATProblem.SAT;

public class RandomRandomPI extends SATProblemGenerator
{
	
	int ctr=0;
	SATProblemGenerator spgA;
	SATProblemGenerator spgB;
	
	
	public RandomRandomPI(SATProblemGenerator spgA, SATProblemGenerator spgB)
	{
		this.spgA=spgA;
		this.spgB=spgB;
	}

	@Override
	public SAT generateSAT() 
	{
		ctr++;
		ctr=0;
		if(ctr%2==0)
		{
			return spgA.generateSAT();
		}
		else
		{
			return spgB.generateSAT();
		}	
	}

	@Override
	public int getNumberVariables() 
	{
		return spgA.getNumberVariables();
	}

	@Override
	public int getNumberClauses() 
	{
		return spgA.getNumberClauses();
	}
	
	

}
