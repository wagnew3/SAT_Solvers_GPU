package SATProblemGeneration;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import SATProblem.Clause;
import SATProblem.SAT;
import SATProblem.Variable;

public class RandomArgumentation extends SATProblemGenerator 
{
	
	protected int numberVariables;
	protected int numberClauses;
	
	public RandomArgumentation(int numberClauses, int numberVariables)
	{
		this.numberVariables=numberVariables;
		if(numberClauses%2!=0)
		{
			System.out.println("Random Argumentation Error: Number Clauses%2!=0");
		}
		this.numberClauses=numberClauses;
	}

	@Override
	public SAT generateSAT() 
	{
		int numberAttacks=numberClauses/2;
		List<Variable> varVector=new ArrayList<>();
		for(int rowInd=0; rowInd<numberVariables; rowInd++)
		{
			varVector.add(new Variable());
		}
		
		boolean[][] attackMatrix=new boolean[numberVariables][numberVariables];
		int numberAttacksSet=0;
		while(numberAttacksSet<numberAttacks)
		{
			int row=(int)(attackMatrix.length*Math.random());
			int col=(int)(attackMatrix[row].length*Math.random());
			if(row!=col && attackMatrix[row][col]==false)
			{
				attackMatrix[row][col]=true;
				numberAttacksSet++;
			}
		}
		
		List<Clause> clauses=new ArrayList<>();
		
		for(int rowInd=0; rowInd<attackMatrix.length; rowInd++)
		{
			for(int colInd=0; colInd<attackMatrix[rowInd].length; colInd++)
			{
				if(attackMatrix[rowInd][colInd])
				{
					List<Variable> variables=new ArrayList<>();
					variables.add(varVector.get(rowInd));
					variables.add(varVector.get(colInd));
					
					List<Integer> nots=new ArrayList<>();
					nots.add(1);
					nots.add(1);
					
					Clause clause=new Clause(variables, nots);
					clauses.add(clause);
				}
			}
		}
		
		for(int rowInd=0; rowInd<attackMatrix.length; rowInd++)
		{
			for(int colInd=0; colInd<attackMatrix[rowInd].length; colInd++)
			{
				if(attackMatrix[rowInd][colInd])
				{
					List<Variable> variables=new ArrayList<>();
					variables.add(varVector.get(colInd));
					
					List<Integer> nots=new ArrayList<>();
					nots.add(1);
					
					for(int rowIndAttack=0; rowIndAttack<attackMatrix.length; rowIndAttack++)
					{
						if(attackMatrix[rowIndAttack][rowInd])
						{
							variables.add(varVector.get(rowIndAttack));
							nots.add(0);
						}
					}
					
					Clause clause=new Clause(variables, nots);
					clauses.add(clause);
				}
			}
		}
		SAT sat=new SAT(clauses, varVector);
		return new SAT(clauses, varVector);
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
