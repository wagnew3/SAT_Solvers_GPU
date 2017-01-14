/*******************************************************************************
 * SAT4J: a SATisfiability library for Java Copyright (C) 2004-2008 Daniel Le Berre
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU Lesser General Public License Version 2.1 or later (the
 * "LGPL"), in which case the provisions of the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of the LGPL, and not to allow others to use your version of
 * this file under the terms of the EPL, indicate your decision by deleting
 * the provisions above and replace them with the notice and other provisions
 * required by the LGPL. If you do not delete the provisions above, a recipient
 * may use your version of this file under the terms of the EPL or the LGPL.
 * 
 * Based on the original MiniSat specification from:
 * 
 * An extensible SAT solver. Niklas Een and Niklas Sorensson. Proceedings of the
 * Sixth International Conference on Theory and Applications of Satisfiability
 * Testing, LNCS 2919, pp 502-518, 2003.
 *
 * See www.minisat.se for the original solver in C++.
 * 
 *******************************************************************************/
package org.sat4j.minisat.orders;

import static org.sat4j.core.LiteralsUtils.toDimacs;
import static org.sat4j.core.LiteralsUtils.var;

import java.io.PrintWriter;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.sat4j.core.LiteralsUtils;
import org.sat4j.minisat.constraints.cnf.Lits;
import org.sat4j.minisat.core.Heap;
import org.sat4j.minisat.core.ILits;
import org.sat4j.minisat.core.IOrder;
import org.sat4j.minisat.core.IPhaseSelectionStrategy;
import org.sat4j.minisat.core.MLSolver;
import org.sat4j.minisat.core.Solver;
import org.sat4j.specs.Constr;
import org.sat4j.specs.IVec;

import MLSAT.MLSAT;
import MLSAT.MLSATSAT4J;
import SATProblem.SAT;
import SATSolver.SATSolverSAT4J;
import nDimensionalMatrices.FDMatrix;
import nDimensionalMatrices.Matrix;
import nDimensionalMatrices.SparseFMatrix;

/*
 * Created on 16 oct. 2003
 */

/**
 * @author leberre Heuristique du prouveur. Changement par rapport au MiniSAT
 *         original : la gestion activity est faite ici et non plus dans Solver.
 */
public class MLVarOrderHeap implements IOrder, Serializable {

	private static final long serialVersionUID = 1L;

	private static final double VAR_RESCALE_FACTOR = 1e-100;

	private static final double VAR_RESCALE_BOUND = 1 / VAR_RESCALE_FACTOR;

	/**
	 * mesure heuristique de l'activite d'une variable.
	 */
	protected double[] activity = new double[1];

	private double varDecay = 1.0;

	/**
	 * increment pour l'activite des variables.
	 */
	private double varInc = 1.0;

	protected ILits lits;

	private long nullchoice = 0;

	protected Heap heap;

	public IPhaseSelectionStrategy phaseStrategy;
	
	protected SATSolverSAT4J mlSAT;
	
	protected IVec<Constr> constrs;
	
	public int numberContrs;
	
	protected int numberVars;

	public MLVarOrderHeap(SATSolverSAT4J mlSAT, IVec<Constr> constrs, int numberVariables)
	{
		this(new PhaseInLastLearnedClauseSelectionStrategy(), mlSAT, constrs, numberVariables);
	}

	public MLVarOrderHeap(IPhaseSelectionStrategy strategy, SATSolverSAT4J mlSAT, IVec<Constr> constrs, int numberVariables) 
	{
		this.phaseStrategy = strategy;
		this.mlSAT=mlSAT;
		this.constrs=constrs;
		this.numberVars=numberVariables;
		numberContrs=constrs.size();
	}

	/**
     * Change the selection strategy.
     * 
     * @param strategy
     */
    public void setPhaseSelectionStrategy(IPhaseSelectionStrategy strategy) {
        this.phaseStrategy = strategy;
    }

    public IPhaseSelectionStrategy getPhaseSelectionStrategy() {
        return this.phaseStrategy;
    }

    public void setLits(ILits lits) {
        this.lits = lits;
    }
	
	protected static final int selectsBetweenUpdates=1; //must be even for completeness
	protected int selects;
	protected List<VariableActivation> variables;
	
	public void reset()
	{
		selects=0;
		variables=null;
	}
	
	
	public int select() 
	{
		//correct=selectCorrect();
		if(selects%selectsBetweenUpdates==0)
		{
			updateVarHeap();
		}
		selects++;
		
		int assignInd=0;
		int internalLit=-1;
		float maxActivation=-1;
		int startConsiderInd=0;
		while(!variables.isEmpty()
				&& assignInd<variables.size()
				&& (maxActivation==-1 || variables.get(assignInd).activation==maxActivation)) 
		{
			VariableActivation varActi=variables.get(assignInd);
			internalLit=LiteralsUtils.toInternal(varActi.dimacsVariable);
			if(lits.isUnassigned(internalLit)
					&& maxActivation==-1
					&& (internalLit<=1 || ((MLSolver)mlSAT.getSolver()).voc.watches(internalLit)!=null))
			{
				startConsiderInd=assignInd;
				maxActivation=(float)varActi.activation;
			}
			assignInd++;
		}
		
		int varInd=startConsiderInd+(int)Math.floor(Math.random()*(assignInd-startConsiderInd));
		internalLit=this.phaseStrategy.select(variables.get(varInd).dimacsVariable);
		
		if(assignInd==variables.size())
		{
			return ILits.UNDEFINED;
		}
		
		if(correct!=internalLit)
		{
			int correctInd=Math.abs(toDimacs(correct))-1;
			int internalInd=Math.abs(toDimacs(internalLit))-1;
			int u=0;
		}
		
		/*
		if(internalLit==selectVSIDS())
		{
			mlSAT.vsidsPoints.add(new int[]{(int)((Solver)mlSAT.getSolver()).getStats().decisions,((Solver)mlSAT.getSolver()).decisionLevel()});
		}
		else if(internalLit==selectDLIS())
		{
			mlSAT.dlisPoints.add(new int[]{(int)((Solver)mlSAT.getSolver()).getStats().decisions,((Solver)mlSAT.getSolver()).decisionLevel()});
		}
		else
		{
			mlSAT.nonePoints.add(new int[]{(int)((Solver)mlSAT.getSolver()).getStats().decisions,((Solver)mlSAT.getSolver()).decisionLevel()});
		}
		*/
		
		return internalLit;
	}
	
	int correct;

	public int selectVSIDS() {
		
        while (!this.heap.empty()) {
            int var = this.heap.getmin();
            int next = this.phaseStrategy.select(var);
            if (this.lits.isUnassigned(next)) 
            {
                if (this.activity[var] < 0.0001) 
                {
                    this.nullchoice++;
                }
                else
                {
                	return next;
                }
            }
        }
        return ILits.UNDEFINED;
    }
	
	public int selectDLIS() 
	{
        int bestValue=Integer.MIN_VALUE;
        int bestVar=0;
        
        for(int varInd=1; varInd<activity.length; varInd++)
        {
        	if(lits.isUnassigned(phaseStrategy.select(varInd)))
        	{
            	int numClausesSat//=(int)Math.floor(Math.random()*100);
            	=MLSATSAT4J.getSatisfiedChange(varInd, ((RSATPhaseSelectionStrategy)phaseStrategy).phase, 
            			((Solver)mlSAT.getSolver()).constrs, ((Solver)mlSAT.getSolver()).learnts, (Lits)lits);
            	if(numClausesSat>bestValue)
            	{
            		bestValue=numClausesSat;
            		bestVar=varInd;
            	}
        	}
        }
        
        if(bestVar!=0)
        {
        	return phaseStrategy.select(bestVar);
        }
        else
        {
        	return ILits.UNDEFINED;
        }
    }

	/*
	public int select() {
		
        while (!this.heap.empty()) {
            int var = this.heap.getmin();
            int next = this.phaseStrategy.select(var);
            if (this.lits.isUnassigned(next)) 
            {
                if (this.activity[var] < 0.0001) 
                {
                    this.nullchoice++;
                }
                else
                {
                	return next;
                }
            }
        }
        
        int bestValue=Integer.MIN_VALUE;
        int bestVar=0;
        
        for(int varInd=1; varInd<activity.length; varInd++)
        {
        	if(lits.isUnassigned(phaseStrategy.select(varInd)))
        	{
            	int numClausesSat//=(int)Math.floor(Math.random()*100);
            	=MLSATSAT4J.getSatisfiedChange(varInd, ((RSATPhaseSelectionStrategy)phaseStrategy).phase, 
            			((Solver)mlSAT.getSolver()).constrs, ((Solver)mlSAT.getSolver()).learnts, (Lits)lits);
            	if(numClausesSat>bestValue)
            	{
            		bestValue=numClausesSat;
            		bestVar=varInd;
            	}
        	}
        }
        
        if(bestVar!=0)
        {
        	return phaseStrategy.select(bestVar);
        }
        else
        {
        	return ILits.UNDEFINED;
        }
    }
	*/
	Matrix[] lInput;
	Matrix lOutput;
	
	protected void updateVarHeap()
	{
		Matrix[] input=null;
		/*
		if(mlSAT.alg==0)
		{
			List<Float> nonZeroValues=new ArrayList<>();
			List<Integer> nonZeroValuesRowInds=new ArrayList<>();
			List<Integer> nonZeroValuesColInds=new ArrayList<>();
			for(int clauseIndex=0; clauseIndex<constrs.size(); clauseIndex++)
			{
				boolean unsat=true;
				for(int variableIndex=0; variableIndex<constrs.get(clauseIndex).size(); variableIndex++)
				{
					if(lits.isSatisfied(constrs.get(clauseIndex).get(variableIndex)))
					{
						unsat=false;
						break;
					}
				}
				if(unsat)
				{
					for(int variableIndex=0; variableIndex<constrs.get(clauseIndex).size(); variableIndex++)
					{
						if(lits.isUnassigned(constrs.get(clauseIndex).get(variableIndex)))
						{
							int dimacs=LiteralsUtils.toDimacs(constrs.get(clauseIndex).get(variableIndex));
							if(dimacs<0)
							{
								nonZeroValues.add(-1.0f);
								nonZeroValuesRowInds.add(clauseIndex);
								nonZeroValuesColInds.add(Math.abs(dimacs+1));
							}
							else if(dimacs>0)
							{
								nonZeroValues.add(1.0f);
								nonZeroValuesRowInds.add(clauseIndex);
								nonZeroValuesColInds.add(dimacs-1);
							}
							else
							{
								System.out.println("MLVarOrder Error! Dimacs==0");
							}
						}
					}
				}
			}
			
			float[] nonZeroValuesArray=new float[nonZeroValues.size()];
			int[] nonZeroValuesRowIndsArray=new int[nonZeroValuesRowInds.size()];
			int[] nonZeroValuesColIndsArray=new int[nonZeroValuesRowInds.size()];
			for(int arrayInd=0; arrayInd<nonZeroValuesArray.length; arrayInd++)
			{
				nonZeroValuesArray[arrayInd]=nonZeroValues.get(arrayInd);
				nonZeroValuesRowIndsArray[arrayInd]=nonZeroValuesRowInds.get(arrayInd);
				nonZeroValuesColIndsArray[arrayInd]=nonZeroValuesColInds.get(arrayInd);
			}
			
			input=new Matrix[]{new SparseFMatrix(nonZeroValuesArray, nonZeroValuesRowIndsArray, 
					nonZeroValuesColIndsArray, numberContrs, numberVars)};
		}
		else if(mlSAT.alg==1
				|| mlSAT.alg==2)
		{
			float[][] floatActis=new float[activity.length-1][1];
			for(int varInd=1; varInd<activity.length; varInd++)
			{
				floatActis[varInd-1][0]=(float)Math.log10(activity[varInd]+1.0);
				if(activity[varInd]!=0.0)
				{
					int u=0;
				}
			}
			
			input=new Matrix[]{mlSAT.scaleFilterInputs.scaleData(new Matrix[]{new FDMatrix(floatActis)})[0]};
		}
		else if(mlSAT.alg==3)
		{
			float[][] floatActis=new float[2*(activity.length-1)][1];
			for(int varInd=1; varInd<activity.length; varInd++)
			{
				floatActis[varInd-1][0]=(float)Math.log10(activity[varInd]+1.0);
				if(activity[varInd]!=0.0)
				{
					int u=0;
				}
			}
			
			for(int varInd=1; varInd<activity.length; varInd++)
			{
				if(lits.isUnassigned(LiteralsUtils.toInternal(varInd)))
				{
					floatActis[varInd-1+activity.length-1][0]=getVarFrequency(varInd, ((Solver)mlSAT.getSolver()).constrs, ((Solver)mlSAT.getSolver()).learnts);
				}
			}
			
			input=new Matrix[]{mlSAT.scaleFilterInputs.scaleData(new Matrix[]{new FDMatrix(floatActis)})[0]};
		}
		else if(mlSAT.alg==4)
		{
			float[][] floatActis=new float[2*(activity.length-1)][1];
			for(int varInd=1; varInd<activity.length; varInd++)
			{
				if(lits.isUnassigned(LiteralsUtils.toInternal(varInd)))
				{
					floatActis[varInd-1][0]=(float)Math.log10(activity[varInd]+1.0);
				}
			}
			
			for(int varInd=1; varInd<activity.length; varInd++)
			{
				if(lits.isUnassigned(LiteralsUtils.toInternal(varInd)))
				{
					floatActis[varInd-1+activity.length-1][0]=MLSATSAT4J.getSatisfiedChange(varInd, ((RSATPhaseSelectionStrategy)phaseStrategy).phase, 
							((Solver)mlSAT.getSolver()).constrs, ((Solver)mlSAT.getSolver()).learnts, (Lits)lits);
				}
			}
			
			input=new Matrix[]{mlSAT.scaleFilterInputs.scaleData(new Matrix[]{new FDMatrix(floatActis)})[0]};
		}
		else if(mlSAT.alg==5)
		{
			float[][] floatActis=new float[(activity.length-1)][1];
			
			int unassigned=0;
			float totalActi=0.0f;
			for(int varInd=1; varInd<activity.length; varInd++)
			{
				if(lits.isUnassigned(LiteralsUtils.toInternal(varInd)))
				{
					floatActis[varInd-1][0]=5.0f*(float)Math.pow(Math.log10(activity[varInd]+1.0), 0.25);
					totalActi+=floatActis[varInd-1][0];
					unassigned++;
				}
			}
			
			float[][] floatClauses=new float[(activity.length-1)][1];
			for(int varInd=1; varInd<activity.length; varInd++)
			{
				if(lits.isUnassigned(LiteralsUtils.toInternal(varInd)))
				{
					floatClauses[varInd-1][0]=MLSATSAT4J.getSatisfiedChange(varInd, ((RSATPhaseSelectionStrategy)phaseStrategy).phase, 
							((Solver)mlSAT.getSolver()).constrs, ((Solver)mlSAT.getSolver()).learnts, (Lits)lits);
				}
			}
			
			if(totalActi>0.0f)
			{
				int u=0;
			}
			
			float[][] additionalInfo=new float[2][1];
			additionalInfo[0][0]=((Solver)mlSAT.getSolver()).learnts.size();
			additionalInfo[1][0]=unassigned;
			
			input=mlSAT.scaleFilterInputs.scaleData(new Matrix[]{
					new FDMatrix(floatActis), new FDMatrix(additionalInfo), new FDMatrix(floatClauses)});
		}
		else if(mlSAT.alg==6)
		{
			float[][] floatActis=new float[2*(activity.length-1)+2][1];
			
			int unassigned=0;
			for(int varInd=1; varInd<activity.length; varInd++)
			{
				if(lits.isUnassigned(LiteralsUtils.toInternal(varInd)))
				{
					floatActis[varInd-1][0]=(float)Math.log10(activity[varInd]+1.0)/60.0f;
					unassigned++;
				}
			}
			for(int varInd=1; varInd<activity.length; varInd++)
			{
				if(lits.isUnassigned(LiteralsUtils.toInternal(varInd)))
				{
					floatActis[varInd-1+activity.length-1][0]=MLSATSAT4J.getSatisfiedChange(varInd, ((RSATPhaseSelectionStrategy)phaseStrategy).phase, 
							((Solver)mlSAT.getSolver()).constrs, ((Solver)mlSAT.getSolver()).learnts, (Lits)lits);
				}
			}
			
			floatActis[floatActis.length-2][0]=((Solver)mlSAT.getSolver()).learnts.size()/250.0f;
			floatActis[floatActis.length-1][0]=unassigned/100.0f;
			input=new Matrix[]{mlSAT.scaleFilterInputs.scaleData(new Matrix[]{new FDMatrix(floatActis)})[0]};
		}
		else if(mlSAT.alg==7)
		{
			float[][] floatActis=new float[(activity.length-1)][1];
			
			int unassigned=0;
			float totalActi=0.0f;
			for(int varInd=1; varInd<activity.length; varInd++)
			{
				if(lits.isUnassigned(LiteralsUtils.toInternal(varInd)))
				{
					floatActis[varInd-1][0]=5.0f*(float)Math.pow(Math.log10(activity[varInd]+1.0), 0.25);
					totalActi+=floatActis[varInd-1][0];
					unassigned++;
				}
			}
			
			float[][] floatClauses=new float[(activity.length-1)][1];
			for(int varInd=1; varInd<activity.length; varInd++)
			{
				if(lits.isUnassigned(LiteralsUtils.toInternal(varInd)))
				{
					floatClauses[varInd-1][0]=MLSATSAT4J.getSatisfiedChange(varInd, ((RSATPhaseSelectionStrategy)phaseStrategy).phase, 
							((Solver)mlSAT.getSolver()).constrs, ((Solver)mlSAT.getSolver()).learnts, (Lits)lits);
				}
			}
			
			float[][] floatAddInfo=new float[1][1];
			if(totalActi>0.0f)
			{
				floatAddInfo[0][0]=1.0f;
			}
			
			input=mlSAT.scaleFilterInputs.scaleData(new Matrix[]{
					new FDMatrix(floatActis), new FDMatrix(floatAddInfo), new FDMatrix(floatClauses)});
		}
		else if(mlSAT.alg==8)
		{
			float[][] additionalInfo=new float[4+activity.length-1][1];
			
			float unsatInitialClauses=0;
			float unassignedInitialClausesVars=0;
			for(int initialClauseInd=0; initialClauseInd<((Solver)mlSAT.getSolver()).constrs.size(); initialClauseInd++)
			{
				boolean clauseSat=false;
				float unassignedThisClause=0;
				for(int varInd=0; varInd<((Constr)((Solver)mlSAT.getSolver()).constrs.get(initialClauseInd)).size(); varInd++)
				{
					if(((Lits)lits).isSatisfied(((Constr)((Solver)mlSAT.getSolver()).constrs.get(initialClauseInd)).get(varInd)))
					{
						clauseSat=true;
						break;
					}
					if(((Lits)lits).isUnassigned(((Constr)((Solver)mlSAT.getSolver()).constrs.get(initialClauseInd)).get(varInd)))
					{
						unassignedThisClause++;
					}
				}
				if(!clauseSat)
				{
					unsatInitialClauses++;
					unassignedInitialClausesVars+=unassignedThisClause;
					for(int varInd=0; varInd<((Constr)((Solver)mlSAT.getSolver()).constrs.get(initialClauseInd)).size(); varInd++)
					{
						if(((Lits)lits).isUnassigned(((Constr)((Solver)mlSAT.getSolver()).constrs.get(initialClauseInd)).get(varInd)))
						{
							additionalInfo[4+Math.abs(LiteralsUtils.toDimacs(((Constr)((Solver)mlSAT.getSolver()).constrs.get(initialClauseInd)).get(varInd)))-1][0]++;
						}
					}
				}
			}
			
			float unsatConflictClauses=0;
			float unassignedConflictClausesVars=0;
			for(int initialClauseInd=0; initialClauseInd<((Solver)mlSAT.getSolver()).learnts.size(); initialClauseInd++)
			{
				boolean clauseSat=false;
				float unassignedThisClause=0;
				for(int varInd=0; varInd<((Constr)((Solver)mlSAT.getSolver()).learnts.get(initialClauseInd)).size(); varInd++)
				{
					if(((Lits)lits).isSatisfied(((Constr)((Solver)mlSAT.getSolver()).learnts.get(initialClauseInd)).get(varInd)))
					{
						clauseSat=true;
						break;
					}
					if(((Lits)lits).isUnassigned(((Constr)((Solver)mlSAT.getSolver()).learnts.get(initialClauseInd)).get(varInd)))
					{
						unassignedThisClause++;
					}
				}
				if(!clauseSat)
				{
					unsatConflictClauses++;
					unassignedConflictClausesVars+=unassignedThisClause;
					for(int varInd=0; varInd<((Constr)((Solver)mlSAT.getSolver()).learnts.get(initialClauseInd)).size(); varInd++)
					{
						if(((Lits)lits).isUnassigned(((Constr)((Solver)mlSAT.getSolver()).learnts.get(initialClauseInd)).get(varInd)))
						{
							additionalInfo[4+Math.abs(LiteralsUtils.toDimacs(((Constr)((Solver)mlSAT.getSolver()).learnts.get(initialClauseInd)).get(varInd)))-1][0]++;
						}
					}
				}
			}
			
			additionalInfo[0][0]=unsatInitialClauses/((Solver)mlSAT.getSolver()).constrs.size();
			additionalInfo[1][0]=unassignedInitialClausesVars/(activity.length-1);
			additionalInfo[2][0]=unsatConflictClauses/((Solver)mlSAT.getSolver()).constrs.size();
			additionalInfo[3][0]=unassignedConflictClausesVars/(activity.length-1);
			
			float[][] floatActis=new float[(activity.length-1)][1];
			
			int unassigned=0;
			float totalActi=0.0f;
			for(int varInd=1; varInd<activity.length; varInd++)
			{
				if(lits.isUnassigned(LiteralsUtils.toInternal(varInd)))
				{
					floatActis[varInd-1][0]=5.0f*(float)Math.pow(Math.log10(activity[varInd]+1.0), 0.25);
					totalActi+=floatActis[varInd-1][0];
					unassigned++;
				}
			}
			
			float[][] floatClauses=new float[(activity.length-1)][1];
			for(int varInd=1; varInd<activity.length; varInd++)
			{
				if(lits.isUnassigned(LiteralsUtils.toInternal(varInd)))
				{
					floatClauses[varInd-1][0]=MLSATSAT4J.getSatisfiedChange(varInd, ((RSATPhaseSelectionStrategy)phaseStrategy).phase, 
							((Solver)mlSAT.getSolver()).constrs, ((Solver)mlSAT.getSolver()).learnts, ((Lits)lits));
				}
			}
			
			input=mlSAT.scaleFilterInputs.scaleData(new Matrix[]{
					new FDMatrix(floatActis), new FDMatrix(additionalInfo), new FDMatrix(floatClauses)});
		}
		else */if(mlSAT.alg==9)
		{
			int numberVariablesToInclude=(int)Math.round((activity.length-1)*MLSATSAT4J.fractionVariablesToInclude);
			
			List<VariableActivation> actisVarList=new ArrayList<>();
			List<VariableActivation> clausesVarList=new ArrayList<>();
			for(int varInd=1; varInd<activity.length; varInd++)
			{
				if(lits.isUnassigned(LiteralsUtils.toInternal(varInd)))
				{
					actisVarList.add(new VariableActivation(varInd, 5.0f*(float)Math.pow(Math.log10(activity[varInd]+1.0), 0.25)));
				}
				
				if(lits.isUnassigned(LiteralsUtils.toInternal(varInd)))
				{
					clausesVarList.add(new VariableActivation(varInd, MLSATSAT4J.getSatisfiedChange(varInd, ((RSATPhaseSelectionStrategy)phaseStrategy).phase, 
							((Solver)mlSAT.getSolver()).constrs, ((Solver)mlSAT.getSolver()).learnts, ((Lits)lits))));
				}
			}
			
			float[][] inputFloatActis=new float[numberVariablesToInclude][1];
			float[][] inputFloatClauses=new float[numberVariablesToInclude][1];
			Collections.sort(actisVarList);
			Collections.sort(clausesVarList);
			List<Integer> includedHeuristicVariables=new ArrayList<>();
			int turn=0;
			for(int inputInd=0; inputInd<numberVariablesToInclude; inputInd++)
			{
				if(turn%2==0 && actisVarList.size()>turn/2)
				{
					inputFloatActis[inputInd][0]=(float)actisVarList.get(turn/2).activation;
					inputFloatClauses[inputInd][0]=(float)getVal(actisVarList.get(turn/2).dimacsVariable, clausesVarList);
					includedHeuristicVariables.add(actisVarList.get(turn/2).dimacsVariable);
				}
				else if(turn%2==1 && clausesVarList.size()>turn/2)
				{
					inputFloatActis[inputInd][0]=(float)getVal(clausesVarList.get(turn/2).dimacsVariable, actisVarList);
					inputFloatClauses[inputInd][0]=(float)clausesVarList.get(turn/2).activation;
					includedHeuristicVariables.add(clausesVarList.get(turn/2).dimacsVariable);
				}
				turn++;
			}
			
			float[][] floatActis=new float[(activity.length-1)][1];
			
			for(int varInd=1; varInd<activity.length; varInd++)
			{
				if(lits.isUnassigned(LiteralsUtils.toInternal(varInd)))
				{
					floatActis[varInd-1][0]=5.0f*(float)Math.pow(Math.log10(activity[varInd]+1.0), 0.25);
				}
			}
			
			float[][] floatClauses=new float[(activity.length-1)][1];
			for(int varInd=1; varInd<activity.length; varInd++)
			{
				if(lits.isUnassigned(LiteralsUtils.toInternal(varInd)))
				{
					floatClauses[varInd-1][0]=MLSATSAT4J.getSatisfiedChange(varInd, ((RSATPhaseSelectionStrategy)phaseStrategy).phase, 
							((Solver)mlSAT.getSolver()).constrs, ((Solver)mlSAT.getSolver()).learnts, ((Lits)lits));
				}
			}
			
			float[][] additionalInfo=new float[4+numberVariablesToInclude][1];	
			float unsatInitialClauses=0;
			float unassignedInitialClausesVars=0;
			for(int initialClauseInd=0; initialClauseInd<((Solver)mlSAT.getSolver()).constrs.size(); initialClauseInd++)
			{
				boolean clauseSat=false;
				float unassignedThisClause=0;
				for(int varInd=0; varInd<((Constr)((Solver)mlSAT.getSolver()).constrs.get(initialClauseInd)).size(); varInd++)
				{
					if(((Lits)lits).isSatisfied(((Constr)((Solver)mlSAT.getSolver()).constrs.get(initialClauseInd)).get(varInd)))
					{
						clauseSat=true;
						break;
					}
					if(((Lits)lits).isUnassigned(((Constr)((Solver)mlSAT.getSolver()).constrs.get(initialClauseInd)).get(varInd)))
					{
						unassignedThisClause++;
					}
				}
				if(!clauseSat)
				{
					unsatInitialClauses++;
					unassignedInitialClausesVars+=unassignedThisClause;
					for(int varInd=0; varInd<((Constr)((Solver)mlSAT.getSolver()).constrs.get(initialClauseInd)).size(); varInd++)
					{
						if(((Lits)lits).isUnassigned(((Constr)((Solver)mlSAT.getSolver()).constrs.get(initialClauseInd)).get(varInd))
								&& includedHeuristicVariables.contains(Math.abs(LiteralsUtils.toDimacs(((Constr)((Solver)mlSAT.getSolver()).constrs.get(initialClauseInd)).get(varInd)))))
						{
							additionalInfo[4+includedHeuristicVariables.indexOf(Math.abs(LiteralsUtils.toDimacs(((Constr)((Solver)mlSAT.getSolver()).constrs.get(initialClauseInd)).get(varInd))))][0]++;
						}
					}
				}
			}
			float unsatConflictClauses=0;
			float unassignedConflictClausesVars=0;
			for(int initialClauseInd=0; initialClauseInd<((Solver)mlSAT.getSolver()).learnts.size(); initialClauseInd++)
			{
				boolean clauseSat=false;
				float unassignedThisClause=0;
				for(int varInd=0; varInd<((Constr)((Solver)mlSAT.getSolver()).learnts.get(initialClauseInd)).size(); varInd++)
				{
					if(((Lits)lits).isSatisfied(((Constr)((Solver)mlSAT.getSolver()).learnts.get(initialClauseInd)).get(varInd)))
					{
						clauseSat=true;
						break;
					}
					if(((Lits)lits).isUnassigned(((Constr)((Solver)mlSAT.getSolver()).learnts.get(initialClauseInd)).get(varInd)))
					{
						unassignedThisClause++;
					}
				}
				if(!clauseSat)
				{
					unsatConflictClauses++;
					unassignedConflictClausesVars+=unassignedThisClause;
					for(int varInd=0; varInd<((Constr)((Solver)mlSAT.getSolver()).learnts.get(initialClauseInd)).size(); varInd++)
					{
						if(((Lits)lits).isUnassigned(((Constr)((Solver)mlSAT.getSolver()).learnts.get(initialClauseInd)).get(varInd))
								&& includedHeuristicVariables.contains(Math.abs(LiteralsUtils.toDimacs(((Constr)((Solver)mlSAT.getSolver()).learnts.get(initialClauseInd)).get(varInd)))))
						{
							additionalInfo[4+includedHeuristicVariables.indexOf(Math.abs(LiteralsUtils.toDimacs(((Constr)((Solver)mlSAT.getSolver()).learnts.get(initialClauseInd)).get(varInd))))][0]++;
						}
					}
				}
			}
			additionalInfo[0][0]=unsatInitialClauses/((Solver)mlSAT.getSolver()).constrs.size();
			additionalInfo[1][0]=unassignedInitialClausesVars/(activity.length-1);
			additionalInfo[2][0]=unsatConflictClauses/((Solver)mlSAT.getSolver()).constrs.size();
			additionalInfo[3][0]=unassignedConflictClausesVars/(activity.length-1);
			
			//input=mlSAT.scaleFilterInputs.scaleData(new Matrix[]{
			//		new FDMatrix(inputFloatActis), new FDMatrix(additionalInfo), new FDMatrix(inputFloatClauses)});
			FDMatrix output=null;//=(FDMatrix)(mlSAT.network.getOutput(input)[0]);
			
			lInput=input;
			//lOutput=output;
					
			variables=new ArrayList<>();
			turn=0;
			for(int outputInd=0; outputInd<numberVariablesToInclude; outputInd++)
			{
				if(turn%2==0 && actisVarList.size()>turn/2)
				{
					variables.add(new VariableActivation(actisVarList.get(turn/2).dimacsVariable, 0.0f/*output.get(outputInd, 0)*/));
				}
				else if(turn%2==1 && clausesVarList.size()>turn/2)
				{
					variables.add(new VariableActivation(clausesVarList.get(turn/2).dimacsVariable, 0.0f/*output.get(outputInd, 0)*/));
				}
				turn++;
			}
			for(int outputInd=0; outputInd<output.getLen(); outputInd++)
			{
				if(getVal(outputInd+1, variables)==-0.01)
				{
					variables.add(new VariableActivation(outputInd+1, -0.01));
				}
			}
			
			Collections.sort(variables);
			return;
		}
		
		FDMatrix output=(FDMatrix)(mlSAT.network.getOutput(input)[0]);
		
		lInput=input;
		lOutput=output;
				
		if(variables==null)
		{
			variables=new ArrayList<>();
			for(int outputInd=0; outputInd<output.getLen(); outputInd++)
			{
				variables.add(new VariableActivation(outputInd+1, output.get(outputInd, 0)));
			}
		}
		else
		{
			List<VariableActivation> newVariables=new ArrayList<>();
			for(int outputInd=0; outputInd<output.getLen(); outputInd++)
			{
				newVariables.add(new VariableActivation(outputInd+1, output.get(outputInd, 0)));
			}
			variables=newVariables;
		}
		Collections.sort(variables);
	}
	
	public double getVal(int variable, List<VariableActivation> vars)
	{
		for(int ind=0; ind<vars.size(); ind++)
		{
			if(vars.get(ind).dimacsVariable==variable)
			{
				return vars.get(ind).activation;
			}
		}
		return -0.01;	
	}
	
	private int getVarFrequency(int dimacsVar, IVec<Constr> initialConstrs, IVec<Constr> learnedConstrs)
	{
		int frequency=0;
		for(int constrInd=0; constrInd<initialConstrs.size(); constrInd++)
		{
			for(int varInd=0; varInd<initialConstrs.get(constrInd).size(); varInd++)
			{
				if(Math.abs(toDimacs(initialConstrs.get(constrInd).get(varInd)))==dimacsVar)
				{
					frequency++;
				}
			}
		}
		
		for(int constrInd=0; constrInd<learnedConstrs.size(); constrInd++)
		{
			for(int varInd=0; varInd<learnedConstrs.get(constrInd).size(); varInd++)
			{
				if(Math.abs(toDimacs(learnedConstrs.get(constrInd).get(varInd)))==dimacsVar)
				{
					frequency++;
				}
			}
		}
		
		return frequency;
	}
	
	/**
     * Change la valeur de varDecay.
     * 
     * @param d
     *            la nouvelle valeur de varDecay
     */
    public void setVarDecay(double d) {
        this.varDecay = d;
    }

    /**
     * Methode appelee quand la variable x est desaffectee.
     * 
     * @param x
     */
    public void undo(int x) {
        if (!this.heap.inHeap(x)) {
            this.heap.insert(x);
        }
    }

    /**
     * Appelee lorsque l'activite de la variable x a change.
     * 
     * @param p
     *            a literal
     */
    public void updateVar(int p) {
        int var = var(p);
        updateActivity(var);
        this.phaseStrategy.updateVar(p);
        if (this.heap.inHeap(var)) {
            this.heap.increase(var);
        }
    }

    protected void updateActivity(final int var) {
        if ((this.activity[var] += this.varInc) > VAR_RESCALE_BOUND) {
            varRescaleActivity();
        }
    }

    /**
     * 
     */
    public void varDecayActivity() {
        this.varInc *= this.varDecay;
    }

    /**
     * 
     */
    private void varRescaleActivity() {
        for (int i = 1; i < this.activity.length; i++) {
            this.activity[i] *= VAR_RESCALE_FACTOR;
        }
        this.varInc *= VAR_RESCALE_FACTOR;
    }

    public double varActivity(int p) {
        return this.activity[var(p)];
    }

    /**
     * 
     */
    public int numberOfInterestingVariables() {
        int cpt = 0;
        for (int i = 1; i < this.activity.length; i++) {
            if (this.activity[i] > 1.0) {
                cpt++;
            }
        }
        return cpt;
    }

    protected Heap createHeap(double[] activity) {
        return new Heap(new ActivityBasedVariableComparator(activity));
    }

    /**
     * that method has the responsibility to initialize all arrays in the
     * heuristics. PLEASE CALL super.init() IF YOU OVERRIDE THAT METHOD.
     */
    public void init() {
        int nlength = this.lits.nVars() + 1;
        if (this.activity == null || this.activity.length < nlength) {
            this.activity = new double[nlength];
        }
        this.phaseStrategy.init(nlength);
        this.activity[0] = -1;
        this.heap = createHeap(this.activity);
        this.heap.setBounds(nlength);
        for (int i = 1; i < nlength; i++) {
            assert i > 0;
            assert i <= this.lits.nVars() : "" + this.lits.nVars() + "/" + i; //$NON-NLS-1$ //$NON-NLS-2$
            this.activity[i] = 0.0;
            if (this.lits.belongsToPool(i)) {
                this.heap.insert(i);
            }
        }
    }

    @Override
    public String toString() {
        return "VSIDS like heuristics from MiniSAT using a heap " + this.phaseStrategy; //$NON-NLS-1$
    }

    public ILits getVocabulary() {
        return this.lits;
    }

    public void printStat(PrintWriter out, String prefix) {
        out.println(prefix + "non guided choices\t" + this.nullchoice); //$NON-NLS-1$
    }

    public void assignLiteral(int p) {
        this.phaseStrategy.assignLiteral(p);
    }

    public void updateVarAtDecisionLevel(int q) {
        this.phaseStrategy.updateVarAtDecisionLevel(q);

    }

    public double[] getVariableHeuristics() {
        return this.activity;
    }

}

class VariableActivation implements Comparable<VariableActivation>
{
	
	public int dimacsVariable;
	public double activation;

	public VariableActivation(int dimacsVariable, double activation)
	{
		this.dimacsVariable=dimacsVariable;
		this.activation=activation;
	}
	
	@Override
	public int compareTo(VariableActivation o)
	{
		return (int)Math.signum(o.activation-activation);
	}
	
}
