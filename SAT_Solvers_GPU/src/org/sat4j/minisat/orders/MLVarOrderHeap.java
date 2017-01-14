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

import static org.sat4j.core.LiteralsUtils.var;

import java.io.PrintWriter;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.sat4j.core.LiteralsUtils;
import org.sat4j.minisat.core.Constr;
import org.sat4j.minisat.core.Heap;
import org.sat4j.minisat.core.ILits;
import org.sat4j.minisat.core.IOrder;
import org.sat4j.minisat.core.IPhaseSelectionStrategy;
import org.sat4j.specs.IVec;

import MLSAT.MLSAT;
import MLSAT.MLSATSAT4J;
import SATProblem.SAT;
import nDimensionalMatrices.FDMatrix;
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

	protected IPhaseSelectionStrategy phaseStrategy;
	
	protected MLSATSAT4J mlSAT;
	
	protected IVec<Constr> constrs;
	
	protected int numberVars;

	public MLVarOrderHeap(MLSATSAT4J mlSAT, IVec<Constr> constrs, int numberVariables)
	{
		this(new PhaseInLastLearnedClauseSelectionStrategy(), mlSAT, constrs, numberVariables);
	}

	public MLVarOrderHeap(IPhaseSelectionStrategy strategy, MLSATSAT4J mlSAT, IVec<Constr> constrs, int numberVariables) 
	{
		this.phaseStrategy = strategy;
		this.mlSAT=mlSAT;
		this.constrs=constrs;
		this.numberVars=numberVariables;
	}

	/**
	 * Change the selection strategy.
	 * 
	 * @param strategy
	 */
	public void setPhaseSelectionStrategy(IPhaseSelectionStrategy strategy) {
		phaseStrategy = strategy;
	}

	public IPhaseSelectionStrategy getPhaseSelectionStrategy() {
		return phaseStrategy;
	}

	public void setLits(ILits lits) {
		this.lits = lits;
	}
	
	protected static final int selectsBetweenUpdates=1; //must be even for completeness
	protected int selects;
	protected List<VarActivation> variables;
	
	public void reset()
	{
		selects=0;
		variables=null;
	}
	
	public int select() 
	{
		if(selects%selectsBetweenUpdates==0)
		{
			updateVarHeap();
		}
		selects++;
		
		int assignInd=0;
		int internalLit=-1;
		while(!variables.isEmpty()) 
		{
			VarActivation varActi=variables.get(assignInd);
			if(varActi.activation<0.5)
			{
				internalLit=LiteralsUtils.toInternal(-varActi.var);
			}
			else
			{
				internalLit=LiteralsUtils.toInternal(varActi.var);
			}
			if(lits.isUnassigned(internalLit))
			{
				break;
			}
			if(varActi.activation<0.5)
			{
				internalLit=LiteralsUtils.toInternal(varActi.var);
			}
			else
			{
				internalLit=LiteralsUtils.toInternal(-varActi.var);
			}
			if(lits.isUnassigned(internalLit))
			{
				break;
			}
			assignInd++;
		}
		
		if(variables.isEmpty())
		{
			return ILits.UNDEFINED;
		}
		
		VarActivation varActi=variables.get(assignInd);
		return internalLit;
	}
	
	protected void updateVarHeap()
	{
		//SparseFMatrix input=SATToInputArrayRealVector(constrs, numberVars);
		
		SparseFMatrix input=mlSAT.SATToInputArrayRealVector(mlSAT.unitPropogation(mlSAT.toSAT(constrs, lits)));
		FDMatrix output=mlSAT.getOutput(input);
				
		if(variables==null)
		{
			variables=new ArrayList<>();
			for(int outputInd=0; outputInd<output.getLen(); outputInd++)
			{
				variables.add(new VarActivation(outputInd+1, output.get(outputInd, 0)));
			}
		}
		else
		{
			List<VarActivation> newVariables=new ArrayList<>();
			for(int outputInd=0; outputInd<output.getLen(); outputInd++)
			{
				newVariables.add(new VarActivation(outputInd+1, output.get(outputInd, 0)));
			}
			variables=newVariables;
		}
		Collections.sort(variables);
	}
	
	protected SparseFMatrix SATToInputArrayRealVector(IVec<Constr> constraints, int numberVariables)
	{
		//WRONG! not internal rep
		/*
		List<Float> nonZeroValues=new ArrayList<>();
		List<Integer> nonZeroValuesRowInds=new ArrayList<>();
		List<Integer> nonZeroValuesColInds=new ArrayList<>();
		for(int clauseIndex=0; clauseIndex<constraints.size(); clauseIndex++)
		{
			for(int variableIndex=0; variableIndex<constraints.get(clauseIndex).size(); variableIndex++)
			{
				int var=constraints.get(clauseIndex).get(variableIndex);
				if(var<0)
				{
					nonZeroValues.add(-1.0f);
				}
				else
				{
					nonZeroValues.add(1.0f);
				}
				nonZeroValuesRowInds.add(clauseIndex);
				nonZeroValuesColInds.add(variableIndex);
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
		
		return new SparseFMatrix(nonZeroValuesArray, nonZeroValuesRowIndsArray, nonZeroValuesColIndsArray, constraints.size(), numberVariables);
		*/
	}

	/**
	 * Change la valeur de varDecay.
	 * 
	 * @param d
	 *            la nouvelle valeur de varDecay
	 */
	public void setVarDecay(double d) {
		varDecay = d;
	}

	/**
	 * Methode appelee quand la variable x est desaffectee.
	 * 
	 * @param x
	 */
	public void undo(int x) {
		if (!heap.inHeap(x))
			heap.insert(x);
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
		phaseStrategy.updateVar(p);
		if (heap.inHeap(var))
			heap.increase(var);
	}

	protected void updateActivity(final int var) {
		if ((activity[var] += varInc) > VAR_RESCALE_BOUND) {
			varRescaleActivity();
		}
	}

	/**
     * 
     */
	public void varDecayActivity() {
		varInc *= varDecay;
	}

	/**
     * 
     */
	private void varRescaleActivity() {
		for (int i = 1; i < activity.length; i++) {
			activity[i] *= VAR_RESCALE_FACTOR;
		}
		varInc *= VAR_RESCALE_FACTOR;
	}

	public double varActivity(int p) {
		return activity[var(p)];
	}

	/**
     * 
     */
	public int numberOfInterestingVariables() {
		int cpt = 0;
		for (int i = 1; i < activity.length; i++) {
			if (activity[i] > 1.0) {
				cpt++;
			}
		}
		return cpt;
	}

	/**
	 * that method has the responsability to initialize all arrays in the
	 * heuristics. PLEASE CALL super.init() IF YOU OVERRIDE THAT METHOD.
	 */
	public void init() {
		int nlength = lits.nVars() + 1;
		if (activity == null || activity.length < nlength) {
			activity = new double[nlength];
		}
		phaseStrategy.init(nlength);
		activity[0] = -1;
		heap = new Heap(activity);
		heap.setBounds(nlength);
		for (int i = 1; i < nlength; i++) {
			assert i > 0;
			assert i <= lits.nVars() : "" + lits.nVars() + "/" + i; //$NON-NLS-1$ //$NON-NLS-2$
			activity[i] = 0.0;
			if (lits.belongsToPool(i)) {
				heap.insert(i);
			}
		}
	}

	@Override
	public String toString() {
		return "VSIDS like heuristics from MiniSAT using a heap " + phaseStrategy; //$NON-NLS-1$
	}

	public ILits getVocabulary() {
		return lits;
	}

	public void printStat(PrintWriter out, String prefix) {
		out.println(prefix + "non guided choices\t" + nullchoice); //$NON-NLS-1$
	}

	public void assignLiteral(int p) {
		// do nothing
	}

	public void updateVarAtDecisionLevel(int q) {
		phaseStrategy.updateVarAtDecisionLevel(q);

	}
}

class VarActivation implements Comparable
{
	
	public int var;
	public float activation;
	public boolean state;
	
	public VarActivation(int var, float activation)
	{
		this.var=var;
		this.activation=activation;
	}

	@Override
	public int compareTo(Object o) 
	{
		float diff=Math.abs(0.5f-((VarActivation)o).activation)-Math.abs(0.5f-activation);
		if(diff<0)
		{
			return -1;
		}
		else if(diff>0)
		{
			return 1;
		}
		else
		{
			return 0;
		}
	}
	
}
