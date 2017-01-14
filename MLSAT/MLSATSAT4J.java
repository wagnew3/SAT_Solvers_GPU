package MLSAT;

import static org.sat4j.core.LiteralsUtils.toDimacs;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.sat4j.core.LiteralsUtils;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.minisat.core.ILits;
import org.sat4j.minisat.core.Solver;
import org.sat4j.minisat.orders.MLVarOrderHeap;
import org.sat4j.reader.LecteurDimacs;
import org.sat4j.specs.Constr;
import org.sat4j.specs.IVec;
import org.sat4j.tools.ModelIterator;

import SATProblem.Clause;
import SATProblem.SAT;
import SATProblem.Variable;
import SATProblemGeneration.SATProblemGenerator;
import SATSolver.DPLL;
import SATSolver.SATSolverSAT4J;
import activationFunctions.Sigmoid;
import costFunctions.EuclideanDistanceCostFunction;
import filters.ScaleFilter;
import layer.BInputLayer;
import layer.BLayer;
import layer.ConvolutionBLayerSparseVector;
import layer.FullyConnectedBLayer;
import learningRule.BPGDUnsupervisedTraining;
import nDimensionalMatrices.FDMatrix;
import nDimensionalMatrices.Matrix;
import nDimensionalMatrices.SparseFMatrix;
import network.SplitFeedForwardNetwork;
import network.SplitNetwork;

public class MLSATSAT4J extends SATSolverSAT4J
{
	
	protected SATProblemGenerator satProblem;
	protected SplitNetwork network;
	public ScaleFilter scaleFilterInputs;
	public ScaleFilter scaleFilterOutputs;
	public int alg;
	
	public MLSATSAT4J(boolean verbose, SATProblemGenerator satProblem, int alg)
	{
		this.alg=alg;
		this.verbose=verbose;
		scaleFilterInputs=new ScaleFilter();
		scaleFilterOutputs=new ScaleFilter();
        this.satProblem=satProblem;	
		initNetwork();
		
		solver=SolverFactory.newDefaultML(this, satProblem.getNumberVariables());
        mi=new ModelIterator(solver);
        solver.setTimeout(3600); // 1 hour timeout
        reader=new LecteurDimacs(mi);
	}

	public void initNetwork()
	{
		switch(alg)
		{
			case 0:
				BInputLayer inputLayer1=new BInputLayer(null, null, satProblem.getNumberClauses()*satProblem.getNumberVariables());
				ConvolutionBLayerSparseVector convLayer1a=new ConvolutionBLayerSparseVector(new Sigmoid(), new BLayer[]{inputLayer1}, satProblem.getNumberVariables(), satProblem.getNumberClauses());
				FullyConnectedBLayer hiddenLayer2a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{convLayer1a}, 4*satProblem.getNumberClauses());
				FullyConnectedBLayer hiddenLayer3a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer2a}, (int)Math.round(0.5*satProblem.getNumberClauses()));
				FullyConnectedBLayer outputLayer=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer3a}, satProblem.getNumberVariables());
				network=new SplitFeedForwardNetwork(new BLayer[][]{new BLayer[]{inputLayer1}, new BLayer[]{convLayer1a}, new BLayer[]{hiddenLayer2a}, new BLayer[]{hiddenLayer3a}, new BLayer[]{outputLayer}});
				break;
			case 1:	
				inputLayer1=new BInputLayer(null, null, satProblem.getNumberVariables());
				FullyConnectedBLayer hiddenLayer1a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{inputLayer1}, 4*satProblem.getNumberClauses());
				hiddenLayer2a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer1a}, satProblem.getNumberClauses());
				hiddenLayer3a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer2a}, (int)Math.round(0.5*satProblem.getNumberClauses()));
				outputLayer=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer3a}, satProblem.getNumberVariables());
				network=new SplitFeedForwardNetwork(new BLayer[][]{new BLayer[]{inputLayer1}, new BLayer[]{hiddenLayer1a}, new BLayer[]{hiddenLayer2a}, new BLayer[]{hiddenLayer3a}, new BLayer[]{outputLayer}});
				break;
		}
	}
	
	public void trainNetwork(int numberSamples, boolean loadData, boolean loadNetwork)
	{
		if(!loadNetwork)
		{
			initNetwork();
			
			Matrix[][] inputsArray=null;
			Matrix[][] outputsArray=null;
			
			Matrix[][][] trainingData=null;
			
			switch(alg)
			{
				case 0:
					trainingData=getTrainingData(numberSamples);
					break;
				case 1:	
					trainingData=getTrainingDataActivationHeuristic(numberSamples);
					break;
			}
			
			inputsArray=trainingData[0];
			outputsArray=trainingData[1];
			
			if(!loadData)
			{
				try 
				{
					FileOutputStream inputsFOut=new FileOutputStream(new File(TestMLSATSAT4J.dataDir+"DataInputs"+TestMLSATSAT4J.testName));
					ObjectOutputStream inputsObjOut=new ObjectOutputStream(inputsFOut);
					inputsObjOut.writeObject(inputsArray);
					inputsObjOut.close();
					inputsFOut.close();
					
					FileOutputStream outputsFOut=new FileOutputStream(new File(TestMLSATSAT4J.dataDir+"DataOutputs"+TestMLSATSAT4J.testName));
					ObjectOutputStream outputsObjOut=new ObjectOutputStream(outputsFOut);
					outputsObjOut.writeObject(outputsArray);
					outputsObjOut.close();
					outputsFOut.close();
				} 
				catch (IOException e) 
				{
					e.printStackTrace();
				}	
			}
			else
			{
				try 
				{
					FileInputStream inputsFIn=new FileInputStream(new File(TestMLSATSAT4J.dataDir+"DataInputs"+TestMLSATSAT4J.testName));
					ObjectInputStream inputsObjIn=new ObjectInputStream(inputsFIn);
					inputsArray=(Matrix[][])inputsObjIn.readObject();
					inputsObjIn.close();
					inputsFIn.close();
					
					FileInputStream outputsFIn=new FileInputStream(new File(TestMLSATSAT4J.dataDir+"DataOutputs"+TestMLSATSAT4J.testName));
					ObjectInputStream outputsObjIn=new ObjectInputStream(outputsFIn);
					outputsArray=(Matrix[][])outputsObjIn.readObject();
					outputsObjIn.close();
					outputsFIn.close();
				} 
				catch (IOException | ClassNotFoundException e) 
				{
					e.printStackTrace();
				}
			}
			
			float lambda=0.01f;
			BPGDUnsupervisedTraining bpgd=new BPGDUnsupervisedTraining(100, 10, lambda);
			//bpgd.setRegularization(new L2Regularization(outputLayer.getOutputSize(), lambda, 0.1));
			for(int i=0; i<1; i++)
			{
				
				bpgd.unsupervisedTrain(network, inputsArray,
						outputsArray, new EuclideanDistanceCostFunction());
				
				
				bpgd.trainNetwork(network, inputsArray,
						outputsArray, new EuclideanDistanceCostFunction());
			}
			SplitNetwork.saveNetwork(new File(TestMLSATSAT4J.dataDir+"Network"+TestMLSATSAT4J.testName), network);
		}
		else
		{
			network=SplitNetwork.loadNetwork(new File(TestMLSATSAT4J.dataDir+"Network"+TestMLSATSAT4J.testName));
		}
	}
	
	Matrix[][][] getTrainingData(int numberSamples)
	{
		List<SAT> satInputs=new ArrayList<>();
		List<Matrix[]> inputs=new ArrayList<>();
		List<Matrix[]> outputs=new ArrayList<>();
		
		Matrix[][] inputsArray;
		Matrix[][] outputsArray;
		
		SATSolverSAT4J vanillaSolver=new SATSolverSAT4J();
		
		SAT solutionSAT=null;
		SAT subSAT=null;
		boolean varSet=false;
		
		while(inputs.size()<numberSamples)
		{
			if(inputs.size()%250==0)
			{
				System.out.println("Number of inputs: "+inputs.size());
				inputsArray=inputs.toArray(new Matrix[0][]);
				outputsArray=scaleFilterOutputs.scaleData(outputs.toArray(new Matrix[0][]), true);
				
				try 
				{
					FileOutputStream inputsFOut=new FileOutputStream(new File(TestMLSATSAT4J.dataDir+"DataInputs"+TestMLSATSAT4J.testName));
					ObjectOutputStream inputsObjOut=new ObjectOutputStream(inputsFOut);
					inputsObjOut.writeObject(inputsArray);
					inputsObjOut.close();
					inputsFOut.close();
					
					FileOutputStream outputsFOut=new FileOutputStream(new File(TestMLSATSAT4J.dataDir+"DataOutputs"+TestMLSATSAT4J.testName));
					ObjectOutputStream outputsObjOut=new ObjectOutputStream(outputsFOut);
					outputsObjOut.writeObject(outputsArray);
					outputsObjOut.close();
					outputsFOut.close();
				} 
				catch (IOException e) 
				{
					e.printStackTrace();
				}
			}
			if(subSAT==null || !varSet || subSAT.clauses.get(0)==null)
			{
				solutionSAT=null;
				while(solutionSAT==null || solutionSAT.isSAT()!=1)
				{
					solutionSAT=satProblem.generateSAT();
					boolean[] result=vanillaSolver.solve(solutionSAT);
					if(result!=null)
					{
						for(int varInd=0; varInd<result.length; varInd++)
						{
							if(result[varInd])
							{
								solutionSAT.variables.get(varInd).value=1;
							}
							else
							{
								solutionSAT.variables.get(varInd).value=-1;
							}
						}
						int u=0;
					}
					else
					{
						solutionSAT=null;
					}
				}
				subSAT=solutionSAT.cloneSATVariables();
				for(Variable variable: subSAT.variables)
				{
					variable.value=0;
				}
			}
			
			SAT simplifiedSAT=unitPropogation(subSAT.cloneSATVariables());
			
			satInputs.add(simplifiedSAT);
			
			Matrix newInput=SATToInputArrayRealVector(simplifiedSAT);
			if(inputs.isEmpty() || !newInput.equals(inputs.get(inputs.size()-1)[0]))
			{
				inputs.add(new Matrix[]{newInput});
				outputs.add(new Matrix[]{SATToOutputArrayRealVectors(simplifiedSAT, solutionSAT)});
			}
			else
			{
				inputs.set(inputs.size()-1, new Matrix[]{newInput});
				outputs.set(inputs.size()-1, new Matrix[]{SATToOutputArrayRealVectors(simplifiedSAT, solutionSAT)});
			}
			
			varSet=false;
			for(Clause clause: subSAT.clauses)
			{
				for(Variable variable: clause.variables)
				{
					if(variable.value==0
							&& solutionSAT.variables.get(subSAT.variables.indexOf(variable)).value!=0)
					{
						variable.value=solutionSAT.variables.get(subSAT.variables.indexOf(variable)).value;
						varSet=true;
						break;
					}
				}
				if(varSet)
				{
					break;
				}
			}
		}

		inputsArray=inputs.toArray(new Matrix[0][]);
		outputsArray=scaleFilterOutputs.scaleData(outputs.toArray(new Matrix[0][]), true);
		return new Matrix[][][]{inputsArray, outputsArray};
	}
	
	Matrix[][][] getTrainingDataActivationHeuristic(int numberSamples)
	{
		List<SAT> satInputs=new ArrayList<>();
		List<Matrix[]> inputs=new ArrayList<>();
		List<Matrix[]> outputs=new ArrayList<>();
		
		Matrix[][] inputsArray;
		Matrix[][] outputsArray;
		
		SATSolverSAT4J vanillaSolver=new SATSolverSAT4J();
		((Solver)vanillaSolver.getSolver()).trackTrainingData=true;
		
		SAT solutionSAT=null;
		SAT subSAT=null;
		boolean varSet=false;
		
		while(inputs.size()<numberSamples)
		{
			if(inputs.size()%250==0)
			{
				System.out.println("Number of inputs: "+inputs.size());
				/*
				inputsArray=inputs.toArray(new Matrix[0][]);
				outputsArray=scaleFilterOutputs.scaleData(outputs.toArray(new Matrix[0][]), true);
				
				try 
				{
					FileOutputStream inputsFOut=new FileOutputStream(new File(TestMLSATSAT4J.dataDir+"DataInputs"+TestMLSATSAT4J.testName));
					ObjectOutputStream inputsObjOut=new ObjectOutputStream(inputsFOut);
					inputsObjOut.writeObject(inputsArray);
					inputsObjOut.close();
					inputsFOut.close();
					
					FileOutputStream outputsFOut=new FileOutputStream(new File(TestMLSATSAT4J.dataDir+"DataOutputs"+TestMLSATSAT4J.testName));
					ObjectOutputStream outputsObjOut=new ObjectOutputStream(outputsFOut);
					outputsObjOut.writeObject(outputsArray);
					outputsObjOut.close();
					outputsFOut.close();
				} 
				catch (IOException e) 
				{
					e.printStackTrace();
				}
				*/
			}
			
			solutionSAT=satProblem.generateSAT();
			vanillaSolver.solve(solutionSAT);
			List<Object[]> steps=((Solver)vanillaSolver.getSolver()).steps;
			
			for(int stepInd=0; stepInd<steps.size(); stepInd++)
			{
				float[][] floatActis=new float[((double[])steps.get(stepInd)[4]).length][1];
				for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
				{
					floatActis[varInd][0]=(float)Math.log10(((double[])steps.get(stepInd)[4])[varInd]+1.0);
					if(floatActis[varInd][0]==Float.POSITIVE_INFINITY)
					{
						int u=0;
					}
				}
				
				Matrix input=new FDMatrix(floatActis);
				inputs.add(new Matrix[]{input});
				
				Object[] nextHighestStep=getNextGreaterOrEqualDLevel(steps, stepInd);
				if(nextHighestStep!=null)
				{
					List<Integer> addClauseVars=getNewConflictClauseVars((IVec<Constr>)steps.get(stepInd)[2],
							(IVec<Constr>)nextHighestStep[2]);
					List<VariableActivation> possibleVars=new ArrayList<>();
					for(Integer variable: addClauseVars)
					{
						possibleVars.add(
								new VariableActivation(variable, ((double[])steps.get(stepInd)[4])[Math.abs(variable)-1]));
					}
					Collections.sort(possibleVars);
					int bestVarInd=0;

					while(bestVarInd<possibleVars.size()
							&& !isUnassigned(possibleVars.get(bestVarInd).dimacsVariable, (ILits)steps.get(stepInd)[3]))
					{
						bestVarInd++;
					}

					if(bestVarInd<possibleVars.size())
					{
						float[] outputFloats=new float[satProblem.getNumberVariables()];
						outputFloats[Math.abs(possibleVars.get(bestVarInd).dimacsVariable)-1]=Math.signum(possibleVars.get(bestVarInd).dimacsVariable);
						Matrix output=new FDMatrix(new float[][]{outputFloats});
						outputs.add(new Matrix[]{output});
					}
					else
					{
						float[][] outputFloats=new float[satProblem.getNumberVariables()][1];
						outputFloats[Math.abs(((int)steps.get(stepInd)[6]))-1][0]=Math.signum(((int)steps.get(stepInd)[6]));
						Matrix output=new FDMatrix(outputFloats);
						outputs.add(new Matrix[]{output});
					}
				}
				else
				{
					float[][] outputFloats=new float[satProblem.getNumberVariables()][1];
					outputFloats[Math.abs(((int)steps.get(stepInd)[6]))-1][0]=Math.signum(((int)steps.get(stepInd)[6]));
					Matrix output=new FDMatrix(outputFloats);
					outputs.add(new Matrix[]{output});
				}
			}
			
			int u=0;
			
		}

		inputsArray=scaleFilterInputs.scaleData(inputs.toArray(new Matrix[0][]), true);
		outputsArray=scaleFilterOutputs.scaleData(outputs.toArray(new Matrix[0][]), true);
		return new Matrix[][][]{inputsArray, outputsArray};
	}
	
	private List<Integer> getNewConflictClauseVars(IVec<Constr> oldConflicts, IVec<Constr> newConflicts)
	{
		int constrInd=oldConflicts.size();
		List<Integer> newVariables=new ArrayList<>();
		for(; constrInd<newConflicts.size(); constrInd++)
		{
			for(int varInd=0; varInd<newConflicts.get(constrInd).size(); varInd++)
			{
				if(!newVariables.contains(toDimacs(newConflicts.get(constrInd).get(varInd))))
				{
					newVariables.add(toDimacs(newConflicts.get(constrInd).get(varInd)));
				}
			}
		}
		return newVariables;
	}
	
	private boolean isUnassigned(int dimacsVar, ILits variables)
	{
		return variables.isUnassigned(LiteralsUtils.toInternal(dimacsVar));
	}
	
	Object[] getNextGreaterOrEqualDLevel(List<Object[]> steps, int stepInd)
	{
		int compLevel=(int)(steps.get(stepInd)[5]);
		Object[] aboveStep=null;
		for(int ind=stepInd+1; ind<steps.size(); ind++)
		{
			if(compLevel>=(int)(steps.get(ind)[5]))
			{
				aboveStep=steps.get(ind);
				break;
			}
		}
		return aboveStep;
	}
	
	
	public SparseFMatrix SATToInputArrayRealVector(SAT sat)
	{
		List<Float> nonZeroValues=new ArrayList<>();
		List<Integer> nonZeroValuesRowInds=new ArrayList<>();
		List<Integer> nonZeroValuesColInds=new ArrayList<>();
		for(int clauseIndex=0; clauseIndex<satProblem.getNumberClauses(); clauseIndex++)
		{
			if(clauseIndex<sat.clauses.size())
			{
				for(int variableIndex=0; variableIndex<sat.variables.size(); variableIndex++)
				{
					int varInd=-1;
					if((varInd=sat.clauses.get(clauseIndex).variables.indexOf(sat.variables.get(variableIndex)))!=-1)
					{
						if(sat.clauses.get(clauseIndex).nots.get(varInd)==1)
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
		
		return new SparseFMatrix(nonZeroValuesArray, nonZeroValuesRowIndsArray, nonZeroValuesColIndsArray, satProblem.getNumberClauses(), satProblem.getNumberVariables());
	}
	
	
	protected Matrix SATToOutputArrayRealVectors(SAT sat, SAT solutionSAT)
	{
		Matrix output=new FDMatrix(satProblem.getNumberVariables(), 1);
		for(int variableIndex=0; variableIndex<sat.variables.size(); variableIndex++)
		{
			if(sat.variables.get(variableIndex).value==0)
			{
				output.set(variableIndex, 0, solutionSAT.variables.get(variableIndex).value);
			}
		}
		
		return output;
	}
	
	public FDMatrix getOutput(Matrix input)
	{
		return (FDMatrix)network.getOutput(new Matrix[]{input})[0];
	}
	
	public SAT toSAT(IVec<Constr> constrs, ILits lits)
	{
		List<Variable> variables=new ArrayList<>();
		for(int litInd=0; litInd<lits.nVars(); litInd++)
		{
			int intRep=LiteralsUtils.toInternal(litInd);
			variables.add(new Variable());
			if(lits.isUnassigned(intRep))
			{
				variables.get(litInd).value=0;
			}
			else if(lits.isSatisfied(intRep))
			{
				variables.get(litInd).value=1;
			}
			else
			{
				variables.get(litInd).value=-1;
			}
		}
		
		List<Clause> clauses=new ArrayList<>();
		for(int clauseInd=0; clauseInd<constrs.size(); clauseInd++)
		{
			List<Variable> clauseVaraibles=new ArrayList<>();
			List<Integer> clauseNots=new ArrayList<>();
			for(int varInd=0; varInd<constrs.get(clauseInd).size(); varInd++)
			{
				int dimacs=LiteralsUtils.toDimacs(constrs.get(clauseInd).get(varInd));
				if(dimacs<0)
				{
					clauseNots.add(1);
					dimacs=-dimacs;
				}
				else
				{
					clauseNots.add(0);
				}
				dimacs--;
				clauseVaraibles.add(variables.get(dimacs));
			}
			clauses.add(new Clause(clauseVaraibles, clauseNots));
		}
		return new SAT(clauses, variables);
	}
	
	public SAT unitPropogation(SAT sat)
    {
		boolean varSet=false;
		do
		{
	    	varSet=false;
	    	for(int clauseInd=0; clauseInd<sat.clauses.size(); clauseInd++)
	    	{
	    	    Clause currentClause=sat.clauses.get(clauseInd);
	    	    if(currentClause.isSAT()==1)
	    	    {
	        		sat.clauses.remove(clauseInd);
	        		clauseInd--;
	    	    }
	    	    for(int variableInd=0; variableInd<currentClause.variables.size(); variableInd++)
	    	    {
	        		if((currentClause.variables.get(variableInd).value+currentClause.nots.get(variableInd))%2==-1)
	        		{
	        		    currentClause.variables.remove(variableInd);
	        		    currentClause.nots.remove(variableInd);
	        		    variableInd--;
	        		}
	    	    }
	    	    
	    	    if(currentClause.variables.size()==1)
	    	    {
	        		varSet=true;
	        		currentClause.setVariableNot(0, 1);
	        		for(int unitClauseSearchInd=0; unitClauseSearchInd<sat.clauses.size(); unitClauseSearchInd++)
	        		{
	        		    Clause currentUnitSearchClause=sat.clauses.get(unitClauseSearchInd);
	        		    if(!currentClause.equals(currentUnitSearchClause))
	        		    {
		        			for(int variableInd=0; variableInd<currentUnitSearchClause.variables.size(); variableInd++)
		        			{
		        			    if(currentUnitSearchClause.variables.get(variableInd)
		        				    .equals(currentClause.variables.get(0)))
		        			    {
			        				if(currentUnitSearchClause.nots.get(variableInd)
			        					==currentClause.nots.get(0))
			        				{
			        				    sat.clauses.remove(unitClauseSearchInd);
			        				    unitClauseSearchInd--;
			        				    break;
			        				}
			        				else
			        				{
			        				    currentUnitSearchClause.variables.remove(variableInd);
			        				    currentUnitSearchClause.nots.remove(variableInd);
			        				    variableInd--;
			        				    //break; //no duplicate variables in a clause Actually that is allowed
			        				}
		        			    }
		        			}
	        		    }
	        		}
	    	    }
	    	    if(currentClause.variables.isEmpty())
	    	    {
	    	    	sat.clauses.remove(clauseInd);
	        		clauseInd--;
	    	    }
	    	}
		}
		while(varSet);
		return sat;
    }
	
	@Override
	public void reset()
	{
		//((MLVarOrderHeap)((Solver)solver).order).reset();
		solver.reset();
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
