package MLSAT;

import java.io.File;
import java.util.ArrayList;
import java.util.List;

import org.sat4j.core.LiteralsUtils;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.minisat.core.Constr;
import org.sat4j.minisat.core.ILits;
import org.sat4j.minisat.core.Solver;
import org.sat4j.minisat.orders.MLVarOrderHeap;
import org.sat4j.reader.LecteurDimacs;
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
	protected ScaleFilter scaleFilterOutputs;
	
	public MLSATSAT4J(boolean verbose, SATProblemGenerator satProblem)
	{
		this.verbose=verbose;
		scaleFilterOutputs=new ScaleFilter();
        this.satProblem=satProblem;	
		initNetwork();
		
		solver=SolverFactory.newMiniLearningHeapRsatExpSimpML(this, satProblem.getNumberVariables());
        mi=new ModelIterator(solver);
        solver.setTimeout(3600); // 1 hour timeout
        reader=new LecteurDimacs(mi);
	}

	public void initNetwork()
	{
		BInputLayer inputLayer1=new BInputLayer(null, null, satProblem.getNumberClauses()*satProblem.getNumberVariables());
		ConvolutionBLayerSparseVector convLayer1a=new ConvolutionBLayerSparseVector(new Sigmoid(), new BLayer[]{inputLayer1}, satProblem.getNumberVariables(), satProblem.getNumberClauses());
		//FullyConnectedBLayer hiddenLayer2a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{convLayer1a}, satProblem.getNumberClauses()*satProblem.getNumberVariables());
		//System.out.println("Constant size 2nd layer");
		FullyConnectedBLayer hiddenLayer2a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{convLayer1a}, satProblem.getNumberClauses());
		FullyConnectedBLayer outputLayer=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer2a}, satProblem.getNumberVariables());
		network=new SplitFeedForwardNetwork(new BLayer[][]{new BLayer[]{inputLayer1}, new BLayer[]{convLayer1a}, new BLayer[]{hiddenLayer2a}, new BLayer[]{outputLayer}});
		
		/*
		BInputLayer inputLayer1=new BInputLayer(null, null, satProblem.getNumberClauses()*satProblem.getNumberVariables());
		ConvolutionBLayer convLayer1a=new ConvolutionBLayer(new Sigmoid(), new BLayer[]{inputLayer1}, new int[]{1, satProblem.getNumberClauses()*satProblem.getNumberVariables()}, 1, new int[]{1, satProblem.getNumberVariables()});
		FullyConnectedBLayer hiddenLayer2a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{convLayer1a}, 4*satProblem.getNumberClauses());
		FullyConnectedBLayer outputLayer=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer2a}, satProblem.getNumberVariables());
		network=new SplitFeedForwardNetwork(new BLayer[][]{new BLayer[]{inputLayer1}, new BLayer[]{convLayer1a}, new BLayer[]{hiddenLayer2a}, new BLayer[]{outputLayer}});
		*/
	}
	
	public void trainNetwork(int numberSamples)
	{
		initNetwork();
		
		List<SAT> satInputs=new ArrayList<>();
		List<Matrix[]> inputs=new ArrayList<>();
		List<Matrix[]> outputs=new ArrayList<>();
		
		SATSolverSAT4J vanillaSolver=new SATSolverSAT4J();
		
		SAT solutionSAT=null;
		SAT subSAT=null;
		boolean varSet=false;
		
		while(inputs.size()<numberSamples)
		{
			if(subSAT==null || !varSet || subSAT.clauses.get(0)==null)
			{
				solutionSAT=null;
				while(solutionSAT==null || solutionSAT.isSAT()!=1)
				{
					solutionSAT=satProblem.generateSAT();
					boolean[] result=vanillaSolver.solve(solutionSAT.toCNF());
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
				inputs.add(new Matrix[]{SATToInputArrayRealVector(simplifiedSAT)});
				outputs.add(new Matrix[]{SATToOutputArrayRealVectors(simplifiedSAT, solutionSAT)});
			}
			else
			{
				inputs.set(inputs.size()-1, new Matrix[]{SATToInputArrayRealVector(simplifiedSAT)});
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
		
		float lambda=0.01f;
		BPGDUnsupervisedTraining bpgd=new BPGDUnsupervisedTraining(100, 10, lambda);
		//bpgd.setRegularization(new L2Regularization(outputLayer.getOutputSize(), lambda, 0.1));
		
		Matrix[][] inputsArray=inputs.toArray(new Matrix[0][]);
		Matrix[][] outputsArray=scaleFilterOutputs.scaleData(outputs.toArray(new Matrix[0][]), true);
		
		for(int i=0; i<1; i++)
		{
			
			bpgd.unsupervisedTrain(network, inputsArray,
					outputsArray, new EuclideanDistanceCostFunction());
			
			
			bpgd.trainNetwork(network, inputsArray,
					outputsArray, new EuclideanDistanceCostFunction());
		}
		
		SplitNetwork.saveNetwork(new File("C:\\Users\\C\\workspace\\SAT_Solvers_GPU\\PIndus4043c1100v"), network);
		//network=SplitNetwork.loadNetwork(new File("/home/c/workspace/Reinforcement Machine Learning/SavedNeuralNets/neuralNetPIndustrial120c30vNewProbNots"));
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
		((MLVarOrderHeap)((Solver)solver).order).reset();
		solver.reset();
	}
	
}
