package MLSAT;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectOutputStream;
import java.util.ArrayList;
import java.util.List;

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
import layer.SparseArrayRealVector;
import learningRule.BPGDUnsupervisedTraining;
import nDimensionalMatrices.FDMatrix;
import nDimensionalMatrices.Matrix;
import nDimensionalMatrices.SparseFMatrix;
import network.SplitFeedForwardNetwork;
import network.SplitNetwork;

public class MLSAT extends DPLL
{

	protected SATProblemGenerator satProblem;
	protected SplitNetwork network;
	protected ScaleFilter scaleFilterOutputs;
	
	public MLSAT(SATProblemGenerator satProblem)
	{
		this.satProblem=satProblem;	
		scaleFilterOutputs=new ScaleFilter();
		
		initNetwork();
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
			if(inputs.size()%500==0)
			{
				System.out.println("Number of inputs: "+inputs.size());
			}
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
		
		try 
		{
			FileOutputStream inputsFOut=new FileOutputStream(new File(TestMLSATSAT4J.dataDir+"inputsPIndus4063c1100v"));
			ObjectOutputStream inputsOOut=new ObjectOutputStream(inputsFOut);
			inputsOOut.writeObject(inputsArray);
			inputsOOut.close();
			inputsFOut.close();
			
			FileOutputStream outputsFOut=new FileOutputStream(new File(TestMLSATSAT4J.dataDir+"outputsPIndus4063c1100v"));
			ObjectOutputStream outputsOOut=new ObjectOutputStream(outputsFOut);
			inputsOOut.writeObject(outputsArray);
			inputsOOut.close();
			inputsFOut.close();
		} 
		catch (IOException e) 
		{
			e.printStackTrace();
		}
		
		for(int i=0; i<1; i++)
		{
			
			bpgd.unsupervisedTrain(network, inputsArray,
					outputsArray, new EuclideanDistanceCostFunction());
			
			
			bpgd.trainNetwork(network, inputsArray,
					outputsArray, new EuclideanDistanceCostFunction());
		}
		
		SplitNetwork.saveNetwork(new File(TestMLSATSAT4J.dataDir+"NeuralNetPIndus4063c1100v"), network);
		//network=SplitNetwork.loadNetwork(new File(TestMLSATSAT4J.homeDir+"NeuralNetPIndus4063c1100v"));
	}
	
	
	protected SparseFMatrix SATToInputArrayRealVector(SAT sat)
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
	
	
	/*
	protected ArrayRealVector SATToInputArrayRealVector(SAT sat)
	{
		ArrayRealVector input=new ArrayRealVector(0);
		
		for(int clauseIndex=0; clauseIndex<satProblem.getNumberClauses(); clauseIndex++)
		{
			ArrayRealVector clauseHistogram=new ArrayRealVector(satProblem.getNumberVariables());
			if(clauseIndex<sat.clauses.size())
			{
				for(int variableIndex=0; variableIndex<sat.variables.size(); variableIndex++)
				{
					if(sat.clauses.get(clauseIndex).variables.contains(sat.variables.get(variableIndex)))
					{
						clauseHistogram.setEntry(variableIndex, 1.0);
					}
				}
			}
			input=input.append(clauseHistogram);
		}
		
		return input;
	}
	*/
	
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
	
	Matrix suggestedValues=null;
	int setsSinceSuggestedValuesUpdate=0;
	
	public void reset()
	{
		suggestedValues.clear();
		setsSinceSuggestedValuesUpdate=0;
	}
	
	public FDMatrix getOutput(Matrix input)
	{
		return (FDMatrix)network.getOutput(new Matrix[]{input})[0];
	}
	
	@Override
    protected List<Integer> setVars(SAT sat) 
    {
		Object[] changeState=changeVariableStates.get(sat.parent);
		if(changeState==null)
		{
				
			if(suggestedValues==null || setsSinceSuggestedValuesUpdate>=50)
			{
				suggestedValues=network.getOutput(new Matrix[]{SATToInputArrayRealVector(sat)})[0];
				setsSinceSuggestedValuesUpdate=0;
			}
			setsSinceSuggestedValuesUpdate++;
			
			
			int strongestSuggestionInd=-1;
			double strongestSuggestionDistance=Double.NEGATIVE_INFINITY;
			for(int valueInd=0; valueInd<sat.variables.size(); valueInd++)
			{
				if(sat.variables.get(valueInd).value==0
						&& sat.variableFreq.get(sat.variables.get(valueInd))!=null)
				{
					double suggestionDistance=Math.abs(0.5-suggestedValues.get(valueInd, 0));
					if(suggestionDistance>strongestSuggestionDistance)
					{
						strongestSuggestionDistance=suggestionDistance;
						strongestSuggestionInd=valueInd;
					}
					break;
				}
			}

        	Object[] newChangeState=new Object[2];
        	newChangeState[0]=strongestSuggestionInd;
        	if(true/*suggestedValues.get(strongestSuggestionInd, 0)<0.5*/)
        	{
        	    newChangeState[1]=-1;
        	}
        	else
        	{
        	    newChangeState[1]=1;
        	}
        	changeVariableStates.put(sat.parent, newChangeState);
        	sat.variables.get(strongestSuggestionInd).value=(int)newChangeState[1];
        	List<Integer> changeVariables=new ArrayList<>();
        	changeVariables.add(strongestSuggestionInd);
        	
        	if((int)newChangeState[1]==-1)
        	{
        	    newChangeState[1]=1;
        	}
        	else
        	{
        	    newChangeState[1]=-1;
        	}
        	
        	return changeVariables;
		}
		else
		{
		   	sat.variables.get((int)changeState[0]).value=(int)changeState[1];
		   	changeState[1]=-2;
        	List<Integer> changeVariables=new ArrayList<>();
        	changeVariables.add((int)changeState[0]);
        	return changeVariables;
		}
    }
	
}
