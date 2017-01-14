package MLSAT;

import static org.sat4j.core.LiteralsUtils.toDimacs;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.nio.file.Files;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Hashtable;
import java.util.List;

import org.sat4j.core.LiteralsUtils;
import org.sat4j.core.Vec;
import org.sat4j.core.VecInt;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.minisat.constraints.cnf.BinaryClause;
import org.sat4j.minisat.constraints.cnf.HTClause;
import org.sat4j.minisat.constraints.cnf.Lits;
import org.sat4j.minisat.constraints.cnf.OriginalBinaryClause;
import org.sat4j.minisat.constraints.cnf.OriginalHTClause;
import org.sat4j.minisat.constraints.cnf.UnitClause;
import org.sat4j.minisat.constraints.cnf.UnitClauses;
import org.sat4j.minisat.core.ILits;
import org.sat4j.minisat.core.Solver;
import org.sat4j.minisat.orders.MLVarOrderHeap;
import org.sat4j.reader.LecteurDimacs;
import org.sat4j.specs.Constr;
import org.sat4j.specs.IVec;
import org.sat4j.tools.ModelIterator;

import validation.NActionsValidator;
import SATProblem.Clause;
import SATProblem.SAT;
import SATProblem.Variable;
import SATProblemGeneration.SATProblemGenerator;
import SATSolver.DPLL;
import SATSolver.SATSolverSAT4J;
import activationFunctions.RectifiedLinearActivationFunction;
import activationFunctions.Sigmoid;
import costFunctions.CrossEntropy;
import costFunctions.EuclideanDistanceCostFunction;
import filters.ScaleFilter;
import layer.BInputLayer;
import layer.BLayer;
import layer.ConvolutionBLayerSparseVector;
import layer.FullyConnectedBLayer;
import learningRule.BPGDUnsupervisedTraining;
import learningRule.BPGDUnsupervisedTrainingNestrov;
import learningRule.BPGDUnsupervisedTrainingNestrovDS;
import learningRule.MPBackPropGradientDescent;
import learningRule.MPBackPropGradientDescentNestrov;
import learningRule.RProp;
import learningRule.RPropMultithreaded;
import nDimensionalMatrices.FDMatrix;
import nDimensionalMatrices.Matrix;
import nDimensionalMatrices.SparseFMatrix;
import network.SplitFeedForwardNetwork;
import network.SplitNetwork;

public class MLSATSAT4J extends SATSolverSAT4J
{
	
	protected SATProblemGenerator satProblem;
	public SplitNetwork network;
	public ScaleFilter scaleFilterInputs;
	public ScaleFilter scaleFilterOutputs;
	public int alg;
	public boolean networkInitilized=false;
	
	public List<int[]> nonePoints=new ArrayList<>();
	public List<int[]> vsidsPoints=new ArrayList<>();
	public List<int[]> dlisPoints=new ArrayList<>();
	
	public static double fractionVariablesToInclude=0.01;
	public static int numberVariablesToInclude=15;
	
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
        dimacsReader=new LecteurDimacs(mi);
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
				//hiddenLayer2a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer1a}, (int)Math.round(0.5*satProblem.getNumberClauses()));
				outputLayer=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer1a}, satProblem.getNumberVariables());
				network=new SplitFeedForwardNetwork(new BLayer[][]{new BLayer[]{inputLayer1}, new BLayer[]{hiddenLayer1a}, new BLayer[]{outputLayer}});
				break;
			case 2:	
				inputLayer1=new BInputLayer(null, null, satProblem.getNumberVariables());
				hiddenLayer1a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{inputLayer1}, 4*satProblem.getNumberClauses());
				//hiddenLayer2a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer1a}, (int)Math.round(0.5*satProblem.getNumberClauses()));
				outputLayer=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer1a}, satProblem.getNumberVariables());
				network=new SplitFeedForwardNetwork(new BLayer[][]{new BLayer[]{inputLayer1}, new BLayer[]{hiddenLayer1a}, new BLayer[]{outputLayer}});
				break;
			case 3:	
				inputLayer1=new BInputLayer(null, null, 2*satProblem.getNumberVariables());
				hiddenLayer1a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{inputLayer1}, 2*satProblem.getNumberVariables());
				//hiddenLayer2a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer1a}, (int)Math.round(0.5*satProblem.getNumberClauses()));
				outputLayer=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer1a}, satProblem.getNumberVariables());
				network=new SplitFeedForwardNetwork(new BLayer[][]{new BLayer[]{inputLayer1}, new BLayer[]{hiddenLayer1a}, new BLayer[]{outputLayer}});
				break;
			case 4:	
				inputLayer1=new BInputLayer(null, null, 2*satProblem.getNumberVariables());
				hiddenLayer1a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{inputLayer1}, 4*satProblem.getNumberVariables());
				//hiddenLayer2a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer1a}, 2*satProblem.getNumberVariables());
				outputLayer=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer1a}, satProblem.getNumberVariables());
				network=new SplitFeedForwardNetwork(new BLayer[][]{new BLayer[]{inputLayer1}, new BLayer[]{hiddenLayer1a}, new BLayer[]{outputLayer}});
				break;
			case 5:	
				BInputLayer inputLayerActis=new BInputLayer(null, null, satProblem.getNumberVariables());
				BInputLayer inputLayerAddInfo=new BInputLayer(null, null, 2);
				BInputLayer inputLayerClauses=new BInputLayer(null, null, satProblem.getNumberVariables());
				FullyConnectedBLayer hiddenLayerActis=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{inputLayerActis, inputLayerAddInfo}, 2*satProblem.getNumberVariables());
				FullyConnectedBLayer hiddenLayerClauses=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{inputLayerClauses, inputLayerAddInfo}, 2*satProblem.getNumberVariables());
				//hiddenLayer2a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer1a}, 2*satProblem.getNumberVariables());
				outputLayer=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayerActis, hiddenLayerClauses}, satProblem.getNumberVariables());
				network=new SplitFeedForwardNetwork(new BLayer[][]{new BLayer[]{inputLayerActis, inputLayerAddInfo, inputLayerClauses}, new BLayer[]{hiddenLayerActis, hiddenLayerClauses}, new BLayer[]{outputLayer}});
				break;
			case 6:	
				inputLayer1=new BInputLayer(null, null, 2*satProblem.getNumberVariables());
				hiddenLayer1a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{inputLayer1}, 4*satProblem.getNumberVariables());
				//hiddenLayer2a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer1a}, 2*satProblem.getNumberVariables());
				outputLayer=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer1a}, satProblem.getNumberVariables());
				network=new SplitFeedForwardNetwork(new BLayer[][]{new BLayer[]{inputLayer1}, new BLayer[]{hiddenLayer1a}, new BLayer[]{outputLayer}});
				break;
			case 7:	
				inputLayerActis=new BInputLayer(null, null, satProblem.getNumberVariables());
				inputLayerAddInfo=new BInputLayer(null, null, 1);
				inputLayerClauses=new BInputLayer(null, null, satProblem.getNumberVariables());
				hiddenLayerActis=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{inputLayerActis, inputLayerAddInfo}, 2*satProblem.getNumberVariables());
				hiddenLayerClauses=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{inputLayerClauses, inputLayerAddInfo}, 2*satProblem.getNumberVariables());
				//hiddenLayer2a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer1a}, 2*satProblem.getNumberVariables());
				outputLayer=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayerActis, hiddenLayerClauses}, satProblem.getNumberVariables());
				network=new SplitFeedForwardNetwork(new BLayer[][]{new BLayer[]{inputLayerActis, inputLayerAddInfo, inputLayerClauses}, new BLayer[]{hiddenLayerActis, hiddenLayerClauses}, new BLayer[]{outputLayer}});
				break;
			case 8:	
				inputLayerActis=new BInputLayer(null, null, satProblem.getNumberVariables());
				inputLayerAddInfo=new BInputLayer(null, null, 4+satProblem.getNumberVariables());
				inputLayerClauses=new BInputLayer(null, null, satProblem.getNumberVariables());
				hiddenLayerActis=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{inputLayerActis, inputLayerAddInfo}, 2*satProblem.getNumberVariables());
				hiddenLayerClauses=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{inputLayerClauses, inputLayerAddInfo}, 2*satProblem.getNumberVariables());
				//hiddenLayer2a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer1a}, 2*satProblem.getNumberVariables());
				outputLayer=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayerActis, hiddenLayerClauses}, satProblem.getNumberVariables());
				network=new SplitFeedForwardNetwork(new BLayer[][]{new BLayer[]{inputLayerActis, inputLayerAddInfo, inputLayerClauses}, new BLayer[]{hiddenLayerActis, hiddenLayerClauses}, new BLayer[]{outputLayer}});
				break;
			case 9:	
				inputLayerActis=new BInputLayer(null, null, numberVariablesToInclude);
				inputLayerAddInfo=new BInputLayer(null, null, 4+numberVariablesToInclude);
				inputLayerClauses=new BInputLayer(null, null, numberVariablesToInclude);
				FullyConnectedBLayer hidden1a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{inputLayerActis, inputLayerAddInfo, inputLayerClauses}, 2*numberVariablesToInclude);
				//hiddenLayer2a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hidden1a}, 2*numberVariablesToInclude);
				outputLayer=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hidden1a}, numberVariablesToInclude);
				network=new SplitFeedForwardNetwork(new BLayer[][]{new BLayer[]{inputLayerActis, inputLayerAddInfo, inputLayerClauses}, new BLayer[]{hidden1a}, new BLayer[]{outputLayer}});
				
//				inputLayerActis=new BInputLayer(null, null, (int)Math.round(satProblem.getNumberVariables()*fractionVariablesToInclude));
//				inputLayerAddInfo=new BInputLayer(null, null, 4+(int)Math.round(satProblem.getNumberVariables()*fractionVariablesToInclude));
//				inputLayerClauses=new BInputLayer(null, null, (int)Math.round(satProblem.getNumberVariables()*fractionVariablesToInclude));
//				FullyConnectedBLayer hidden1a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{inputLayerActis, inputLayerAddInfo, inputLayerClauses}, 4*(int)Math.round(satProblem.getNumberVariables()*fractionVariablesToInclude));
//				hiddenLayer2a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hidden1a}, 2*(int)Math.round(satProblem.getNumberVariables()*fractionVariablesToInclude));
//				outputLayer=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer2a}, (int)Math.round(satProblem.getNumberVariables()*fractionVariablesToInclude));
//				network=new SplitFeedForwardNetwork(new BLayer[][]{new BLayer[]{inputLayerActis, inputLayerAddInfo, inputLayerClauses}, new BLayer[]{hidden1a}, new BLayer[]{hiddenLayer2a}, new BLayer[]{outputLayer}});

				//				inputLayerActis=new BInputLayer(null, null, (int)Math.round(satProblem.getNumberVariables()*fractionVariablesToInclude));
//				inputLayerAddInfo=new BInputLayer(null, null, 4+(int)Math.round(satProblem.getNumberVariables()*fractionVariablesToInclude));
//				inputLayerClauses=new BInputLayer(null, null, (int)Math.round(satProblem.getNumberVariables()*fractionVariablesToInclude));
//				hiddenLayerActis=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{inputLayerActis, inputLayerAddInfo}, 2*(int)Math.round(satProblem.getNumberVariables()*fractionVariablesToInclude));
//				hiddenLayerClauses=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{inputLayerClauses, inputLayerAddInfo}, 2*(int)Math.round(satProblem.getNumberVariables()*fractionVariablesToInclude));
//				hiddenLayer2a=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayerActis, hiddenLayerClauses}, 2*(int)Math.round(satProblem.getNumberVariables()*fractionVariablesToInclude));
//				outputLayer=new FullyConnectedBLayer(new Sigmoid(), new BLayer[]{hiddenLayer2a}, (int)Math.round(satProblem.getNumberVariables()*fractionVariablesToInclude));
//				network=new SplitFeedForwardNetwork(new BLayer[][]{new BLayer[]{inputLayerActis, inputLayerAddInfo, inputLayerClauses}, new BLayer[]{hiddenLayerActis, hiddenLayerClauses}, new BLayer[]{hiddenLayer2a}, new BLayer[]{outputLayer}});
				break;
		}
	}
	
	public void trainNetwork(int numberSamples, boolean loadData, boolean loadNetwork, SATSolverSAT4J vanillaSolver) throws IOException
	{
		if(!loadNetwork)
		{
			if(!networkInitilized)
			{
				initNetwork();
			}
			
			Matrix[][] inputsArray=null;
			Matrix[][] outputsArray=null;
			
			Matrix[][] validationInputsArray=null;
			Matrix[][] validationOutputsArray=null;
			
			Matrix[][][] trainingData=null;
			Matrix[][][] validationData=null;
			
			System.out.println("Alg: "+alg);
			
			if(!loadData)
			{
				switch(alg)
				{
					case 0:
						trainingData=getTrainingData(numberSamples);
						break;
					case 1:	
						break;
					case 2:
						trainingData=getTrainingDataActivationCopy(numberSamples);
						break;
					case 3:
						trainingData=getTrainingDataActivationHeuristicInformed(numberSamples);
						break;
					case 4:
						//trainingData=getTrainingDataActivationHeuristicInformedWMostSatisfied(numberSamples);
						break;
					case 5:
						trainingData=getTrainingDataActivationHeuristicInformedNoActi(numberSamples);
						break;
					case 6:
						trainingData=getTrainingDataActivationHeuristicInformedBestStep(numberSamples);
						break;
					case 7:
						trainingData=getTrainingDataActivationHeuristicInformedBestStepDI(numberSamples);
						break;
					case 8:
						trainingData=getTrainingDataActivationHeuristicInformedVarFreq(numberSamples, vanillaSolver);
						break;
					case 9:
						trainingData=getTrainingDataActivationHeuristicInformedVarFreqReduced(numberSamples, vanillaSolver);
						break;
				}
				
				
				switch(alg)
				{
					case 9:
						validationData=getTrainingDataActivationHeuristicInformedVarFreqReduced(numberSamples/5, vanillaSolver);
						break;
					default:
						System.out.println("Validation data nyi!");
						break;
				}
				
				
				inputsArray=trainingData[0];
				outputsArray=trainingData[1];
				
				validationInputsArray=validationData[0];
				validationOutputsArray=validationData[1];
				
				toCSV(inputsArray, "PI4000TrainInNoCC.csv");
				toCSV(outputsArray, "PI4000TrainOutNoCC.csv");
				toCSV(validationInputsArray, "PI4000ValInNoCC.csv");
				toCSV(validationOutputsArray, "PI4000ValOutNoCC.csv");
				
				saveData(inputsArray, outputsArray, 
						validationInputsArray, validationOutputsArray);
				
				System.out.println("Training on "+inputsArray.length);
				
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
			//BPGDUnsupervisedTrainingNestrov bpgd=new BPGDUnsupervisedTrainingNestrov(1000, 50, 50, lambda, 0.9f);
			//BPGDUnsupervisedTraining bpgd=new BPGDUnsupervisedTraining(new MPBackPropGradientDescent(1000, 50, 0.01f));
			//BPGDUnsupervisedTraining bpgd=new BPGDUnsupervisedTraining(new RPropMultithreaded(1000, 250, 0.01f));
			//BPGDUnsupervisedTraining bpgd=new BPGDUnsupervisedTraining(new RPropMultithreaded(1000, 50, 0.01f));
			//bpgd.setRegularization(new L2Regularization(outputLayer.getOutputSize(), lambda, 0.1));
			RPropMultithreaded learner=new RPropMultithreaded(50000, 500, 0.01f);
			for(int i=0; i<1; i++)
			{
				if(!networkInitilized)
				{
					
					//learner.unsupervisedTrain(network, inputsArray,
					//		outputsArray, new CrossEntropy());
							
					networkInitilized=true;
				}
				//bpgd.backprop=new MPBackPropGradientDescentNestrov(1000, 50, 0.01f, 0.9f);
				//bpgd.backprop=new RProp(1000, 50, 0.01f);
				learner.trainNetwork(network, inputsArray,
						outputsArray, new CrossEntropy(), 
						new NActionsValidator(validationInputsArray,
								validationOutputsArray, 1));
			}
			SplitNetwork.saveNetwork(new File(TestMLSATSAT4J.dataDir+"Network"+TestMLSATSAT4J.testName), network);
			
			try 
			{
				FileOutputStream inputsFOut=new FileOutputStream(new File(TestMLSATSAT4J.dataDir+"ScaleInputs"+TestMLSATSAT4J.testName));
				ObjectOutputStream inputsObjOut=new ObjectOutputStream(inputsFOut);
				inputsObjOut.writeObject(scaleFilterInputs);
				inputsObjOut.close();
				inputsFOut.close();
			} 
			catch (IOException e) 
			{
				e.printStackTrace();
			}
		}
		else
		{
			network=SplitNetwork.loadNetwork(new File(TestMLSATSAT4J.dataDir+"Network"+TestMLSATSAT4J.testName));
			
			
			try 
			{
				FileInputStream inputsFIn=new FileInputStream(new File(TestMLSATSAT4J.dataDir+"ScaleInputs"+TestMLSATSAT4J.testName));
				ObjectInputStream inputsObjIn=new ObjectInputStream(inputsFIn);
				scaleFilterInputs=(ScaleFilter)inputsObjIn.readObject();
				inputsObjIn.close();
				inputsFIn.close();
			} 
			catch (IOException | ClassNotFoundException e) 
			{
				e.printStackTrace();
			}
			
			/*
			Matrix[][] inputsArray=null;
			Matrix[][] outputsArray=null;
			
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
			
			float lambda=0.02f;
			BPGDUnsupervisedTraining bpgd=new BPGDUnsupervisedTraining(1000, 200, lambda);
			bpgd.trainNetwork(network, inputsArray,
					outputsArray, new EuclideanDistanceCostFunction());
			
			SplitNetwork.saveNetwork(new File(TestMLSATSAT4J.dataDir+"Network"+TestMLSATSAT4J.testName), network);
			*/
		}
	}
	
	void toCSV(Matrix[][] inputs, String fileName)
	{
		BufferedWriter fDatasout=null;
		try 
		{
			fDatasout=new BufferedWriter(new FileWriter(new File("/home/willie/workspace/SAT_Solvers_GPU/data/tfData/"+fileName)));
		} 
		catch (IOException e1)
		{
			e1.printStackTrace();
		}
		String inputString="";
		try 
		{
			fDatasout.write(inputString);
		} 
		catch (IOException e1) 
		{
			e1.printStackTrace();
		}
		DecimalFormat df=new DecimalFormat("#0.000000000000000000"); 
		try
		{
			for(int sampleInd=0; sampleInd<inputs.length; sampleInd++)
			{
				inputString="";
				for(int matInd=0; matInd<inputs[sampleInd].length; matInd++)
				{
					for(int inputInd=0; inputInd<inputs[sampleInd][matInd].getRows(); inputInd++)
					{
						inputString+=(df.format(inputs[sampleInd][matInd].get(inputInd, 0))+",");
					}
				}
				fDatasout.write(inputString.substring(0, inputString.length()-1)+"\n");
			}
			fDatasout.close();
		}
		catch(Exception e)
		{
			e.printStackTrace();
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
	
	Matrix[][][] getTrainingDataActivationHeuristicInformed(int numberSamples)
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
			}
			
			solutionSAT=satProblem.generateSAT();
			vanillaSolver.solve(solutionSAT);
			List<Object[]> steps=((Solver)vanillaSolver.getSolver()).steps;
			
			for(int stepInd=0; stepInd<steps.size(); stepInd++)
			{
				float[][] floatActis=new float[2*((double[])steps.get(stepInd)[4]).length][1];
				float[][] outputFloats=new float[satProblem.getNumberVariables()][1];				
				
				for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
				{
					floatActis[varInd][0]=(float)Math.log10(((double[])steps.get(stepInd)[4])[varInd]+1.0);
				}
				
				for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
				{
					floatActis[varInd+((double[])steps.get(stepInd)[4]).length][0]
							=getVarFrequency(varInd+1, (IVec<Constr>)steps.get(stepInd)[1], (IVec<Constr>)steps.get(stepInd)[2], (Lits)steps.get(stepInd)[3]);
				}
				
				Matrix input=new FDMatrix(floatActis);
				inputs.add(new Matrix[]{input});
				
				Object[] nextHighestStep=getFarthestStep(steps, stepInd);
				if((int)nextHighestStep[5]>(int)steps.get(stepInd)[5])
				{
					List<Integer> addClauseVars=getNewConflictClauseVars((IVec<Constr>)steps.get(stepInd)[2],
							(IVec<Constr>)nextHighestStep[2]);
					
					outputFloats=new float[satProblem.getNumberVariables()][1];
					for(Integer variable: addClauseVars)
					{
						outputFloats[Math.abs(variable)-1][0]=(float)Math.log10(((double[])steps.get(stepInd)[4])[Math.abs(variable)-1]+1.0);
					}

					Matrix output=new FDMatrix(outputFloats);
					outputs.add(new Matrix[]{output});
				}
				else
				{
					for(int varInd=0; varInd<((double[])nextHighestStep[4]).length; varInd++)
					{
						outputFloats[varInd][0]=(float)Math.log10(((double[])nextHighestStep[4])[varInd]+1.0);
					}
					//outputFloats[Math.abs(((int)steps.get(stepInd)[6]))-1][0]=Math.signum(((int)steps.get(stepInd)[6]));
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
	
	Matrix[][][] getTrainingDataActivationHeuristicInformedNoActi(int numberSamples)
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
			}
			
			solutionSAT=satProblem.generateSAT();
			boolean[] result=vanillaSolver.solve(solutionSAT);
			List<Object[]> steps=((Solver)vanillaSolver.getSolver()).steps;
			
			for(int stepInd=0; stepInd<steps.size(); stepInd++)
			{
				float[][] floatActis=new float[((double[])steps.get(stepInd)[4]).length][1];
				float[][] outputFloats=new float[satProblem.getNumberVariables()][1];	
				
				int unassigned=0;
				float totalFirstHeuristic=0.0f;
				
				for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
				{
					if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
					{
						floatActis[varInd][0]=5.0f*(float)Math.pow(Math.log10(((double[])steps.get(stepInd)[4])[varInd]+1.0), 0.25);
						totalFirstHeuristic+=floatActis[varInd][0];
						outputFloats[varInd][0]=floatActis[varInd][0];
						unassigned++;
					}
				}
				
				float[][] floatClauses=new float[((double[])steps.get(stepInd)[4]).length][1];
				for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
				{
					if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
					{
						floatClauses[varInd][0]
								=getSatisfiedChange(varInd+1, (int[])steps.get(stepInd)[7], (IVec<Constr>)steps.get(stepInd)[1], 
										(IVec<Constr>)steps.get(stepInd)[2], (Lits)steps.get(stepInd)[3]);
					}
				}
				
				float[][] additionalInfo=new float[2][1];
				
				additionalInfo[0][0]=((IVec<Constr>)steps.get(stepInd)[2]).size();
				additionalInfo[1][0]=unassigned;

				double dropChance=0.95;
				
				Object[] nextHighestStep=getFarthestStep(steps, stepInd);
				if((int)nextHighestStep[5]<(int)steps.get(stepInd)[5])
				{
					/*
					for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
					{
							floatActis[varInd][0]=(float)Math.log10(((double[])steps.get(stepInd)[4])[varInd]+1.0)/60.0f;
							outputFloats[varInd][0]=floatActis[varInd][0];
					}
					*/
					Matrix output=new FDMatrix(outputFloats);
					outputs.add(new Matrix[]{output});
					
					Matrix inputActis=new FDMatrix(floatActis);
					Matrix inputAddInfo=new FDMatrix(additionalInfo);
					Matrix inputlauses=new FDMatrix(floatClauses);
					inputs.add(new Matrix[]{inputActis, inputAddInfo, inputlauses});
				}
				else if(Math.random()>dropChance)
				{
					if(true)
					{
						for(int varInd=0; varInd<((double[])nextHighestStep[4]).length; varInd++)
						{
							if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
							{
								outputFloats[varInd][0]=floatClauses[varInd][0];
							}
						}
					}
					else
					{
						outputFloats[Math.abs(((int)steps.get(stepInd)[6]))-1][0]=1.0f;
					}

					Matrix output=new FDMatrix(outputFloats);
					outputs.add(new Matrix[]{output});
					
					Matrix inputActis=new FDMatrix(floatActis);
					Matrix inputAddInfo=new FDMatrix(additionalInfo);
					Matrix inputlauses=new FDMatrix(floatClauses);
					inputs.add(new Matrix[]{inputActis, inputAddInfo, inputlauses});
				}
			}
			
			int u=0;
			
		}

		inputsArray=scaleFilterInputs.scaleData(inputs.toArray(new Matrix[0][]), true);
		outputsArray=scaleFilterOutputs.scaleData(outputs.toArray(new Matrix[0][]), true);
		return new Matrix[][][]{inputsArray, outputsArray};
	}
	
	Matrix[][][] getTrainingDataActivationHeuristicInformedBestStep(int numberSamples)
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
			}
			
			solutionSAT=satProblem.generateSAT();
			boolean[] result=vanillaSolver.solve(solutionSAT);
			List<Object[]> steps=((Solver)vanillaSolver.getSolver()).steps;
			
			for(int stepInd=0; stepInd<steps.size(); stepInd++)
			{
				float[][] floatActis=new float[2*((double[])steps.get(stepInd)[4]).length+2][1];
				float[][] outputFloats=new float[satProblem.getNumberVariables()][1];	
				
				int unassigned=0;
				float totalFirstHeuristic=0.0f;
				
				for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
				{
					if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
					{
						floatActis[varInd][0]=(float)Math.log10(((double[])steps.get(stepInd)[4])[varInd]+1.0)/60.0f;
						totalFirstHeuristic+=floatActis[varInd][0];
						outputFloats[varInd][0]=floatActis[varInd][0];
						unassigned++;
					}
				}
				
				for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
				{
					if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
					{
						floatActis[varInd+((double[])steps.get(stepInd)[4]).length][0]
								=getSatisfiedChange(varInd+1, (int[])steps.get(stepInd)[7], (IVec<Constr>)steps.get(stepInd)[1], 
										(IVec<Constr>)steps.get(stepInd)[2], (Lits)steps.get(stepInd)[3]);
					}
				}
				
				floatActis[floatActis.length-2][0]=((IVec<Constr>)steps.get(stepInd)[2]).size()/250.0f;
				floatActis[floatActis.length-1][0]=unassigned/100.0f;
				
				Matrix input=new FDMatrix(floatActis);
				inputs.add(new Matrix[]{input});
				
				Object[] nextHighestStep=getFarthestStep(steps, stepInd);
				if(totalFirstHeuristic>0)
				{
					for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
					{
							floatActis[varInd][0]=(float)Math.log10(((double[])steps.get(stepInd)[4])[varInd]+1.0)/60.0f;
							outputFloats[varInd][0]=floatActis[varInd][0];
					}
					Matrix output=new FDMatrix(outputFloats);
					outputs.add(new Matrix[]{output});
				}
				else
				{
					if(true)
					{
						for(int varInd=0; varInd<((double[])nextHighestStep[4]).length; varInd++)
						{
							outputFloats[varInd][0]=floatActis[varInd+((double[])steps.get(stepInd)[4]).length][0];
						}
					}
					else
					{
						outputFloats[Math.abs(((int)steps.get(stepInd)[6]))-1][0]=1.0f;
					}

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
	
	Matrix[][][] getTrainingDataActivationHeuristicInformedBestStepDI(int numberSamples)
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
			}
			
			solutionSAT=satProblem.generateSAT();
			boolean[] result=vanillaSolver.solve(solutionSAT);
			List<Object[]> steps=((Solver)vanillaSolver.getSolver()).steps;
			
			for(int stepInd=0; stepInd<steps.size(); stepInd++)
			{
				float[][] floatActis=new float[((double[])steps.get(stepInd)[4]).length][1];
				float[][] outputFloats=new float[satProblem.getNumberVariables()][1];	
				
				int unassigned=0;
				float totalFirstHeuristic=0.0f;
				
				for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
				{
					if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
					{
						floatActis[varInd][0]=5.0f*(float)Math.pow(Math.log10(((double[])steps.get(stepInd)[4])[varInd]+1.0), 0.25);
						totalFirstHeuristic+=floatActis[varInd][0];
						outputFloats[varInd][0]=floatActis[varInd][0];
						unassigned++;
					}
				}
				
				float[][] floatClauses=new float[((double[])steps.get(stepInd)[4]).length][1];
				for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
				{
					if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
					{
						floatClauses[varInd][0]
								=getSatisfiedChange(varInd+1, (int[])steps.get(stepInd)[7], (IVec<Constr>)steps.get(stepInd)[1], 
										(IVec<Constr>)steps.get(stepInd)[2], (Lits)steps.get(stepInd)[3]);
					}
				}
				
				float[][] additionalInfo=new float[1][1];
				
				if(totalFirstHeuristic>0)
				{
					additionalInfo[0][0]=1.0f;
				}

				//double dropChance=0.95;
				double dropChance=0.5;
				
				Object[] nextHighestStep=getFarthestStep(steps, stepInd);
				if(totalFirstHeuristic>0)
				{
					/*
					for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
					{
							floatActis[varInd][0]=(float)Math.log10(((double[])steps.get(stepInd)[4])[varInd]+1.0)/60.0f;
							outputFloats[varInd][0]=floatActis[varInd][0];
					}
					*/
					Matrix output=new FDMatrix(outputFloats);
					outputs.add(new Matrix[]{output});
					
					Matrix inputActis=new FDMatrix(floatActis);
					Matrix inputAddInfo=new FDMatrix(additionalInfo);
					Matrix inputlauses=new FDMatrix(floatClauses);
					inputs.add(new Matrix[]{inputActis, inputAddInfo, inputlauses});
				}
				else if(Math.random()>dropChance)
				{
					if(true)
					{
						for(int varInd=0; varInd<((double[])nextHighestStep[4]).length; varInd++)
						{
							if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
							{
								outputFloats[varInd][0]=floatClauses[varInd][0];
							}
						}
					}
					else
					{
						outputFloats[Math.abs(((int)steps.get(stepInd)[6]))-1][0]=1.0f;
					}

					Matrix output=new FDMatrix(outputFloats);
					outputs.add(new Matrix[]{output});
					
					Matrix inputActis=new FDMatrix(floatActis);
					Matrix inputAddInfo=new FDMatrix(additionalInfo);
					Matrix inputlauses=new FDMatrix(floatClauses);
					inputs.add(new Matrix[]{inputActis, inputAddInfo, inputlauses});
				}
				
				
				
			}
			
			int u=0;
			
		}

		inputsArray=scaleFilterInputs.scaleData(inputs.toArray(new Matrix[0][]), true);
		outputsArray=scaleFilterOutputs.scaleData(outputs.toArray(new Matrix[0][]), true);
		return new Matrix[][][]{inputsArray, outputsArray};
	}
	
	Matrix[][][] getTrainingDataActivationHeuristicInformedVarFreq(int numberSamples, SATSolverSAT4J vanillaSolver)
	{
		List<SAT> satInputs=new ArrayList<>();
		List<Matrix[]> inputs=new ArrayList<>();
		List<Matrix[]> outputs=new ArrayList<>();
		
		Matrix[][] inputsArray;
		Matrix[][] outputsArray;
		
		((Solver)vanillaSolver.getSolver()).trackTrainingData=true;
		
		SAT solutionSAT=null;
		SAT subSAT=null;
		boolean varSet=false;
		int corrLClauses=0;
		int numbervsids=0;
		while(inputs.size()<numberSamples)
		{
			if(inputs.size()%250==0)
			{
				System.out.println("Number of inputs: "+inputs.size());
			}
			
			solutionSAT=satProblem.generateSAT();
			boolean[] result=vanillaSolver.solve(solutionSAT);
			List<Object[]> steps=((Solver)vanillaSolver.getSolver()).steps;
			
			for(int stepInd=0; stepInd<steps.size(); stepInd++)
			{
				float[][] floatActis=new float[((double[])steps.get(stepInd)[4]).length][1];
				float[][] outputFloats=new float[satProblem.getNumberVariables()][1];	
				
				for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
				{
					if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
					{
						floatActis[varInd][0]=5.0f*(float)Math.pow(Math.log10(((double[])steps.get(stepInd)[4])[varInd]+1.1), 0.25);
						if(floatActis[varInd][0]==Float.NEGATIVE_INFINITY)
						{
							int u=0;
						}
					}
				}
				
				float[][] floatClauses=new float[((double[])steps.get(stepInd)[4]).length][1];
				for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
				{
					if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
					{
						floatClauses[varInd][0]
								=getSatisfiedChange(varInd+1, (int[])steps.get(stepInd)[7], (IVec<Constr>)steps.get(stepInd)[1], 
										(IVec<Constr>)steps.get(stepInd)[2], (Lits)steps.get(stepInd)[3]);
					}
				}
				
				//0=unassigned in initial
				//1=unassigned in conflict clauses
				//2=# unsatisfied initial clauses
				//3=#unsatisfied conflict clauses
				//4+=var freq histogram				
				float[][] additionalInfo=new float[4+((double[])steps.get(stepInd)[4]).length][1];
				
				float unsatInitialClauses=0;
				float unassignedInitialClausesVars=0;
				for(int initialClauseInd=0; initialClauseInd<((IVec<Constr>)steps.get(stepInd)[1]).size(); initialClauseInd++)
				{
					boolean clauseSat=false;
					float unassignedThisClause=0;
					for(int varInd=0; varInd<((IVec<Constr>)steps.get(stepInd)[1]).get(initialClauseInd).size(); varInd++)
					{
						if(((Lits)steps.get(stepInd)[3]).isSatisfied(((IVec<Constr>)steps.get(stepInd)[1]).get(initialClauseInd).get(varInd)))
						{
							clauseSat=true;
							break;
						}
						if(((Lits)steps.get(stepInd)[3]).isUnassigned(((IVec<Constr>)steps.get(stepInd)[1]).get(initialClauseInd).get(varInd)))
						{
							unassignedThisClause++;
						}
					}
					if(!clauseSat)
					{
						unsatInitialClauses++;
						unassignedInitialClausesVars+=unassignedThisClause;
						for(int varInd=0; varInd<((IVec<Constr>)steps.get(stepInd)[1]).get(initialClauseInd).size(); varInd++)
						{
							if(((Lits)steps.get(stepInd)[3]).isUnassigned(((IVec<Constr>)steps.get(stepInd)[1]).get(initialClauseInd).get(varInd)))
							{
								additionalInfo[4+Math.abs(LiteralsUtils.toDimacs(((IVec<Constr>)steps.get(stepInd)[1]).get(initialClauseInd).get(varInd)))-1][0]++;
							}
						}
					}
				}
				
				float unsatConflictClauses=0;
				float unassignedConflictClausesVars=0;
				for(int initialClauseInd=0; initialClauseInd<((IVec<Constr>)steps.get(stepInd)[2]).size(); initialClauseInd++)
				{
					boolean clauseSat=false;
					float unassignedThisClause=0;
					for(int varInd=0; varInd<((IVec<Constr>)steps.get(stepInd)[2]).get(initialClauseInd).size(); varInd++)
					{
						if(((Lits)steps.get(stepInd)[3]).isSatisfied(((IVec<Constr>)steps.get(stepInd)[2]).get(initialClauseInd).get(varInd)))
						{
							clauseSat=true;
							break;
						}
						if(((Lits)steps.get(stepInd)[3]).isUnassigned(((IVec<Constr>)steps.get(stepInd)[2]).get(initialClauseInd).get(varInd)))
						{
							unassignedThisClause++;
						}
					}
					if(!clauseSat)
					{
						unsatConflictClauses++;
						unassignedConflictClausesVars+=unassignedThisClause;
						for(int varInd=0; varInd<((IVec<Constr>)steps.get(stepInd)[2]).get(initialClauseInd).size(); varInd++)
						{
							if(((Lits)steps.get(stepInd)[3]).isUnassigned(((IVec<Constr>)steps.get(stepInd)[2]).get(initialClauseInd).get(varInd)))
							{
								additionalInfo[4+Math.abs(LiteralsUtils.toDimacs(((IVec<Constr>)steps.get(stepInd)[2]).get(initialClauseInd).get(varInd)))-1][0]++;
							}
						}
					}
				}
				
				additionalInfo[0][0]=unsatInitialClauses/((IVec<Constr>)steps.get(stepInd)[1]).size();
				additionalInfo[1][0]=unassignedInitialClausesVars/((double[])steps.get(stepInd)[4]).length;
				additionalInfo[2][0]=unsatConflictClauses/((IVec<Constr>)steps.get(stepInd)[1]).size();
				additionalInfo[3][0]=unassignedConflictClausesVars/((double[])steps.get(stepInd)[4]).length;
				
				boolean actiBest=false;
				

				
				
				double dropChance=0.99;
				
				float[] correctChooseVars=new float[satProblem.getNumberVariables()];
				Object[] nextHighestStep=getFarthestStep(steps, stepInd);
				if((int)nextHighestStep[5]<(int)steps.get(stepInd)[5])
				{
					List<Integer> addClauseVars=getNewConflictClauseVars((IVec<Constr>)steps.get(stepInd)[2],
							(IVec<Constr>)nextHighestStep[2]);						
					
					for(Integer variable: addClauseVars)
					{
						if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(Math.abs(variable))))
						{
							correctChooseVars[Math.abs(variable)-1]=1.0f;
						}									
					}
				}
				else
				{
					
					if(result!=null)
					{
						for(int varInd=0; varInd<((double[])nextHighestStep[4]).length; varInd++)
						{
							if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1))
									&& ((((int[])steps.get(stepInd)[7])[varInd+1]%2==1 && !result[varInd]) ||
											(((int[])steps.get(stepInd)[7])[varInd+1]%2==0 && result[varInd])))
							{
								correctChooseVars[varInd]=1.0f;
							}
						}
					}
				}
				
				
				int numberActi=0;
				int numberCC=0;
				int n=0;
				while(numberActi==numberCC
						&& n<satProblem.getNumberVariables())
				{
					if(correctChooseVars[getNthHighest(floatActis, n)]==1)
					{
						numberActi++;
					}
					if(correctChooseVars[getNthHighest(floatClauses, n)]==1)
					{
						numberCC++;
					}
					n++;
				}
				if(unsatConflictClauses>0)
				{
					numbervsids++;
				}
				if(numberActi>numberCC)
				{
					outputFloats=cloneFloatssToFloatss(floatActis);
					
					if(unsatConflictClauses>0)
					{
						corrLClauses++;
					}
				}
				else if(numberActi<numberCC)
				{
					outputFloats=cloneFloatssToFloatss(floatClauses);
				}
				else
				{
					if(Math.random()<0.5)
					{
						outputFloats=cloneFloatssToFloatss(floatActis);
					}
					else
					{
						outputFloats=cloneFloatssToFloatss(floatClauses);
					}
				}
				
				Matrix output=new FDMatrix(outputFloats);
				outputs.add(new Matrix[]{output});
				
				Matrix inputActis=new FDMatrix(floatActis);
				Matrix inputAddInfo=new FDMatrix(additionalInfo);
				Matrix inputlauses=new FDMatrix(floatClauses);
				inputs.add(new Matrix[]{inputActis, inputAddInfo, inputlauses});				
			}
			
			int u=0;
			
		}

		inputsArray=scaleFilterInputs.scaleData(inputs.toArray(new Matrix[0][]), true);
		outputsArray=scaleFilterOutputs.scaleData(outputs.toArray(new Matrix[0][]), true);
		return new Matrix[][][]{inputsArray, outputsArray};
	}
	
	
	Matrix[][][] getTrainingDataActivationHeuristicInformedVarFreqReduced(int numberSamples, SATSolverSAT4J vanillaSolver) throws IOException
	{
		//int numberVariablesToInclude=(int)Math.round(satProblem.getNumberVariables()*fractionVariablesToInclude);
		
		List<SAT> satInputs=new ArrayList<>();
		int inputOffset=0;
		
		Matrix[][] inputsArray=new Matrix[numberSamples][];
		Matrix[][] outputsArray=new Matrix[numberSamples][];
		
		((Solver)vanillaSolver.getSolver()).trackTrainingData=true;
		
		SAT solutionSAT=null; 
		SAT subSAT=null;
		boolean varSet=false;
		int corrLClauses=0;
		int numbervsids=0;
		int lineNumber=0;
		int inputsCreated=0;
		while(inputsCreated<numberSamples)
		{
			/*
			int numberThreads=8;
			OutputProducer[] threads=new OutputProducer[numberThreads];
			for(int threadInd=0; threadInd<numberThreads; threadInd++)
			{
				threads[threadInd]=new OutputProducer(inputsArray, outputsArray, 
						steps, threadInd, numberThreads, inputOffset, numberSamples,
						numberVariablesToInclude, satProblem, results);
				threads[threadInd].start();
			}
			boolean allFinished=false;
			do
			{
				allFinished=true;
				for(OutputProducer thread: threads)
				{
					if(!thread.done)
					{
						allFinished=false;
						try 
						{
							Thread.sleep(200);
						} 
						catch (InterruptedException e) 
						{
							e.printStackTrace();
						}
						break;
					}
				}
			}
			while(!allFinished);
			*/
			
			getResult();
			steps=new ArrayList<>();
			lineNumber=0;
			Object[] line=null;
			while((line=getLine(lineNumber))!=null)
			{
				if(inputsCreated%10==0)
				{
					System.out.println("Number of inputs: "+inputsCreated);
				}
				
				float[][] floatActis=new float[((double[])line[4]).length][1];
				float[][] outputFloats=new float[numberVariablesToInclude][1];
				
				List<VariableActivation> actisVarList=new ArrayList<>();
				List<VariableActivation> clausesVarList=new ArrayList<>();
				int[] satChanges=getSatisfiedChange((int[])line[7], (IVec<Constr>)line[1], 
						(IVec<Constr>)line[2], (Lits)line[3]);
				for(int varInd=0; varInd<((double[])line[4]).length; varInd++)
				{
					if(((Lits)line[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
					{
						actisVarList.add(new VariableActivation(varInd, 5.0f*(float)Math.pow(Math.log10(((double[])line[4])[varInd]+1.0), 0.25)));
					}
					if(((Lits)line[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
					{
						clausesVarList.add(new VariableActivation(varInd, satChanges[varInd]));
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
				
				for(int varInd=0; varInd<((double[])line[4]).length; varInd++)
				{
					if(((Lits)line[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
					{
						floatActis[varInd][0]=(float)Math.pow(((double[])line[4])[varInd], 0.25);
					}
				}
				
				float[][] floatClauses=new float[((double[])line[4]).length][1];
				int[] satChangesArr=getSatisfiedChange((int[])line[7], (IVec<Constr>)line[1], 
						(IVec<Constr>)line[2], (Lits)line[3]);
				for(int varInd=0; varInd<((double[])line[4]).length; varInd++)
				{
					if(((Lits)line[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
					{
						floatClauses[varInd][0]=satChangesArr[varInd];
					}
				}
				
				//0=unassigned in initial
				//1=unassigned in conflict clauses
				//2=# unsatisfied initial clauses
				//3=#unsatisfied conflict clauses
				//4+=var freq histogram				
				float[][] additionalInfo=new float[4+numberVariablesToInclude][1];
				
				float unsatInitialClauses=0;
				float unassignedInitialClausesVars=0;
				for(int initialClauseInd=0; initialClauseInd<((IVec<Constr>)line[1]).size(); initialClauseInd++)
				{
					boolean clauseSat=false;
					float unassignedThisClause=0;
					for(int varInd=0; varInd<((IVec<Constr>)line[1]).get(initialClauseInd).size(); varInd++)
					{
						if(((Lits)line[3]).isSatisfied(((IVec<Constr>)line[1]).get(initialClauseInd).get(varInd)))
						{
							clauseSat=true;
							break;
						}
						if(((Lits)line[3]).isUnassigned(((IVec<Constr>)line[1]).get(initialClauseInd).get(varInd)))
						{
							unassignedThisClause++;
						}
					}
					if(!clauseSat)
					{
						unsatInitialClauses++;
						unassignedInitialClausesVars+=unassignedThisClause;
						for(int varInd=0; varInd<((IVec<Constr>)line[1]).get(initialClauseInd).size(); varInd++)
						{
							if(((Lits)line[3]).isUnassigned(((IVec<Constr>)line[1]).get(initialClauseInd).get(varInd))
									&& includedHeuristicVariables.contains(Math.abs(LiteralsUtils.toDimacs(((IVec<Constr>)line[1]).get(initialClauseInd).get(varInd)))))
							{
								additionalInfo[4+includedHeuristicVariables.indexOf(Math.abs(LiteralsUtils.toDimacs(((IVec<Constr>)line[1]).get(initialClauseInd).get(varInd))))][0]++;
							}
						}
					}
				}
				
				float unsatConflictClauses=0;
				float unassignedConflictClausesVars=0;
				for(int initialClauseInd=0; initialClauseInd<((IVec<Constr>)line[2]).size(); initialClauseInd++)
				{
					boolean clauseSat=false;
					float unassignedThisClause=0;
					for(int varInd=0; varInd<((IVec<Constr>)line[2]).get(initialClauseInd).size(); varInd++)
					{
						if(((Lits)line[3]).isSatisfied(((IVec<Constr>)line[2]).get(initialClauseInd).get(varInd)))
						{
							clauseSat=true;
							break;
						}
						if(((Lits)line[3]).isUnassigned(((IVec<Constr>)line[2]).get(initialClauseInd).get(varInd)))
						{
							unassignedThisClause++;
						}
					}
					if(!clauseSat)
					{
						unsatConflictClauses++;
						unassignedConflictClausesVars+=unassignedThisClause;
						for(int varInd=0; varInd<((IVec<Constr>)line[2]).get(initialClauseInd).size(); varInd++)
						{
							if(((Lits)line[3]).isUnassigned(((IVec<Constr>)line[2]).get(initialClauseInd).get(varInd))
									&& includedHeuristicVariables.contains(LiteralsUtils.toDimacs(((IVec<Constr>)line[2]).get(initialClauseInd).get(varInd))))
							{
								additionalInfo[4+includedHeuristicVariables.indexOf(LiteralsUtils.toDimacs(((IVec<Constr>)line[2]).get(initialClauseInd).get(varInd)))][0]++;
							}
						}
					}
				}
				
				additionalInfo[0][0]=unsatInitialClauses/((IVec<Constr>)line[1]).size();
				additionalInfo[1][0]=unassignedInitialClausesVars/((double[])line[4]).length;
				additionalInfo[2][0]=unsatConflictClauses/((IVec<Constr>)line[1]).size();
				additionalInfo[3][0]=unassignedConflictClausesVars/((double[])line[4]).length;
				
				boolean actiBest=false;
				double dropChance=0.99;
				
				float[] correctChooseVars=new float[((double[])line[4]).length];
				Object[] nextHighestStep=getFarthestStep(steps, lineNumber);
				int numberCorrectChooseVars=0;
				if((int)nextHighestStep[5]<(int)line[5])
				{
					List<Integer> addClauseVars=getNewConflictClauseVars((IVec<Constr>)line[2],
							(IVec<Constr>)nextHighestStep[2]);						
					
					for(Integer variable: addClauseVars)
					{
						if(((Lits)line[3]).isUnassigned(LiteralsUtils.toInternal(Math.abs(variable))))
						{
							correctChooseVars[Math.abs(variable)]=1.0f;
							numberCorrectChooseVars++;
						}									
					}
				}
				//else
				//{
					
					if(results!=null)
					{
						for(int varInd=0; varInd<((double[])nextHighestStep[4]).length; varInd++)
						{
							if(((Lits)line[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1))
									&& ((((int[])line[7])[varInd+1]%2==1 && !results[varInd]) ||
											(((int[])line[7])[varInd+1]%2==0 && results[varInd])))
							{
								correctChooseVars[varInd]=1.0f;
								numberCorrectChooseVars++;
							}
						}
					}
				//}
				
				
				int numberActi=0;
				System.out.println("-------------------------------------no cc");
				int numberCC=0;
				int n=0;
				while(numberActi==numberCC
						&& n<((double[])line[4]).length
						&& (numberActi<numberCorrectChooseVars || numberCC<numberCorrectChooseVars))
				{
					
					if(correctChooseVars[getNthHighest(floatActis, n)]==1)
					{
						//outputFloats[n][0]=20.0f;
						numberActi++;
					}
					/*
					else if(correctChooseVars[getNthHighest(floatClauses, n)]==1)
					{
						outputFloats[n][0]=20.0f;
					}
					else
					{
						outputFloats[n][0]=inputFloatActis[n][0]/3.0f;
					}
					*/
					if(correctChooseVars[getNthHighest(floatClauses, n)]==1)
					{
						numberCC++;
					}
					n++;
				}
				
				//numberCC=-1;
				if(numberActi>numberCC)
				{
					outputFloats=cloneFloatssToFloatss(inputFloatActis);
				}
				else if(numberActi<numberCC)
				{
					outputFloats=cloneFloatssToFloatss(inputFloatClauses);
				}
				else
				{
					if(Math.random()<0.5)
					{
						outputFloats=cloneFloatssToFloatss(inputFloatActis);
					}
					else
					{
						outputFloats=cloneFloatssToFloatss(inputFloatClauses);
					}
				}
				
				
				if(inputsCreated<outputsArray.length)
				{
					Matrix output=new FDMatrix(outputFloats);
					outputsArray[inputsCreated]=new Matrix[]{output};
					
					Matrix inputActis=new FDMatrix(inputFloatActis);
					Matrix inputAddInfo=new FDMatrix(additionalInfo);
					Matrix inputClauses=new FDMatrix(inputFloatClauses);
					inputsArray[inputsCreated]=new Matrix[]{inputActis, inputAddInfo};	
					inputsCreated++;
				}
				
				if(lineNumber>5)
				{
					freeLine(lineNumber-5);
				}
				lineNumber++;
			}
			//lineNumber++;
		}

		inputsArray=scaleFilterInputs.scaleData(inputsArray, true);
		outputsArray=scaleFilterInputs.scaleData(outputsArray);
		return new Matrix[][][]{inputsArray, outputsArray};
	}
	
	String saveStub="/home/willie/workspace/SAT_Solvers_GPU/data/caffeValidation";
	BufferedReader reader=null;
	String dataString="PIndus4000";
	
	List<Object[]> steps=new ArrayList<>();
	boolean[] results;
	long charsRead=0;
	
	Lits lastVariableAssigns=null;
	Vec<Constr> constraints=new Vec<>();
	Vec<Constr> prevLearnedConstraints=new Vec<>();
	int loaded=0;
	
	Object[] getLine(int lineNumber)
	{
		if(reader==null)
		{
			try 
			{
				reader=new BufferedReader(new FileReader(new File("/home/willie/workspace/SAT_Solvers_GPU/data/trainingData/"+dataString)));
			} 
			catch (FileNotFoundException e) 
			{
				e.printStackTrace();
			}
		}
		
		while(steps.size()<=lineNumber)
		{
			String stepString=null;
			try 
			{
				do
				{
					stepString=reader.readLine();
					loaded++;
				}
				while(stepString.isEmpty());
			} 
			catch (IOException e) 
			{
				e.printStackTrace();
			}
			if(loaded%100==0)
			{
				System.out.println("load "+loaded);
			}
			charsRead+=stepString.length();
			if(stepString.charAt(0)=='R')
			{
				boolean[] newResult=new boolean[stepString.length()-1];
				for(int ind=1; ind<stepString.length(); ind++)
				{
					if(stepString.charAt(ind)=='1')
					{
						newResult[ind-1]=true;
					}
					else
					{
						newResult[ind-1]=false;
					}
				}
				steps.add(null);
				break;
			}
			else if(stepString.charAt(0)=='N')
			{
				steps.add(null);
				break;
			}
			else if(stepString.charAt(0)=='C')
			{
				//initial clauses
				constraints=new Vec<>();
				VecInt constraint=null;
	        	int numberInd=-1;
	        	for(int ind=1; ind<stepString.length(); ind++)
	        	{
	        		if(stepString.charAt(ind)=='(')
	        		{
	        			constraint=new VecInt();
	        			numberInd=ind+1;
	        		}
	        		else if(stepString.charAt(ind)==')')
	        		{
	        			numberInd=-1;
	        			if(constraint.size()>0)
	        			{
	        				constraints.push(new OriginalHTClause(constraint, null));
	        			}
	        		}
	        		else if(stepString.charAt(ind)==' ')
	        		{
	        			if(numberInd>-1)
	        			{
	        				constraint.push(LiteralsUtils.toInternal(Integer.parseInt(stepString.substring(numberInd, ind))));
	        			}
	        			numberInd=ind+1;
	        		}
	        	}
	        	prevLearnedConstraints=new Vec<>();
	        	continue;
			}
			Object[] stepInfo=new Object[8];
			if(!steps.isEmpty())
			{
				stepInfo[0]=steps.get(steps.size()-1);
			}
			
			stepInfo[1]=constraints;
	    	
	    	//learned clauses
			Hashtable<VecInt, VecInt> removedClauses=new Hashtable<>();
	    	Vec<Constr> learnedConstraints=new Vec<>();
			VecInt learnedConstraint=null;
	    	int learnedClauseEnd=stepString.indexOf('R');
	    	int numberInd=-1;
	    	VecInt constraint=null;
	    	int ind=0;
	    	for(; ind<=learnedClauseEnd; ind++)
	    	{
	    		if(stepString.charAt(ind)=='(')
	    		{
	    			constraint=new VecInt();
	    			numberInd=ind+1;
	    		}
	    		else if(stepString.charAt(ind)==')')
	    		{
	    			numberInd=-1;
	    			if(constraint.size()>0)
	    			{
	    				removedClauses.put(constraint, constraint);
	    			}
	    		}
	    		else if(stepString.charAt(ind)==' ')
	    		{
	    			if(numberInd>-1)
	    			{
	    				/*
	    				if(Integer.parseInt(stepString.substring(numberInd, ind))<1300)
	    				{
	    					int i=Integer.parseInt(stepString.substring(numberInd, ind));
	    					int u=0;
	    				}
	    				*/
	    				constraint.push(Integer.parseInt(stepString.substring(numberInd, ind)));
	    			}
	    			numberInd=ind+1;
	    		}
	    	}
	    	
	    	for(int constrInd=0; constrInd<prevLearnedConstraints.size(); constrInd++)
	    	{
	    		if(removedClauses.get(prevLearnedConstraints.get(constrInd))==null)
	    		{
	    			learnedConstraints.push(prevLearnedConstraints.get(constrInd));
	    		}
	    	}
	    	
	    	learnedClauseEnd=stepString.indexOf('E');
	    	for(; ind<=learnedClauseEnd; ind++)
	    	{
	    		if(stepString.charAt(ind)=='(')
	    		{
	    			constraint=new VecInt();
	    			numberInd=ind+1;
	    		}
	    		else if(stepString.charAt(ind)==')')
	    		{
	    			numberInd=-1;
	    			if(constraint.size()==1)
	    			{
	    				learnedConstraints.push(new UnitClause(constraint.get(0)));
	    			}
	    			else if(constraint.size()==2)
	    			{
	    				learnedConstraints.push(new OriginalBinaryClause(constraint, null));
	    			}
	    			if(constraint.size()>2)
	    			{
	    				learnedConstraints.push(new OriginalHTClause(constraint, null));
	    			}
	    		}
	    		else if(stepString.charAt(ind)==' ')
	    		{
	    			if(numberInd>-1)
	    			{
	    				if(Integer.parseInt(stepString.substring(numberInd, ind))>1300)
	    				{
	    					int u=0;
	    				}
	    				constraint.push(Integer.parseInt(stepString.substring(numberInd, ind)));
	    			}
	    			numberInd=ind+1;
	    		}
	    	}
	    	
	    	stepInfo[2]=learnedConstraints;
	    	prevLearnedConstraints=learnedConstraints;
	    	
	    	int numberVariablesIndEnd=stepString.indexOf(' ', learnedClauseEnd);
	    	int numberVariables=Integer.parseInt(stepString.substring(learnedClauseEnd+1, numberVariablesIndEnd));
	
	    	if(numberVariables!=650)
	    	{
	    		int u=0;
	    	}
	    	//variable assignements
	    	Lits variables=new Lits();
	    	variables.init(numberVariables);
	    	int variablesSet=0;
	    	ind=numberVariablesIndEnd;
	    	while(variablesSet<numberVariables)
	    	{
	    		if(stepString.charAt(ind)!=' ')
	    		{
	    			int nextSpace=stepString.indexOf(' ', ind);
	    			int varValue=Integer.parseInt(stepString.substring(ind, nextSpace));
	    			if(varValue==1)
	    			{
	    				variables.satisfies(LiteralsUtils.toInternal((variablesSet+1)));
	    			}
	    			else if(varValue==-1)
	    			{
	    				variables.satisfies(LiteralsUtils.toInternal(-(variablesSet+1)));
	    			}
	    			else if(varValue==0)
	    			{
	    				
	    			}
	    			else
	    			{
	    				System.out.println("Training data parse: unknown var value!");
	    			}
	    			variablesSet++;
	    			ind=nextSpace;
	    		}
	    		ind++;
	    	}
	    	stepInfo[3]=variables;
	    	
	    	
	    	//activites
	    	ind++;
	    	double[] activites=new double[numberVariables];
	    	variablesSet=0;
	    	while(variablesSet<numberVariables)
	    	{
	    		if(stepString.charAt(ind)!=' ')
	    		{
	    			int nextSpace=stepString.indexOf(' ', ind);
	    			activites[variablesSet]=Double.parseDouble(stepString.substring(ind, nextSpace));
	    			variablesSet++;
	    			ind=nextSpace;
	    		}
	    		ind++;
	    	}
	    	stepInfo[4]=activites;
	
	    	//descision level
	    	ind=stepString.indexOf('L', ind);
	    	ind++;
	    	int descLvlEndInd=stepString.indexOf(' ', ind);
	    	stepInfo[5]=Integer.parseInt(stepString.substring(ind, descLvlEndInd));
	
	    	//descision variable
	    	ind=stepString.indexOf('V', ind);
	    	ind++;
	    	int descVarEndInd=stepString.indexOf(' ', ind);
	    	stepInfo[6]=Integer.parseInt(stepString.substring(ind, descVarEndInd));
	
	    	//polarities
	    	ind=descVarEndInd+1;
	    	int[] polarities=new int[numberVariables+1];
	    	variablesSet=0;
	    	while(variablesSet<numberVariables)
	    	{
	    		if(stepString.charAt(ind)!=' ')
	    		{
	    			polarities[variablesSet+1]=Integer.parseInt(stepString.substring(ind, ind+1));
	    			variablesSet++;
	    		}
	    		ind++;
	    	}
	    	stepInfo[7]=polarities;
	    	
	    	steps.add(stepInfo);
		}
		if(lineNumber<steps.size())
		{
			return steps.get(lineNumber);
		}
		else
		{
			return null;
		}
	}
	
	void freeLine(int lineNumber)
	{
		steps.set(lineNumber, new Object[0]);
	}
	
	void getResult()
	{
		int read=0;
		stepsSize--;
		if(reader==null)
		{
			try 
			{
				reader=new BufferedReader(new FileReader(new File("/home/willie/workspace/SAT_Solvers_GPU/data/trainingData/"+dataString)));
			} 
			catch (FileNotFoundException e) 
			{
				e.printStackTrace();
			}
		}
		while(true)
		{
			String stepString=null;
			
			try 
			{
				stepString=reader.readLine();
			} 
			catch (IOException e) 
			{
				e.printStackTrace();
			}
			if(stepString!=null)
			{
				read++;
				if(stepString.charAt(0)=='R')
				{
					boolean[] newResult=new boolean[stepString.length()-1];
					for(int ind=1; ind<stepString.length(); ind++)
					{
						if(stepString.charAt(ind)=='1')
						{
							newResult[ind-1]=true;
						}
						else
						{
							newResult[ind-1]=false;
						}
					}
					results=newResult;
					break;
				}
				else if(stepString.charAt(0)=='N')
				{
					results=null;
					break;
				}
				else
				{
					stepsSize++;
				}
			}
			
			if(read%10==0)
			{
				System.out.println("result read: "+read);
			}
		}
		try 
		{
			reader=new BufferedReader(new FileReader(new File("/home/willie/workspace/SAT_Solvers_GPU/data/trainingData/"+dataString)));
			reader.skip(charsRead);
			if(charsRead>0)
			{
				charsRead+=reader.readLine().length();
			}
		} 
		catch (IOException e) 
		{
			e.printStackTrace();
		}
	}
	
	public void saveData(Matrix[][] trainingInputs, Matrix[][] trainingOutputs,
			Matrix[][] validationInputs, Matrix[][] validationOutputs)
	{
		try
		{
			File trainingInputsFile=new File(saveStub+"trainingInputsFile");
			BufferedWriter fOut=new BufferedWriter(new FileWriter(trainingInputsFile));
			for(Matrix[] mats: trainingInputs)
			{
				for(Matrix mat: mats)
				{
					for(int rowInd=0; rowInd<((FDMatrix)mat).getLen(); rowInd++)
					{
						fOut.write(""+mat.get(rowInd, 0)+" ");
					}
				}
				fOut.write("\n");
			}
			fOut.close();
			
			File trainingOutputsFile=new File(saveStub+"trainingOutputsFile");
			fOut=new BufferedWriter(new FileWriter(trainingOutputsFile));
			for(Matrix[] mats: trainingOutputs)
			{
				for(Matrix mat: mats)
				{
					for(int rowInd=0; rowInd<((FDMatrix)mat).getLen(); rowInd++)
					{
						fOut.write(""+mat.get(rowInd, 0)+" ");
					}
				}
				fOut.write("\n");
			}
			fOut.close();
			/*
			File validationInputsFile=new File(saveStub+"validationInputsFile");
			fOut=new BufferedWriter(new FileWriter(validationInputsFile));
			for(Matrix[] mats: validationInputs)
			{
				for(Matrix mat: mats)
				{
					for(int rowInd=0; rowInd<((FDMatrix)mat).getLen(); rowInd++)
					{
						fOut.write(""+mat.get(rowInd, 0)+" ");
					}
				}
				fOut.write("\n");
			}
			fOut.close();
			
			File validationOutputsFile=new File(saveStub+"validationOutputsFile");
			fOut=new BufferedWriter(new FileWriter(validationOutputsFile));
			for(Matrix[] mats: validationOutputs)
			{
				for(Matrix mat: mats)
				{
					for(int rowInd=0; rowInd<((FDMatrix)mat).getLen(); rowInd++)
					{
						fOut.write(""+mat.get(rowInd, 0)+" ");
					}
				}
				fOut.write("\n");
			}
			fOut.close();
			*/
		} 
		catch (IOException e)
		{
			e.printStackTrace();
		}
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
	
	public static int getNthHighest(float[][] values, int n)
	{
		float[] valuesCopy=cloneFloatss(values);
		Arrays.sort(valuesCopy);
		for(int ind=0; ind<values.length; ind++)
		{
			if(values[ind][0]==valuesCopy[n])
			{
				return ind;
			}
		}
		
		/*
		int highestInd=-1;
		for(int r=0; r<=n; r++)
		{
			highestInd=-1;
			float highestValues=Float.NEGATIVE_INFINITY;
			for(int ind=0; ind<valuesCopy.length; ind++)
			{
				if(valuesCopy[ind]>highestValues)
				{
					highestValues=valuesCopy[ind];
					highestInd=ind;
				}
			}
			valuesCopy[highestInd]=Float.NEGATIVE_INFINITY;
		}
		return highestInd;
		*/
		return -1;
	}
	
	public static float[] cloneFloatss(float[][] floatss)
	{
		float[] floats=new float[floatss.length];
		for(int ind=0; ind<floats.length; ind++)
		{
			floats[ind]=floatss[ind][0];
		}
		return floats;
	}
	
	public static float[][] cloneFloatssToFloatss(float[][] floatss)
	{
		float[][] floats=new float[floatss.length][1];
		for(int ind=0; ind<floats.length; ind++)
		{
			floats[ind][0]=floatss[ind][0];
		}
		return floats;
	}
	
	public static int[] getSatisfiedChange(int[] phase, IVec<Constr> initialConstrs, IVec<Constr> learnedConstrs, Lits lits)
	{
		int[] satChanges=new int[phase.length];

		for(int constrInd=0; constrInd<initialConstrs.size(); constrInd++)
		{
			boolean unsat=true;
			for(int varInd=0; varInd<initialConstrs.get(constrInd).size(); varInd++)
			{
				if(lits.isSatisfied(initialConstrs.get(constrInd).get(varInd)))
				{
					unsat=false;
				}
			}
			if(unsat)
			{
				for(int varInd=0; varInd<initialConstrs.get(constrInd).size(); varInd++)
				{
					if(initialConstrs.get(constrInd).get(varInd)==phase[Math.abs(LiteralsUtils.toDimacs(initialConstrs.get(constrInd).get(varInd)))]
							&& lits.isUnassigned(initialConstrs.get(constrInd).get(varInd)))
					{
						satChanges[Math.abs(LiteralsUtils.toDimacs(initialConstrs.get(constrInd).get(varInd)))]++;
					}
				}
			}
		}
		
		/*
		for(int constrInd=0; constrInd<learnedConstrs.size(); constrInd++)
		{
			for(int varInd=0; varInd<learnedConstrs.get(constrInd).size(); varInd++)
			{
				if(learnedConstrs.get(constrInd).get(varInd)==internalLit)
				{
					numberSatisfiedClauses++;
				}
			}
		}
		*/
		
		for(int constrInd=0; constrInd<learnedConstrs.size(); constrInd++)
		{
			boolean unsat=true;
			for(int varInd=0; varInd<learnedConstrs.get(constrInd).size(); varInd++)
			{
				if(lits.isSatisfied(learnedConstrs.get(constrInd).get(varInd)))
				{
					unsat=false;
				}
			}
			if(unsat)
			{
				for(int varInd=0; varInd<learnedConstrs.get(constrInd).size(); varInd++)
				{
					if(learnedConstrs.get(constrInd).get(varInd)==phase[Math.abs(LiteralsUtils.toDimacs(learnedConstrs.get(constrInd).get(varInd)))]
							&& lits.isUnassigned(learnedConstrs.get(constrInd).get(varInd)))
					{
						satChanges[Math.abs(LiteralsUtils.toDimacs(learnedConstrs.get(constrInd).get(varInd)))]++;
					}
				}
			}
		}
		
		return satChanges;
	}
	
	private int getVarFrequency(int dimacsVar, IVec<Constr> initialConstrs, IVec<Constr> learnedConstrs, Lits lits)
	{
		int frequency=0;
		for(int constrInd=0; constrInd<initialConstrs.size(); constrInd++)
		{
			for(int varInd=0; varInd<initialConstrs.get(constrInd).size(); varInd++)
			{
				if(lits.isUnassigned(toDimacs(initialConstrs.get(constrInd).get(varInd)))
						&&  Math.abs(toDimacs(initialConstrs.get(constrInd).get(varInd)))==dimacsVar)
				{
					frequency++;
				}
			}
		}
		
		for(int constrInd=0; constrInd<learnedConstrs.size(); constrInd++)
		{
			for(int varInd=0; varInd<learnedConstrs.get(constrInd).size(); varInd++)
			{
				if(lits.isUnassigned(toDimacs(initialConstrs.get(constrInd).get(varInd)))
						&& Math.abs(toDimacs(learnedConstrs.get(constrInd).get(varInd)))==dimacsVar)
				{
					frequency++;
				}
			}
		}
		
		return frequency;
	}
	
	Matrix[][][] getTrainingDataActivationCopy(int numberSamples)
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
				float[][] outputFloats=new float[satProblem.getNumberVariables()][1];
				
				boolean oneNonzero=false;
				for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
				{
					floatActis[varInd][0]=(float)Math.log10(((double[])steps.get(stepInd)[4])[varInd]+1.0);
					outputFloats[varInd][0]=floatActis[varInd][0];
					if(floatActis[varInd][0]>0.0f)
					{
						oneNonzero=true;
					}
				}
				if(oneNonzero)
				{
					Matrix input=new FDMatrix(floatActis);
					inputs.add(new Matrix[]{input});
					
					//outputFloats[Math.abs(((int)steps.get(stepInd)[6]))-1][0]=Math.signum(((int)steps.get(stepInd)[6]));
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
	
	int stepsSize=0;
	
	Object[] getFarthestStep(List<Object[]> steps, int stepInd)
	{
		int compLevel=(int)(getLine(stepInd)[5]);
		Object[] aboveStep=null;
		for(int ind=stepInd; getLine(ind)!=null; ind++)
		{
			if(compLevel>(int)(getLine(ind)[5]))
			{
				aboveStep=steps.get(ind);
				break;
			}
			else if(compLevel==(int)(getLine(ind)[5]))
			{
				aboveStep=steps.get(ind);
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

class OutputProducer extends Thread
{
	
	Matrix[][] inputsArray;
	Matrix[][] outputsArray;
	List<Object[]> steps;
	int threadOffset;
	int numberThreads;
	public boolean done=false;
	int inputOffset;
	int numberSamples;
	int numberVariablesToInclude;
	SATProblemGenerator satProblem;
	List<boolean[]> results;
	
	public OutputProducer(Matrix[][] inputs, Matrix[][] outputs, 
			List<Object[]> steps, int threadOffset, int numberThreads, int inputOffset, int numberSamples,
			int numberVariablesToInclude, SATProblemGenerator satProblem, List<boolean[]> results)
	{
		this.inputsArray=inputs;
		this.outputsArray=outputs;
		this.steps=steps;
		this.threadOffset=threadOffset;
		this.numberThreads=numberThreads;
		this.inputOffset=inputOffset;
		this.numberSamples=numberSamples;
		this.numberVariablesToInclude=numberVariablesToInclude;
		this.satProblem=satProblem;
		this.results=results;
	}
	
	public void run()
	{
		for(int stepInd=threadOffset; stepInd<steps.size() && (inputOffset+stepInd)<numberSamples; stepInd+=numberThreads)
		{
			if((inputOffset+stepInd)%10==0)
			{
				System.out.println("Number of inputs: "+(inputOffset+stepInd));
			}
			
			float[][] floatActis=new float[((double[])steps.get(stepInd)[4]).length][1];
			float[][] outputFloats=new float[satProblem.getNumberVariables()][1];
			
			List<VariableActivation> actisVarList=new ArrayList<>();
			List<VariableActivation> clausesVarList=new ArrayList<>();
			int[] satChanges=getSatisfiedChange((int[])steps.get(stepInd)[7], (IVec<Constr>)steps.get(stepInd)[1], 
					(IVec<Constr>)steps.get(stepInd)[2], (Lits)steps.get(stepInd)[3]);
			for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
			{
				if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
				{
					actisVarList.add(new VariableActivation(varInd, 5.0f*(float)Math.pow(Math.log10(((double[])steps.get(stepInd)[4])[varInd]+1.0), 0.25)));
				}
				if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
				{
					clausesVarList.add(new VariableActivation(varInd, satChanges[varInd]));
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
			
			for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
			{
				if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
				{
					floatActis[varInd][0]=5.0f*(float)Math.pow(Math.log10(((double[])steps.get(stepInd)[4])[varInd]+1.1), 0.25);
				}
			}
			
			float[][] floatClauses=new float[((double[])steps.get(stepInd)[4]).length][1];
			int[] satChangesArr=getSatisfiedChange((int[])steps.get(stepInd)[7], (IVec<Constr>)steps.get(stepInd)[1], 
					(IVec<Constr>)steps.get(stepInd)[2], (Lits)steps.get(stepInd)[3]);
			for(int varInd=0; varInd<((double[])steps.get(stepInd)[4]).length; varInd++)
			{
				if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1)))
				{
					floatClauses[varInd][0]=satChangesArr[varInd];
				}
			}
			
			//0=unassigned in initial
			//1=unassigned in conflict clauses
			//2=# unsatisfied initial clauses
			//3=#unsatisfied conflict clauses
			//4+=var freq histogram				
			float[][] additionalInfo=new float[4+numberVariablesToInclude][1];
			
			float unsatInitialClauses=0;
			float unassignedInitialClausesVars=0;
			for(int initialClauseInd=0; initialClauseInd<((IVec<Constr>)steps.get(stepInd)[1]).size(); initialClauseInd++)
			{
				boolean clauseSat=false;
				float unassignedThisClause=0;
				for(int varInd=0; varInd<((IVec<Constr>)steps.get(stepInd)[1]).get(initialClauseInd).size(); varInd++)
				{
					if(((Lits)steps.get(stepInd)[3]).isSatisfied(((IVec<Constr>)steps.get(stepInd)[1]).get(initialClauseInd).get(varInd)))
					{
						clauseSat=true;
						break;
					}
					if(((Lits)steps.get(stepInd)[3]).isUnassigned(((IVec<Constr>)steps.get(stepInd)[1]).get(initialClauseInd).get(varInd)))
					{
						unassignedThisClause++;
					}
				}
				if(!clauseSat)
				{
					unsatInitialClauses++;
					unassignedInitialClausesVars+=unassignedThisClause;
					for(int varInd=0; varInd<((IVec<Constr>)steps.get(stepInd)[1]).get(initialClauseInd).size(); varInd++)
					{
						if(((Lits)steps.get(stepInd)[3]).isUnassigned(((IVec<Constr>)steps.get(stepInd)[1]).get(initialClauseInd).get(varInd))
								&& includedHeuristicVariables.contains(Math.abs(LiteralsUtils.toDimacs(((IVec<Constr>)steps.get(stepInd)[1]).get(initialClauseInd).get(varInd)))))
						{
							additionalInfo[4+includedHeuristicVariables.indexOf(Math.abs(LiteralsUtils.toDimacs(((IVec<Constr>)steps.get(stepInd)[1]).get(initialClauseInd).get(varInd))))][0]++;
						}
					}
				}
			}
			
			float unsatConflictClauses=0;
			float unassignedConflictClausesVars=0;
			for(int initialClauseInd=0; initialClauseInd<((IVec<Constr>)steps.get(stepInd)[2]).size(); initialClauseInd++)
			{
				boolean clauseSat=false;
				float unassignedThisClause=0;
				for(int varInd=0; varInd<((IVec<Constr>)steps.get(stepInd)[2]).get(initialClauseInd).size(); varInd++)
				{
					if(((Lits)steps.get(stepInd)[3]).isSatisfied(((IVec<Constr>)steps.get(stepInd)[2]).get(initialClauseInd).get(varInd)))
					{
						clauseSat=true;
						break;
					}
					if(((Lits)steps.get(stepInd)[3]).isUnassigned(((IVec<Constr>)steps.get(stepInd)[2]).get(initialClauseInd).get(varInd)))
					{
						unassignedThisClause++;
					}
				}
				if(!clauseSat)
				{
					unsatConflictClauses++;
					unassignedConflictClausesVars+=unassignedThisClause;
					for(int varInd=0; varInd<((IVec<Constr>)steps.get(stepInd)[2]).get(initialClauseInd).size(); varInd++)
					{
						if(((Lits)steps.get(stepInd)[3]).isUnassigned(((IVec<Constr>)steps.get(stepInd)[2]).get(initialClauseInd).get(varInd))
								&& includedHeuristicVariables.contains(LiteralsUtils.toDimacs(((IVec<Constr>)steps.get(stepInd)[2]).get(initialClauseInd).get(varInd))))
						{
							additionalInfo[4+includedHeuristicVariables.indexOf(LiteralsUtils.toDimacs(((IVec<Constr>)steps.get(stepInd)[2]).get(initialClauseInd).get(varInd)))][0]++;
						}
					}
				}
			}
			
			additionalInfo[0][0]=unsatInitialClauses/((IVec<Constr>)steps.get(stepInd)[1]).size();
			additionalInfo[1][0]=unassignedInitialClausesVars/((double[])steps.get(stepInd)[4]).length;
			additionalInfo[2][0]=unsatConflictClauses/((IVec<Constr>)steps.get(stepInd)[1]).size();
			additionalInfo[3][0]=unassignedConflictClausesVars/((double[])steps.get(stepInd)[4]).length;
			
			boolean actiBest=false;
			double dropChance=0.99;
			
			float[] correctChooseVars=new float[((double[])steps.get(stepInd)[4]).length];
			Object[] nextHighestStep=getFarthestStep(steps, stepInd);
			int numberCorrectChooseVars=0;
			if((int)nextHighestStep[5]<(int)steps.get(stepInd)[5])
			{
				List<Integer> addClauseVars=getNewConflictClauseVars((IVec<Constr>)steps.get(stepInd)[2],
						(IVec<Constr>)nextHighestStep[2]);						
				
				for(Integer variable: addClauseVars)
				{
					if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(Math.abs(variable))))
					{
						correctChooseVars[Math.abs(variable)]=1.0f;
						numberCorrectChooseVars++;
					}									
				}
			}
			else
			{
				
				if(results.get(stepInd)!=null)
				{
					for(int varInd=0; varInd<((double[])nextHighestStep[4]).length; varInd++)
					{
						try
						{
						if(((Lits)steps.get(stepInd)[3]).isUnassigned(LiteralsUtils.toInternal(varInd+1))
								&& ((((int[])steps.get(stepInd)[7])[varInd+1]%2==1 && !results.get(stepInd)[varInd]) ||
										(((int[])steps.get(stepInd)[7])[varInd+1]%2==0 && results.get(stepInd)[varInd])))
						{
							correctChooseVars[varInd]=1.0f;
							numberCorrectChooseVars++;
						}
						}
						catch(Exception e)
						{
							e.printStackTrace();
						}
					}
				}
			}
			
			
			int numberActi=0;
			int numberCC=0;
			int n=0;
			while(numberActi==numberCC
					&& n<((double[])steps.get(stepInd)[4]).length
					&& (numberActi<numberCorrectChooseVars || numberCC<numberCorrectChooseVars))
			{
				if(correctChooseVars[getNthHighest(floatActis, n)]==1)
				{
					numberActi++;
				}
				if(correctChooseVars[getNthHighest(floatClauses, n)]==1)
				{
					numberCC++;
				}
				n++;
			}
			if(numberActi>numberCC)
			{
				outputFloats=cloneFloatssToFloatss(inputFloatActis);
			}
			else if(numberActi<numberCC)
			{
				outputFloats=cloneFloatssToFloatss(inputFloatClauses);
			}
			else
			{
				if(Math.random()<0.5)
				{
					outputFloats=cloneFloatssToFloatss(inputFloatActis);
				}
				else
				{
					outputFloats=cloneFloatssToFloatss(inputFloatClauses);
				}
			}
			
			Matrix output=new FDMatrix(outputFloats);
			outputsArray[inputOffset+stepInd]=new Matrix[]{output};
			
			Matrix inputActis=new FDMatrix(inputFloatActis);
			Matrix inputAddInfo=new FDMatrix(additionalInfo);
			Matrix inputClauses=new FDMatrix(inputFloatClauses);
			inputsArray[inputOffset+stepInd]=new Matrix[]{inputActis, inputAddInfo, inputClauses};			
		}
		done=true;
	}
	
	public static int[] getSatisfiedChange(int[] phase, IVec<Constr> initialConstrs, IVec<Constr> learnedConstrs, Lits lits)
	{
		int[] satChanges=new int[phase.length];

		for(int constrInd=0; constrInd<initialConstrs.size(); constrInd++)
		{
			boolean unsat=true;
			for(int varInd=0; varInd<initialConstrs.get(constrInd).size(); varInd++)
			{
				if(lits.isSatisfied(initialConstrs.get(constrInd).get(varInd)))
				{
					unsat=false;
				}
			}
			if(unsat)
			{
				for(int varInd=0; varInd<initialConstrs.get(constrInd).size(); varInd++)
				{
					if(initialConstrs.get(constrInd).get(varInd)==phase[Math.abs(LiteralsUtils.toDimacs(initialConstrs.get(constrInd).get(varInd)))]
							&& lits.isUnassigned(initialConstrs.get(constrInd).get(varInd)))
					{
						satChanges[Math.abs(LiteralsUtils.toDimacs(initialConstrs.get(constrInd).get(varInd)))]++;
					}
				}
			}
		}
		
		/*
		for(int constrInd=0; constrInd<learnedConstrs.size(); constrInd++)
		{
			for(int varInd=0; varInd<learnedConstrs.get(constrInd).size(); varInd++)
			{
				if(learnedConstrs.get(constrInd).get(varInd)==internalLit)
				{
					numberSatisfiedClauses++;
				}
			}
		}
		*/
		
		for(int constrInd=0; constrInd<learnedConstrs.size(); constrInd++)
		{
			boolean unsat=true;
			for(int varInd=0; varInd<learnedConstrs.get(constrInd).size(); varInd++)
			{
				if(lits.isSatisfied(learnedConstrs.get(constrInd).get(varInd)))
				{
					unsat=false;
				}
			}
			if(unsat)
			{
				for(int varInd=0; varInd<learnedConstrs.get(constrInd).size(); varInd++)
				{
					if(learnedConstrs.get(constrInd).get(varInd)==phase[Math.abs(LiteralsUtils.toDimacs(learnedConstrs.get(constrInd).get(varInd)))]
							&& lits.isUnassigned(learnedConstrs.get(constrInd).get(varInd)))
					{
						satChanges[Math.abs(LiteralsUtils.toDimacs(learnedConstrs.get(constrInd).get(varInd)))]++;
					}
				}
			}
		}
		
		return satChanges;
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
	
	Object[] getFarthestStep(List<Object[]> steps, int stepInd)
	{
		int compLevel=(int)(steps.get(stepInd)[5]);
		Object[] aboveStep=null;
		for(int ind=stepInd; ind<steps.size(); ind++)
		{
			if(compLevel>(int)(steps.get(ind)[5]))
			{
				aboveStep=steps.get(ind);
				break;
			}
			else if(compLevel==(int)(steps.get(ind)[5]))
			{
				aboveStep=steps.get(ind);
			}
		}
		return aboveStep;
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
	
	public static int getNthHighest(float[][] values, int n)
	{
		float[] valuesCopy=cloneFloatss(values);
		Arrays.sort(valuesCopy);
		for(int ind=0; ind<values.length; ind++)
		{
			if(values[ind][0]==valuesCopy[n])
			{
				return ind;
			}
		}
		
		/*
		int highestInd=-1;
		for(int r=0; r<=n; r++)
		{
			highestInd=-1;
			float highestValues=Float.NEGATIVE_INFINITY;
			for(int ind=0; ind<valuesCopy.length; ind++)
			{
				if(valuesCopy[ind]>highestValues)
				{
					highestValues=valuesCopy[ind];
					highestInd=ind;
				}
			}
			valuesCopy[highestInd]=Float.NEGATIVE_INFINITY;
		}
		return highestInd;
		*/
		return -1;
	}
	
	public static float[] cloneFloatss(float[][] floatss)
	{
		float[] floats=new float[floatss.length];
		for(int ind=0; ind<floats.length; ind++)
		{
			floats[ind]=floatss[ind][0];
		}
		return floats;
	}
	
	public static float[][] cloneFloatssToFloatss(float[][] floatss)
	{
		float[][] floats=new float[floatss.length][1];
		for(int ind=0; ind<floats.length; ind++)
		{
			floats[ind][0]=floatss[ind][0];
		}
		return floats;
	}
	
}
