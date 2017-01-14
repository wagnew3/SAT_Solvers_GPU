package test;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.text.DecimalFormat;
import java.text.NumberFormat;
import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

public class ProcessLRMToRNNData 
{
	
	static String fileName="/home/willie/workspace/SAT_Solvers_GPU/data/trainingData/LRBPI6065Recurrent";
	static String saveName="/home/willie/workspace/TensorFlow/data/LRBPI6065.csv";
	static int numberExamples=100000000;
	
	public static void main(String[] args) throws IOException
	{
		BufferedReader bIn=new BufferedReader(new FileReader(new File(fileName)));
		List<String> lines=new ArrayList<>();
		
		int examples=0;
		int numS=0;
		while(examples<numberExamples && bIn.ready())
		{
			lines.add(bIn.readLine());
			if(lines.get(lines.size()-1).equals("E"))
			{
				examples++;
			}
			else if(lines.get(lines.size()-1).equals("S"))
			{
				numS++;
			}
			if(numS>1)
			{
				break;
			}
		}
		bIn.close();
		System.out.println(examples+" examples");
		
		NumberFormat formatter=new DecimalFormat("#0.0000000000000");
		BufferedWriter bOut=new BufferedWriter(new FileWriter(new File(saveName)));
		Hashtable<String, List<String>> variableInfos=new Hashtable<>();
		boolean lastWasV=false;
		boolean lastWasVarName=false;
		String varName="";
		String input="";
		double maxReward=0.0;
		for(int exampleInd=0; exampleInd<lines.size(); exampleInd++)
		{
			if(lines.get(exampleInd).contains("S"))
			{
				for(String key: variableInfos.keySet())
				{
					bOut.write("n\n");
					for(int variableInfoInd=0; variableInfoInd<variableInfos.get(key).size()-1; variableInfoInd++)
					{
						bOut.write(variableInfos.get(key).get(variableInfoInd)+"\n");
					}
				}
				variableInfos=new Hashtable<>();
				lastWasV=true;
			}
			else if(lines.get(exampleInd).equals("V"))
			{
				lastWasV=true;
			}
			else if(lastWasV)
			{
				varName=lines.get(exampleInd);
				
				if(variableInfos.get(varName)==null)
				{
					variableInfos.put(varName, new ArrayList<>());
				}
				lastWasV=false;
				lastWasVarName=true;
			}
			else if(lastWasVarName)
			{
				if(!variableInfos.get(varName).isEmpty())
				{
					double reward=Double.parseDouble(lines.get(exampleInd));
					if(reward>maxReward)
					{
						maxReward=reward;
					}
					variableInfos.get(varName).add(lines.get(exampleInd));
				}
				lastWasVarName=false;
			}
			else if(!lines.get(exampleInd).equals("R") && !lines.get(exampleInd).equals("F") && !lines.get(exampleInd).equals("E"))
			{
				input+=lines.get(exampleInd)+",";
			}
			else if(lines.get(exampleInd).equals("E"))
			{
				variableInfos.get(varName).add(input.substring(0, input.length()-1));
				input="";
			}	
		}
		bOut.close();
	}

}
