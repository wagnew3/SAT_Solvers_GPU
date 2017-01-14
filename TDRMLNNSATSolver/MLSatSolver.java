package TDRMLNNSATSolver;

import java.util.ArrayList;
import java.util.List;

import SATProblem.SAT;
import SATSolver.DPLL;
import SATSolver.SATSolver;

public class MLSatSolver extends DPLL
{

    @Override
    protected List<Integer> setVars(SAT sat) 
    {
	Object[] changeState=changeVariableStates.get(sat.parent);
	if(changeState==null)
	{
	    	int startInd=(int)(sat.variables.size()*Math.random());
        	while(sat.variables.get(startInd).value!=0)
        	{
        	    startInd=((startInd+1)%sat.variables.size());
        	}
        	
        	Object[] newChangeState=new Object[2];
        	newChangeState[0]=startInd;
        	if(Math.random()<0.5)
        	{
        	    newChangeState[1]=-1;
        	}
        	else
        	{
        	    newChangeState[1]=1;
        	}
        	changeVariableStates.put(sat.parent, newChangeState);
        	sat.variables.get(startInd).value=(int)newChangeState[1];
        	List<Integer> changeVariables=new ArrayList<>();
        	changeVariables.add(startInd);
        	
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
	    if((int)changeState[1]==1)
	    {
		int u=0;
	    }
	   	sat.variables.get((int)changeState[0]).value=(int)changeState[1];
	   	changeState[1]=-2;
        	List<Integer> changeVariables=new ArrayList<>();
        	changeVariables.add((int)changeState[0]);
        	return changeVariables;
	}
	
    }

}
