package SATSolver;

import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;

import SATProblem.SAT;
import SATProblem.Variable;

public class DPLL extends SATSolver
{

    //[0]=variableIndex, [1]=setValueTo, if -2 then backtrack past parent
    protected Hashtable<SAT, Object[]> changeVariableStates;
    int varInd=0;
    
    @Override
    protected List<Integer> setVars(SAT sat) 
    {
		Object[] changeState=changeVariableStates.get(sat.parent);
		if(changeState==null)
		{
	    	int startInd=(int)(sat.variables.size()*Math.random());
	    	while(sat.variables.get(startInd).value!=0
	    			|| sat.variableFreq.get(sat.variables.get(startInd))==null)
	    	{
	    	    startInd=((startInd+1)%sat.variables.size());
	    	    sat.isSAT();
	    	    sat=unitPropogation(sat);
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
		   	sat.variables.get((int)changeState[0]).value=(int)changeState[1];
		   	changeState[1]=-2;
        	List<Integer> changeVariables=new ArrayList<>();
        	changeVariables.add((int)changeState[0]);
        	return changeVariables;
		}
    }

    @Override
    protected SAT backtrack(SAT sat) 
    {
		sat=sat.parent;
		if(sat==null)
	    {
	    	return null;
	    }
		Object[] changeState;
		while((int)(changeState=changeVariableStates.get(sat))[1]==-2)
		{
		    sat=sat.parent;
		    if(sat==null)
		    {
		    	return null;
		    }
		}
		return sat;
    }

    @Override
    protected SAT init(SAT sat) 
    {
    	varInd=0;
		changeVariableStates=new Hashtable<>();
		return sat;
    }

}
