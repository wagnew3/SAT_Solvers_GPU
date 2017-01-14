package SATSolver;

import java.util.List;

import SATProblem.Clause;
import SATProblem.SAT;
import SATProblem.Variable;

public abstract class SATSolver 
{
    
	public int numberSteps;
	
    protected abstract List<Integer> setVars(SAT sat);
    
    //return null to indicate no more SAT problems to backtrack to
    protected abstract SAT backtrack(SAT sat);
    
    protected abstract SAT init(SAT sat);
    
    //[0]=sat, [1]=variables
    public Object[] solve(SAT sat)
    {
    	numberSteps=0;
		SAT currentSAT=init(sat);
		int SATState=0;
    	int state=-2;
    	int ssp=0;
		while(currentSAT!=null)
		{
			numberSteps++;
		    SAT imSAT=currentSAT.cloneSAT();
		    imSAT.parent=currentSAT;
		    
		    ssp=sat.isSAT();
		    imSAT.setVariables=(setVars(imSAT));
		    
		    SATState=sat.isSAT();
		    if(SATState==1)
		    {
		    	if(sat.isSAT()!=1)
		    	{
		    		int u=0;
		    	}
				return new Object[]{sat, imSAT.variables};
		    }
		    else if(SATState==0)
		    {
				imSAT=unitPropogation(imSAT);
				currentSAT=imSAT;
				SATState=sat.isSAT();
				if(SATState==1)
			    {
					return new Object[]{sat, imSAT.variables};
			    }
		    }
		    if(SATState==-1 || !imSAT.unsetVariables() || imSAT.clauses.isEmpty())
		    {
		    	currentSAT=imSAT;
		    	do
		    	{
					currentSAT=backtrack(currentSAT);
					if(currentSAT!=null)
					{
						System.out.println("ms: bj");
					    backtrackVariableSets(imSAT, currentSAT);
					    state=sat.isSAT();
					}
		    	}
		    	while(currentSAT!=null &&
		    			(state==-1 || !currentSAT.unsetVariables() || currentSAT.clauses.isEmpty()));
		    }
		}
		return new Object[]{sat, sat.variables};
    }
    
    protected SAT backtrackVariableSets(SAT child, SAT parent)
    {
	while(!parent.equals(child))
	{
	    for(Integer variableInd: child.setVariables)
	    {
	    	System.out.println("ms: unset "+variableInd);
	    	parent.variables.get(variableInd).value=0;
	    }
	    child=child.parent;
	}
	return parent;
    }
    
    protected SAT unitPropogation(SAT sat)
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
	        		sat.setVariables.add(sat.variableLoc.get(currentClause.variables.get(0)));
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

}
