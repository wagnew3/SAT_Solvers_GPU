package SATProblemGeneration;

import SATProblem.SAT;

public abstract class SATProblemGenerator 
{
    
    public abstract SAT generateSAT();
    
    public abstract int getNumberVariables();
    
    public abstract int getNumberClauses();

}
