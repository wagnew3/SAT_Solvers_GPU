package test;

import java.io.File;

public class GenCBMCScript 
{
	
	public static void main(String[] args)
	{
		/*
		File floatsFile=new File("/home/willie/workspace/SAT_Solvers_GPU/data/software_verification_problems/sv-benchmarks-svcomp15/c/float-benchs");
		int ctr=0;
		int mod=1;
		for(File problemFile: floatsFile.listFiles())
		{
			if(problemFile.getName().contains(".c"))
			{
				if(ctr%mod==0)
				{
					System.out.println("./cbmc --unwind 100 --dimacs --outfile /home/willie/Software_Verification/cbmc-cbmc-5.4/generated_sat_problems_floats_100/"+(ctr/mod)+".cnf "+problemFile.getAbsolutePath());
				}
				ctr++;
			}
		}
		
		System.out.println();		
		for(int i=0; i<ctr; i+=2)
		{
			if(i!=42 && i!=30)
			{
				System.out.println("./glucose -cpu-lim=300 /home/willie/Software_Verification/cbmc-cbmc-5.4/generated_sat_problems_floats_100/"+i+".cnf");
			}
		}
		*/
		System.out.println();
		for(int i=0; i<123; i++)
		{
			//System.out.println("./maplesat -cpu-lim=600 /home/willie/Software_Verification/cbmc-cbmc-5.4/minisat-2.2.1/PIndusFixConfClausesInformed9086c2200v9a100000ns"+i+".cnf");
			System.out.println("./maplesat -cpu-lim=60 /home/willie/Software_Verification/cbmc-cbmc-5.4/minisat-2.2.1/PIndusFixConfClausesInformed6065c1650v9a750000ns"+i+".cnf");
		}
		
	}

}
