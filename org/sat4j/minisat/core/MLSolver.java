/*******************************************************************************
 * SAT4J: a SATisfiability library for Java Copyright (C) 2004-2008 Daniel Le Berre
 *
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Alternatively, the contents of this file may be used under the terms of
 * either the GNU Lesser General Public License Version 2.1 or later (the
 * "LGPL"), in which case the provisions of the LGPL are applicable instead
 * of those above. If you wish to allow use of your version of this file only
 * under the terms of the LGPL, and not to allow others to use your version of
 * this file under the terms of the EPL, indicate your decision by deleting
 * the provisions above and replace them with the notice and other provisions
 * required by the LGPL. If you do not delete the provisions above, a recipient
 * may use your version of this file under the terms of the EPL or the LGPL.
 * 
 * Based on the original MiniSat specification from:
 * 
 * An extensible SAT solver. Niklas Een and Niklas Sorensson. Proceedings of the
 * Sixth International Conference on Theory and Applications of Satisfiability
 * Testing, LNCS 2919, pp 502-518, 2003.
 *
 * See www.minisat.se for the original solver in C++.
 * 
 * The reason simplification methods are coming from MiniSAT 1.14 released under 
 * the MIT license:
 * MiniSat -- Copyright (c) 2003-2005, Niklas Een, Niklas Sorensson
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the
 * "Software"), to deal in the Software without restriction, including
 * without limitation the rights to use, copy, modify, merge, publish,
 * distribute, sublicense, and/or sell copies of the Software, and to
 * permit persons to whom the Software is furnished to do so, subject to
 * the following conditions:
 *
 * The above copyright notice and this permission notice shall be included
 * in all copies or substantial portions of the Software.
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 * OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE. 
 *******************************************************************************/
package org.sat4j.minisat.core;

import static org.sat4j.core.LiteralsUtils.toDimacs;
import static org.sat4j.core.LiteralsUtils.var;

import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.Serializable;
import java.lang.reflect.Field;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Timer;
import java.util.TimerTask;

import org.sat4j.core.ConstrGroup;
import org.sat4j.core.LiteralsUtils;
import org.sat4j.core.Vec;
import org.sat4j.core.VecInt;
import org.sat4j.specs.Constr;
import org.sat4j.specs.ContradictionException;
import org.sat4j.specs.IConstr;
import org.sat4j.specs.ISolver;
import org.sat4j.specs.IVec;
import org.sat4j.specs.IVecInt;
import org.sat4j.specs.IteratorInt;
import org.sat4j.specs.Lbool;
import org.sat4j.specs.SearchListener;
import org.sat4j.specs.TimeoutException;
import org.sat4j.minisat.orders.MLVarOrderHeap;

/**
 * The backbone of the library providing the modular implementation of a MiniSAT
 * (Chaff) like solver.
 * 
 * @author leberre
 */
public class MLSolver<D extends DataStructureFactory> extends Solver{

	public MLSolver(LearningStrategy learner, DataStructureFactory dsf, IOrder order, RestartStrategy restarter) {
		super(learner, dsf, order, restarter);
	}

	public byte[][] levelVariables;
	final int maxNNSize=4096;
	
	Lbool search(IVecInt assumps) 
	{
		((MLVarOrderHeap)this.order).numberContrs=constrs.size();
		levelVariables=new byte[2000][50000];
		
        assert this.rootLevel == decisionLevel();
        this.stats.starts++;
        int backjumpLevel;

        // varDecay = 1 / params.varDecay;
        this.order.setVarDecay(1 / this.params.getVarDecay());
        this.claDecay = 1 / this.params.getClaDecay();

        do {
            this.slistener.beginLoop();
            // propagate unit clauses and other constraints
            Constr confl = propagate();
            assert this.trail.size() == this.qhead;

            if (confl == null) {
                // No conflict found
                if (decisionLevel() == 0 && this.isDBSimplificationAllowed) {
                    this.stats.rootSimplifications++;
                    boolean ret = simplifyDB();
                    assert ret;
                }
                assert nAssigns() <= this.voc.realnVars();
                if (nAssigns() == this.voc.realnVars()) 
                {
                    modelFound();
                    this.slistener.solutionFound((this.fullmodel != null)
                            ? this.fullmodel : this.model, this);
                    if (this.sharedConflict == null) 
                    {
                        cancelUntil(this.rootLevel);
                        return Lbool.TRUE;
                    } 
                    else 
                    {
                        // this.sharedConflict;
                        if (decisionLevel() == rootLevel) 
                        {
                            confl = this.sharedConflict;
                            this.sharedConflict = null;
                        } 
                        else
                        {
                            int level = this.sharedConflict
                                    .getAssertionLevel(trail, decisionLevel());
                            cancelUntilTrailLevel(level);
                            this.qhead = this.trail.size();
                            this.sharedConflict.assertConstraint(this);
                            this.sharedConflict = null;

                            continue;
                        }
                    }
                } 
                else
                {
                    if (this.restarter.shouldRestart())
                    {
                        cancelUntil(this.rootLevel);
                        return Lbool.UNDEFINED;
                    }
                    if (this.needToReduceDB)
                    {
                        reduceDB();
                        this.needToReduceDB = false;
                    }
                    if (this.sharedConflict == null) 
                    {
                        // New variable decision
                        this.stats.decisions++;
                        int p=-1;
                        if(false)
                        {
                        	p=this.order.select();
                        }
                        else
                        {
                        	p = ((MLVarOrderHeap)order).select(levelVariables[decisionLevel()]);
                        	if(levelVariables[decisionLevel()][Math.abs(LiteralsUtils.toDimacs(p))-1]==0)
            				{
                        		levelVariables[decisionLevel()][Math.abs(LiteralsUtils.toDimacs(p))-1]=(byte)-Math.signum(p);
            				}
            				else
            				{
            					levelVariables[decisionLevel()][Math.abs(LiteralsUtils.toDimacs(p))-1]=-2;
            				}
                        	//System.out.println("mlj: "+LiteralsUtils.toDimacs(p));
                        }
                        if (p == ILits.UNDEFINED)
                        {
                            // check (expensive) if all the constraints are not
                            // satisfied
                            boolean allsat = true;
                            for (int i = 0; i < this.constrs.size(); i++) 
                            {
                                if (!((Constr)this.constrs.get(i)).isSatisfied()) 
                                {
                                    allsat = false;
                                    break;
                                }
                            }
                            if (allsat) 
                            {
                                modelFound();
                                this.slistener.solutionFound(
                                        (this.fullmodel != null)
                                                ? this.fullmodel : this.model,
                                        this);
                                return Lbool.TRUE;
                            } else 
                            {
                                confl = preventTheSameDecisionsToBeMade();
                                this.lastConflictMeansUnsat = false;
                            }
                        } 
                        else 
                        {
                            assert p > 1;
                            this.slistener.assuming(toDimacs(p));
                            boolean ret = assume(p);
                            assert ret;
                        }
                    } 
                    else 
                    {
                        confl = this.sharedConflict;
                        this.sharedConflict = null;
                    }
                }
            }
            if (confl != null) 
            {
                // conflict found
                this.stats.conflicts++;
                this.slistener.conflictFound(confl, decisionLevel(),
                        this.trail.size());
                this.conflictCount.newConflict();

                if (decisionLevel() == this.rootLevel) 
                {
                    if (this.lastConflictMeansUnsat) 
                    {
                        // conflict at root level, the formula is inconsistent
                        this.unsatExplanationInTermsOfAssumptions = analyzeFinalConflictInTermsOfAssumptions(
                                confl, assumps, ILits.UNDEFINED);
                        return Lbool.FALSE;
                    }
                    return Lbool.UNDEFINED;
                }
                int conflictTrailLevel = this.trail.size();
                // analyze conflict
                try 
                {
                    analyze(confl, this.analysisResult);
                }
                catch (TimeoutException e) 
                {
                    return Lbool.UNDEFINED;
                }
                assert this.analysisResult.backtrackLevel < decisionLevel();
                backjumpLevel = Math.max(this.analysisResult.backtrackLevel,
                        this.rootLevel);
                this.slistener.backjump(backjumpLevel);
                
                while(decisionLevel()>backjumpLevel)
				{
					if (decisionLevel() == rootLevel) 
					{
						return Lbool.FALSE;
					}
					
					levelVariables[decisionLevel()]=new byte[levelVariables[decisionLevel()].length];
					slistener.backjump(decisionLevel()-1);
					cancelUntil(decisionLevel()-1);
					//System.out.println("mlj: backjump");
				} 
                
                if (backjumpLevel == this.rootLevel) 
                {
                    this.restarter.onBackjumpToRootLevel();
                }
                assert decisionLevel() >= this.rootLevel
                        && decisionLevel() >= this.analysisResult.backtrackLevel;
                if (this.analysisResult.reason == null)
                {
                    return Lbool.FALSE;
                }
                record(this.analysisResult.reason);
                this.restarter.newLearnedClause(this.analysisResult.reason,
                        conflictTrailLevel);
                this.analysisResult.reason = null;
                decayActivities();
            }
        } 
        while (this.undertimeout);
        return Lbool.UNDEFINED; // timeout occured
    }
	
	/*
	Lbool search(IVecInt assumps) 
	{
		((MLVarOrderHeap)this.order).numberContrs=constrs.size();
		levelVariables=new byte[2000][50000];
		
        assert this.rootLevel == decisionLevel();
        int backjumpLevel;


        do 
        {
            Constr confl = propagate();

            if (confl == null) 
            {
                assert nAssigns() <= this.voc.realnVars();
                if (nAssigns() == this.voc.realnVars()) 
                {
                    modelFound();
                    return Lbool.TRUE;
                } 
                else
                {
                        int p=-1;
                    	p = ((MLVarOrderHeap)order).select(levelVariables[decisionLevel()]);
                    	if(levelVariables[decisionLevel()][Math.abs(LiteralsUtils.toDimacs(p))-1]==0)
        				{
                    		levelVariables[decisionLevel()][Math.abs(LiteralsUtils.toDimacs(p))-1]=(byte)-Math.signum(LiteralsUtils.toDimacs(p));
        				}
        				else
        				{
        					levelVariables[decisionLevel()][Math.abs(LiteralsUtils.toDimacs(p))-1]=-2;
        				}
                    	System.out.println("s4j: "+LiteralsUtils.toDimacs(p));
                        boolean ret = assume(p);
                }
            }
            if (confl != null) 
            {
            	System.out.println("s4j: bj");
                if (decisionLevel() == this.rootLevel) 
                {
                    return Lbool.FALSE;
                }
                
				levelVariables[decisionLevel()]=new byte[levelVariables[decisionLevel()].length];
				slistener.backjump(decisionLevel()-1);
				cancelUntil(decisionLevel()-1);				
            }
        } 
        while (this.undertimeout);
        return Lbool.UNDEFINED; // timeout occured
    }
	*/
}
