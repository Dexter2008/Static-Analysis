/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import fj.test.Bool;
import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import soot.jimple.IfStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        //ControlFlow Unreachable Code && Unreachable Branch
        Stmt entry=cfg.getEntry();
        HashSet<Stmt>visited=new HashSet<Stmt>();
        Set<Stmt>unreachable =new HashSet<>(cfg.getNodes());//unvisited
        DFS(cfg,entry,visited,constants,unreachable);
        deadCode.addAll(unreachable);

        //Dead Variable
        HashSet<Stmt>deadvar=new HashSet<Stmt>();
        DeadAssign(cfg,liveVars,deadvar);
        deadCode.addAll(deadvar);
        deadCode.remove(cfg.getExit());
        return deadCode;
    }

    public void DFS(CFG<Stmt>cfg,Stmt cur,HashSet<Stmt>visited,
                    DataflowResult<Stmt,CPFact> constants,Set<Stmt>unvisited){
        if(visited.contains(cur))return;
        visited.add(cur);
        unvisited.remove(cur);
        Set<Stmt>Succs=new HashSet<>(cfg.getSuccsOf(cur));
        if(cur instanceof If){
            Set<Edge<Stmt>>curOutEdges=cfg.getOutEdgesOf(cur);
            Value res=ConstantPropagation.evaluate(((If) cur).getCondition(),constants.getInFact(cur));
            if (res.isConstant()){
                if(res.getConstant()==1) {
                    for (Edge<Stmt> edge : curOutEdges) {
                        if(edge.getKind()==Edge.Kind.IF_FALSE)Succs.remove(edge.getTarget());
                    }
                } else if (res.getConstant()==0) {
                    for (Edge<Stmt> edge : curOutEdges) {
                        if(edge.getKind()==Edge.Kind.IF_TRUE)Succs.remove(edge.getTarget());
                    }
                }
            }
        } else if (cur instanceof SwitchStmt) {
            Set<Edge<Stmt>>curOutEdges=cfg.getOutEdgesOf(cur);
            Value var=ConstantPropagation.evaluate(((SwitchStmt) cur).getVar(),constants.getInFact(cur));
            if(var.isConstant()){
                boolean flag=false;//false代表进DefaultCase
                for(Edge<Stmt> edge:curOutEdges){
                    if(edge.isSwitchCase()){
                        if(edge.getCaseValue()!=var.getConstant())Succs.remove(edge.getTarget());
                        else flag=true;
                    }
                }
                if(flag)Succs.remove(((SwitchStmt) cur).getDefaultTarget());
            }
        }
        for(Stmt next:Succs){
         if(!visited.contains(next))DFS(cfg,next,visited,constants,unvisited);
        }
    }

    public void DeadAssign(CFG<Stmt>cfg,DataflowResult<Stmt,SetFact<Var>>liveVars,HashSet<Stmt>deadvar){
        for(Stmt cur:cfg){
            if(cur instanceof AssignStmt<?,?>){
                if(cur.getDef().isPresent()&&cur.getDef().get() instanceof Var){
                    if(!liveVars.getOutFact(cur).contains((Var)cur.getDef().get())
                            && hasNoSideEffect(((AssignStmt<?,?>) cur).getRValue())){
                        deadvar.add(cur);
                    }
                }
            }
        }
    }
    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
