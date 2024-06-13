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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import org.checkerframework.common.returnsreceiver.qual.This;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;
import soot.jimple.parser.node.AEntermonitorStatement;
import soot.jimple.parser.node.Switch;

import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if(!this.callGraph.contains(method)){
            this.callGraph.addReachableMethod(method);
            for(Stmt s:method.getIR().getStmts()){
                s.accept(this.stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            VarPtr x=pointerFlowGraph.getVarPtr(stmt.getLValue());
            workList.addEntry(x,new PointsToSet(heapModel.getObj(stmt)));
            return null;
        }
        @Override
        public Void visit(Copy stmt) {
            VarPtr x=pointerFlowGraph.getVarPtr(stmt.getLValue());
            VarPtr y=pointerFlowGraph.getVarPtr(stmt.getRValue());
            addPFGEdge(y,x);
            return null;
        }
        @Override
        public Void visit(Invoke stmt) {
            Invoke callsite=stmt;
            if(callsite.isStatic()){
                JMethod m=resolveCallee(null,callsite);
                if(callGraph.addEdge(new Edge<>(CallKind.STATIC,callsite,m))){
                    addReachable(m);
                    for(int i=0;i<m.getParamCount();i++){
                        Var ai=callsite.getRValue().getArg(i);
                        Var pi=m.getIR().getParam(i);
                        addPFGEdge(pointerFlowGraph.getVarPtr(ai),pointerFlowGraph.getVarPtr(pi));
                    }
                    Var r=callsite.getLValue();
                    if(r!=null) {
                        for (int i = 0; i < m.getIR().getReturnVars().size(); i++) {
                            Var mreti=m.getIR().getReturnVars().get(i);
                            addPFGEdge(pointerFlowGraph.getVarPtr(mreti),pointerFlowGraph.getVarPtr(r));
                        }
                    }
                }
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic()){
                JField field = stmt.getFieldRef().resolve();
                Var y = stmt.getLValue();
                addPFGEdge(pointerFlowGraph.getStaticField(field), pointerFlowGraph.getVarPtr(y));
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if(stmt.isStatic()){
                JField field = stmt.getFieldRef().resolve();
                Var y = stmt.getRValue();
                addPFGEdge(pointerFlowGraph.getVarPtr(y), pointerFlowGraph.getStaticField(field));
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(this.pointerFlowGraph.addEdge(source,target)){
            if(!source.getPointsToSet().isEmpty()){
                workList.addEntry(target,source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()){
            WorkList.Entry entry=workList.pollEntry();
            Pointer pointer= entry.pointer();
            PointsToSet differ=this.propagate(pointer,entry.pointsToSet());
            if(pointer instanceof VarPtr n){
                Var x=n.getVar();
                for(Obj obj:differ) {
                    for (StoreField stmt : x.getStoreFields()) {
                        assert(!stmt.isStatic());
                        if(stmt.isStatic()){
                            JField field = stmt.getFieldRef().resolve();
                            Var y = stmt.getRValue();
                            this.addPFGEdge(pointerFlowGraph.getVarPtr(y), pointerFlowGraph.getStaticField(field));
                        }
                        else{
                            JField field = stmt.getFieldRef().resolve();
                            Var y = stmt.getRValue();
                            this.addPFGEdge(pointerFlowGraph.getVarPtr(y), pointerFlowGraph.getInstanceField(obj, field));
                        }
                    }
                    for (LoadField stmt : x.getLoadFields()) {
                        assert(!stmt.isStatic());
                        if(stmt.isStatic()){
                           JField field = stmt.getFieldRef().resolve();
                           Var y = stmt.getLValue();
                           this.addPFGEdge(pointerFlowGraph.getStaticField(field), pointerFlowGraph.getVarPtr(y));
                        }
                        else{
                           JField field = stmt.getFieldRef().resolve();
                           Var y = stmt.getLValue();
                           this.addPFGEdge(pointerFlowGraph.getInstanceField(obj, field), pointerFlowGraph.getVarPtr(y));
                        }
                    }
                    for (StoreArray stmt : x.getStoreArrays()) {
                        Var y = stmt.getRValue();
                        this.addPFGEdge(pointerFlowGraph.getVarPtr(y), pointerFlowGraph.getArrayIndex(obj));
                    }
                    for (LoadArray stmt : x.getLoadArrays()) {
                        Var y = stmt.getLValue();
                        this.addPFGEdge(pointerFlowGraph.getArrayIndex(obj), pointerFlowGraph.getVarPtr(y));
                    }
                    this.processCall(x, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet differ=new PointsToSet();
        if(!pointsToSet.isEmpty()){
            PointsToSet ptn=pointer.getPointsToSet();
            for(Obj obj:pointsToSet) {
                if (!ptn.contains(obj)) {
                    ptn.addObject(obj);
                    differ.addObject(obj);
                }
            }
            Set<Pointer> succs=this.pointerFlowGraph.getSuccsOf(pointer);
            for(Pointer succ:succs){
                workList.addEntry(succ,differ);
            }
        }
        return differ;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for(Invoke callsite:var.getInvokes()){
            assert (!callsite.isStatic());
            JMethod m = this.resolveCallee(recv, callsite);
            workList.addEntry(pointerFlowGraph.getVarPtr(m.getIR().getThis()),new PointsToSet(recv));
            CallKind kind=null;
            if(callsite.isVirtual()){
                kind=CallKind.VIRTUAL;
            } else if (callsite.isStatic()) {
                kind=CallKind.STATIC;
            } else if (callsite.isInterface()) {
                kind=CallKind.INTERFACE;
            } else if (callsite.isSpecial()) {
                kind=CallKind.SPECIAL;
            } else if (callsite.isDynamic()) {
                kind=CallKind.DYNAMIC;
            }
            if(callGraph.addEdge(new Edge<>(kind,callsite,m))){
                this.addReachable(m);
                for(int i=0;i<m.getParamCount();i++){
                    Var ai=callsite.getRValue().getArg(i);
                    Var pi=m.getIR().getParam(i);
                    this.addPFGEdge(pointerFlowGraph.getVarPtr(ai),pointerFlowGraph.getVarPtr(pi));
                }
                Var r=callsite.getLValue();
                if(r!=null) {
                    for (int i = 0; i < m.getIR().getReturnVars().size(); i++) {
                        Var mreti=m.getIR().getReturnVars().get(i);
                        this.addPFGEdge(pointerFlowGraph.getVarPtr(mreti),pointerFlowGraph.getVarPtr(r));
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
