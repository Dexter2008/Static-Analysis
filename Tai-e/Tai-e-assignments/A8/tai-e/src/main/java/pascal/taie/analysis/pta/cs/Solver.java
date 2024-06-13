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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.CloseableThreadContext;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if(!this.callGraph.contains(csMethod)){
            this.callGraph.addReachableMethod(csMethod);
            for(Stmt s:csMethod.getMethod().getIR().getStmts()){
                s.accept(new StmtProcessor(csMethod));
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        public Void visit(New stmt) {
            Pointer x=csManager.getCSVar(context,stmt.getLValue());
            Obj obj=heapModel.getObj((stmt));
            Context obj_context=contextSelector.selectHeapContext(csMethod,obj);
            CSObj csobj= csManager.getCSObj(obj_context,obj);
            PointsToSet pts=PointsToSetFactory.make(csobj);
            workList.addEntry(x,pts);
            return null;
        }
        @Override
        public Void visit(Copy stmt) {
            CSVar x=csManager.getCSVar(context,stmt.getLValue());
            CSVar y=csManager.getCSVar(context,stmt.getRValue());
            addPFGEdge(y,x);
            return null;
        }
        @Override
        public Void visit(Invoke stmt) {
            CSCallSite cscallsite=csManager.getCSCallSite(context,stmt);
            if(stmt.isStatic()){
                JMethod m=resolveCallee(null,stmt);
                Context ct=contextSelector.selectContext(cscallsite,m);
                CSMethod csm=csManager.getCSMethod(ct,m);
                if(callGraph.addEdge(new Edge<>(CallKind.STATIC,cscallsite,csm))){
                    addReachable(csm);
                    taintAnalysis.taint_addTPFGedge(cscallsite, csm);
                    for(int i=0;i<m.getParamCount();i++){
                        Var ai=stmt.getRValue().getArg(i);
                        Var pi=m.getIR().getParam(i);
                        addPFGEdge(csManager.getCSVar(context,ai), csManager.getCSVar(ct,pi));
                    }
                    Var r=stmt.getLValue();
                    if(r!=null) {
                        for (int i = 0; i < m.getIR().getReturnVars().size(); i++) {
                            Var mreti=m.getIR().getReturnVars().get(i);
                            addPFGEdge(csManager.getCSVar(ct,mreti), csManager.getCSVar(context,r));
                        }
                    }
                }
                taintAnalysis.handle_source(cscallsite, csm);
//                taintAnalysis.taint_static_call(csManager.getCSCallSite(context,stmt),m,null);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if(stmt.isStatic()){
                JField field = stmt.getFieldRef().resolve();
                Var y = stmt.getLValue();
                addPFGEdge(csManager.getStaticField(field), csManager.getCSVar(context,y));
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if(stmt.isStatic()){
                JField field = stmt.getFieldRef().resolve();
                Var y = stmt.getRValue();
                addPFGEdge(csManager.getCSVar(context,y), csManager.getStaticField(field));
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
            if(pointer instanceof CSVar n){
                Var x=n.getVar();
                for(CSObj csobj:differ) {
                    if (taintAnalysis.isTaint(csobj.getObject())) continue;
                    for (StoreField stmt : x.getStoreFields()) {
                        assert(!stmt.isStatic());
                        if(stmt.isStatic()){
                            JField field = stmt.getFieldRef().resolve();
                            Var y = stmt.getRValue();
                            this.addPFGEdge(csManager.getCSVar(n.getContext(),y),csManager.getStaticField(field));
                        }
                        else{
                            JField field = stmt.getFieldRef().resolve();
                            Var y = stmt.getRValue();
                            this.addPFGEdge(csManager.getCSVar(n.getContext(),y), csManager.getInstanceField(csobj,field));
                        }
                    }
                    for (LoadField stmt : x.getLoadFields()) {
                        assert(!stmt.isStatic());
                        if(stmt.isStatic()){
                            JField field = stmt.getFieldRef().resolve();
                            Var y = stmt.getLValue();
                            this.addPFGEdge(csManager.getStaticField(field), csManager.getCSVar(n.getContext(),y));
                        }
                        else{
                            JField field = stmt.getFieldRef().resolve();
                            Var y = stmt.getLValue();
                            this.addPFGEdge(csManager.getInstanceField(csobj, field), csManager.getCSVar(n.getContext(),y));
                        }
                    }
                    for (StoreArray stmt : x.getStoreArrays()) {
                        Var y = stmt.getRValue();
                        this.addPFGEdge(csManager.getCSVar(n.getContext(),y), csManager.getArrayIndex(csobj));
                    }
                    for (LoadArray stmt : x.getLoadArrays()) {
                        Var y = stmt.getLValue();
                        this.addPFGEdge(csManager.getArrayIndex(csobj), csManager.getCSVar(n.getContext(),y));
                    }
                    this.processCall(n, csobj);
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
        PointsToSet differ=PointsToSetFactory.make();
        if(!pointsToSet.isEmpty()){
            PointsToSet ptn=pointer.getPointsToSet();
            for(CSObj csobj:pointsToSet) {
                if (!ptn.contains(csobj)) {
                    ptn.addObject(csobj);
                    differ.addObject(csobj);
                }
            }
            Set<Pointer> succs=this.pointerFlowGraph.getSuccsOf(pointer);
            for(Pointer succ:succs){
                workList.addEntry(succ,differ);
            }
        }
        taintAnalysis.taint_propagate(pointer,differ);
        return differ;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        for (Invoke callsite : recv.getVar().getInvokes()) {
            assert (!callsite.isStatic());
            JMethod m = this.resolveCallee(recvObj, callsite);
            CSCallSite cscallsite = csManager.getCSCallSite(recv.getContext(), callsite);
            Context ct = contextSelector.selectContext(cscallsite, recvObj, m);
            CSMethod csm = csManager.getCSMethod(ct, m);
            workList.addEntry(csManager.getCSVar(ct, m.getIR().getThis()), PointsToSetFactory.make(recvObj));
            CallKind kind = null;
            if (callsite.isVirtual()) {
                kind = CallKind.VIRTUAL;
            } else if (callsite.isStatic()) {
                kind = CallKind.STATIC;
            } else if (callsite.isInterface()) {
                kind = CallKind.INTERFACE;
            } else if (callsite.isSpecial()) {
                kind = CallKind.SPECIAL;
            } else if (callsite.isDynamic()) {
                kind = CallKind.DYNAMIC;
            }
            if (callGraph.addEdge(new Edge<>(kind, cscallsite, csm))) {
                this.addReachable(csm);
                taintAnalysis.taint_addTPFGedge(cscallsite, csm);
                for (int i = 0; i < m.getParamCount(); i++) {
                    Var ai = callsite.getRValue().getArg(i);
                    Var pi = m.getIR().getParam(i);
                    this.addPFGEdge(csManager.getCSVar(recv.getContext(), ai), csManager.getCSVar(ct, pi));
                }
                Var r = callsite.getLValue();
                if (r != null) {
                    for (int i = 0; i < m.getIR().getReturnVars().size(); i++) {
                        Var mreti = m.getIR().getReturnVars().get(i);
                        this.addPFGEdge(csManager.getCSVar(ct, mreti), csManager.getCSVar(recv.getContext(), r));
                    }
                }
                taintAnalysis.handle_source(cscallsite, csm);
            }
        }
//            taintAnalysis.taint_call(csManager.getCSCallSite(recv.getContext(), callsite),m,recv);
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    public JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }

    public void WorkList_addentry(Pointer pointer,CSObj csObj) {
        workList.addEntry(pointer,PointsToSetFactory.make(csObj));
    }
    public void WorkList_addentry(Pointer pointer,PointsToSet pts) {
        workList.addEntry(pointer,pts);
    }
}
