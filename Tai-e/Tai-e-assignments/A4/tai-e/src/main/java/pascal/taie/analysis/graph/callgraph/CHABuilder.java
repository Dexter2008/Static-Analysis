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

package pascal.taie.analysis.graph.callgraph;

import com.fasterxml.jackson.databind.JsonSerializer;
import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Nop;
import pascal.taie.language.classes.*;
import soot.Hierarchy;

import java.util.*;
import java.util.stream.Stream;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod>worklist=new ArrayDeque<JMethod>();
        worklist.add(entry);
        while(!worklist.isEmpty()){
            JMethod m=worklist.poll();
            if(!callGraph.contains(m)){
                callGraph.addReachableMethod(m);
                List<Invoke>callsites=callGraph.callSitesIn(m).toList();
                for(Invoke cs:callsites){
                    Set<JMethod>T=resolve(cs);
                    for(JMethod m1:T){
                        callGraph.addEdge(new Edge<Invoke,JMethod>(CallGraphs.getCallKind(cs),cs,m1));
                        worklist.add(m1);
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod>T=new HashSet<>();
        MethodRef mr=callSite.getMethodRef();
        Subsignature m=mr.getSubsignature();
        if(CallGraphs.getCallKind(callSite)== CallKind.STATIC){
            T.add(mr.getDeclaringClass().getDeclaredMethod(m));
        }
        else if(CallGraphs.getCallKind(callSite)== CallKind.SPECIAL){
            JClass cm=mr.getDeclaringClass();
            if(dispatch(cm,m)!=null)T.add(dispatch(cm,m));
        }
        else if(CallGraphs.getCallKind(callSite)== CallKind.VIRTUAL||CallGraphs.getCallKind(callSite)==CallKind.INTERFACE){
            JClass c=mr.getDeclaringClass();
            Queue<JClass>queue=new ArrayDeque<JClass>();
            queue.add(c);
            while(!queue.isEmpty()){
                JClass c1=queue.poll();
                if(dispatch(c1,m)!=null)T.add(dispatch(c1,m));
                if(c1.isInterface()){
                    queue.addAll(hierarchy.getDirectSubinterfacesOf(c1));
                    queue.addAll(hierarchy.getDirectImplementorsOf(c1));
                }
                else{
                    queue.addAll(hierarchy.getDirectSubclassesOf(c1));
                }
            }
        }
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JMethod m1=jclass.getDeclaredMethod(subsignature);
        if(m1!=null&&!m1.isAbstract()){
            return m1;
        }
        else{
            JClass c1=jclass.getSuperClass();
            if(c1==null||c1.isInterface())return null;
            else return dispatch(c1,subsignature);
        }
    }
}
