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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.util.collection.SetQueue;

import java.util.ArrayDeque;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
        this.workList=new ArrayDeque<Node>();
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        for(Node node:icfg){
            result.setInFact(node,analysis.newInitialFact());
            result.setOutFact(node,analysis.newInitialFact());
        }
        for(Method entrym:icfg.entryMethods().toList()){
            result.setOutFact(icfg.getEntryOf(entrym),analysis.newBoundaryFact(icfg.getEntryOf(entrym)));
        }
    }

    private void doSolve() {
        // TODO - finish me
        for(Node node:icfg){
            workList.add(node);
        }
        while(!workList.isEmpty()){
            Node curblock =workList.poll();
            for(ICFGEdge<Node> prededge:icfg.getInEdgesOf(curblock)){
                analysis.meetInto(analysis.transferEdge(prededge,result.getOutFact(prededge.getSource())),
                        result.getInFact(curblock));
            }
            boolean flag=analysis.transferNode(curblock,result.getInFact(curblock),result.getOutFact(curblock));
            if(flag) workList.addAll(icfg.getSuccsOf(curblock));
        }
    }
    public Fact get_temp_outfact(Node stmt){
        return result.getOutFact(stmt);
    }
    public Fact get_temp_infact(Node stmt){
        return result.getInFact(stmt);
    }
    public void WL_add(Node s){
        workList.add(s);
    }
}