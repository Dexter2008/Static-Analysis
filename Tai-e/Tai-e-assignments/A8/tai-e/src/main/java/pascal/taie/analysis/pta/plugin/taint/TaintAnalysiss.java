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

package pascal.taie.analysis.pta.plugin.taint;

import com.google.common.collect.ArrayListMultimap;
import com.google.common.collect.ListMultimap;
import com.google.common.collect.Multimap;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Pair;
import soot.jimple.spark.ondemand.genericutil.HashSetMultiMap;
import soot.util.HashMultiMap;
import soot.util.MultiMap;

import java.sql.Struct;
import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me
    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }

    public Multimap<CSVar, CSVar> TPFG = ArrayListMultimap.create();

    public void handle_source(CSCallSite cscallsite, CSMethod csMethod) {
        if (config.getSources().contains(new Source(csMethod.getMethod(), csMethod.getMethod().getReturnType()))) {
            Obj taint = manager.makeTaint(cscallsite.getCallSite(), cscallsite.getCallSite().getMethodRef().getReturnType());
            CSObj cstaint = csManager.getCSObj(emptyContext, taint);
            if (cscallsite.getCallSite().getDef().isPresent()) {
                CSVar l = csManager.getCSVar(cscallsite.getContext(), cscallsite.getCallSite().getResult());
                solver.WorkList_addentry(l, cstaint);
            }
        }
    }

    public CSVar handle_base(CSCallSite csCallSite) {
        InvokeExp exp = csCallSite.getCallSite().getInvokeExp();
        Var base;
        if (exp instanceof InvokeInstanceExp) {
            base = ((InvokeInstanceExp) exp).getBase();
            return csManager.getCSVar(csCallSite.getContext(), base);
        } else {
            assert (false);
            return null;
        }
    }

    public CSVar handle_result(CSCallSite csCallSite) {
        return csManager.getCSVar(csCallSite.getContext(), csCallSite.getCallSite().getResult());
    }

    public CSVar handle_arg(CSCallSite csCallSite, int i) {
        return csManager.getCSVar(
                csCallSite.getContext(),
                csCallSite.getCallSite().getInvokeExp().getArg(i)
        );
    }

    public CSVar handle_ArgbaseResult(CSCallSite csCallSite, int i) {
        if (i >= 0) return handle_arg(csCallSite, i);
        else if (i == -1) return handle_base(csCallSite);
        else if (i == -2) return handle_result(csCallSite);
        else {
            assert (false);
            return null;
        }
    }

    public void taint_addTPFGedge(CSCallSite csCallSite, CSMethod csMethod) {
        JMethod method = csMethod.getMethod();
        for (TaintTransfer taintTransfer : config.getTransfers()) {
            if (taintTransfer.method().equals(method)) {
                CSVar source = handle_ArgbaseResult(csCallSite, taintTransfer.from());
                CSVar target = handle_ArgbaseResult(csCallSite, taintTransfer.to());
                if (TPFG.put(source, target)) {
                    PointsToSet taintdiffer = PointsToSetFactory.make();
                    for (CSObj csObj : source.getPointsToSet().getObjects()) {
                        if (manager.isTaint(csObj.getObject())) {
                            taintdiffer.addObject(csObj);
                        }
                    }
                    solver.WorkList_addentry(target, taintdiffer);
                }
            }
        }
    }
    public void taint_propagate(Pointer pointer,PointsToSet differ){
        if (pointer instanceof CSVar){
            PointsToSet taintdiffer = PointsToSetFactory.make();
            for (CSObj csObj : differ.getObjects()) {
                if (manager.isTaint(csObj.getObject())){
                    taintdiffer.addObject(csObj);
                }
            }
            if (!taintdiffer.isEmpty()){
                for (CSVar v:TPFG.get((CSVar) pointer)) {
                    solver.WorkList_addentry(v, taintdiffer);
                }
            }
        }
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        for (Sink sink : config.getSinks()) {
            if (result.getCallGraph().contains(sink.method())) {
                Set<Invoke> sink_invoke = result.getCallGraph().getCallersOf(sink.method());
                for (Invoke invoke : sink_invoke) {
                    for (Obj obj : result.getPointsToSet(invoke.getInvokeExp().getArg(sink.index()))) {
                        if (manager.isTaint(obj)) {
                            taintFlows.add(new TaintFlow(manager.getSourceCall(obj), invoke, sink.index()));
                        }
                    }
                }
            }
        }
        return taintFlows;
    }
}
