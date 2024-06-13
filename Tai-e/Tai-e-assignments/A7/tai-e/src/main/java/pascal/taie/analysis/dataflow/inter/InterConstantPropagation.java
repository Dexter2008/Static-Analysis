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

import fj.data.fingertrees.Node;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.solver.Solver;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.*;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.lang.reflect.Method;
import java.util.HashSet;
import java.util.List;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;
    public static PointerAnalysisResult pta;
    public static InterSolver<JMethod,Stmt,CPFact> sol;
    public static final HashSet<StoreField>sloadfields=new HashSet<StoreField>();
    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
         pta = World.get().getResult(ptaId);
         sol=solver;
        // You can do initialization work here
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if(stmt instanceof StoreField storeField){
            if(storeField.isStatic()){
                //A.f=b
                JClass A=storeField.getFieldRef().getDeclaringClass();
                JField f=storeField.getFieldRef().resolve();
                for(Stmt s:icfg){
                    if(s instanceof LoadField &&((LoadField) s).isStatic()){
                        if(((LoadField) s).getFieldRef().getDeclaringClass()==A
                            && ((LoadField) s).getFieldRef().resolve()==f){
                            solver.WL_add(s);
                        }
                    }
                }
            }
            else{//a.f=b
                JClass a=storeField.getFieldRef().getDeclaringClass();
                JField f=storeField.getFieldRef().resolve();
                assert(storeField.getFieldAccess() instanceof InstanceFieldAccess);
                Var base=((InstanceFieldAccess) storeField.getFieldAccess()).getBase();
                for(Var v:pta.getVars()){
                    if(check_alian(base,v)){
                        for(LoadField vloadfield:v.getLoadFields()){
                            if(!vloadfield.isStatic()&&vloadfield.getFieldAccess().getFieldRef().resolve()==f)
                                solver.WL_add(vloadfield);
                        }
                    }
                }
            }
        }
        else if(stmt instanceof LoadField loadfield){
            if(loadfield.isStatic()){
                //b=A.f
                Value res=Value.getUndef();
                JClass A=loadfield.getFieldRef().getDeclaringClass();
                JField f=loadfield.getFieldRef().resolve();
                for(Stmt s:icfg){
                    if(s instanceof StoreField &&((StoreField) s).isStatic()){
                        if(((StoreField) s).getFieldRef().getDeclaringClass()==A
                                && ((StoreField) s).getFieldRef().resolve()==f){
                            res=cp.meetValue(res,solver.get_temp_outfact(s).get(((StoreField) s).getRValue()));
                        }
                    }
                }
                CPFact copy=in.copy();
                copy.remove(loadfield.getLValue());
                copy.update(loadfield.getLValue(),res);
                return out.copyFrom(copy);
            }
            else{//b=a.f
                Value res=Value.getUndef();
                JClass a=loadfield.getFieldRef().getDeclaringClass();
                JField f=loadfield.getFieldRef().resolve();
                assert(loadfield.getFieldAccess() instanceof InstanceFieldAccess);
                Var base=((InstanceFieldAccess) loadfield.getFieldAccess()).getBase();
                for(Var v:pta.getVars()){
                    if(check_alian(base,v)){
                        for(StoreField vstorefield:v.getStoreFields()){
                            if(!vstorefield.isStatic()&&vstorefield.getFieldAccess().getFieldRef().resolve()==f)
                                res=cp.meetValue(res,solver.get_temp_outfact(vstorefield).get(vstorefield.getRValue()));
                        }
                    }
                }
                CPFact copy=in.copy();
                copy.remove(loadfield.getLValue());
                copy.update(loadfield.getLValue(),res);
                return out.copyFrom(copy);
            }
        }
        else if(stmt instanceof StoreArray storeArray){
            //b[i]=a;
            Var b = storeArray.getArrayAccess().getBase();
            Var i = storeArray.getArrayAccess().getIndex();
            Value i_val=solver.get_temp_infact(stmt).get(i);
            if(i_val.isUndef())return out.copyFrom(in);
            for(Var v:pta.getVars()){
                if(check_alian(b,v)){
                    for(LoadArray vloadArray:v.getLoadArrays()) {
                        CPFact fact=solver.get_temp_outfact(vloadArray).copy();
                        Var index=vloadArray.getArrayAccess().getIndex();
                        Value index_val=fact.get(index);
                        if((i_val.isConstant()&&index_val.isConstant()
                                &&i_val.equals(index_val))
                                ||(i_val.isNAC()||index_val.isNAC())){
                            solver.WL_add(vloadArray);
                        }
                    }
                }
            }
        }
        else if(stmt instanceof LoadArray loadarray){
            //a=b[i]
            Value res=Value.getUndef();
            Var b = loadarray.getArrayAccess().getBase();
            Var i = loadarray.getArrayAccess().getIndex();
            Value i_val=solver.get_temp_infact(stmt).get(i);
            if(i_val.isUndef()){
                CPFact copy = in.copy();
                copy.update(loadarray.getLValue(), Value.getUndef());
                return out.copyFrom(copy);
            }
            for(Var v:pta.getVars()){
                if(check_alian(b,v)){
                    for(StoreArray vstoreArray:v.getStoreArrays()) {
                        CPFact fact=solver.get_temp_outfact(vstoreArray).copy();
                        Var index=vstoreArray.getArrayAccess().getIndex();
                        Value index_val=fact.get(index);
                        if((i_val.isConstant()&&index_val.isConstant()
                                &&i_val.equals(index_val))
                            ||(i_val.isNAC()||index_val.isNAC())){
                            res=cp.meetValue(res,solver.get_temp_outfact(vstoreArray).get(vstoreArray.getRValue()));
                        }
                    }
                }
            }
            CPFact copy=in.copy();
            copy.remove(loadarray.getLValue());
            copy.update(loadarray.getLValue(),res);
            return out.copyFrom(copy);
        }
        return cp.transferNode(stmt,in,out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact copy=out.copy();
        Stmt s=edge.getSource();
        if(s.getDef().isPresent()){
            LValue lvar=s.getDef().get();
            if(lvar instanceof Var && ConstantPropagation.canHoldInt((Var)lvar)){
                copy.remove((Var)lvar);
            }
        }
        return copy;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact res=new CPFact();
        Invoke s=(Invoke) edge.getSource();
        JMethod m=edge.getCallee();
        for(int i=0;i<m.getParamCount();i++){
            Var param=m.getIR().getParam(i);
            if(ConstantPropagation.canHoldInt(param)){
                res.update(param,callSiteOut.get(s.getRValue().getArg(i)));
            }
        }
        return res;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact res=new CPFact();
        Stmt s=edge.getCallSite();
        if(s.getDef().isEmpty())return res;
        List<Var> retvars=edge.getReturnVars().stream().toList();
        Value finalvalue=Value.getUndef();
        for(Var retvar:retvars){
            Value rtvalue =returnOut.get(retvar);
            finalvalue=cp.meetValue(rtvalue,finalvalue);
        }
        LValue lvar=s.getDef().get();
        if(lvar instanceof Var&&ConstantPropagation.canHoldInt((Var)lvar)) {
            res.update((Var) s.getDef().get(), finalvalue);
        }
        return res;
    }
    public boolean check_alian(Var base,Var var){
        for(Obj obj: pta.getPointsToSet(base)){
            if(pta.getPointsToSet(var).contains(obj)){
                return true;
            }
        }
        return false;
    }
}
