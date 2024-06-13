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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;
import java.util.Set;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact entry=new CPFact();
        List<Var> list=cfg.getIR().getParams();
        for(Var l:list){
            if(canHoldInt(l)){
                entry.update(l,Value.getNAC());
            }
        }
        return entry;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        Set<Var> key =fact.keySet();
        for(Var it:key){
            if(canHoldInt(it)){
                Value v1=fact.get(it);
                Value v2=target.get(it);
                Value v=meetValue(v1,v2);
                target.update(it,v);
            }
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.isNAC()||v2.isNAC())return Value.getNAC();
        if(v1.isUndef()&&v2.isUndef())return Value.getUndef();
        if(v1.isConstant()&&v2.isUndef())return v1;
        if(v2.isConstant()&&v1.isUndef())return v2;
        if(v1.isConstant()&&v2.isConstant()){
            if(v1.equals(v2))return v1;
            else return Value.getNAC();
        }
        return null;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact OldOut = out.copy();
        CPFact tmp = in.copy();
        if (stmt instanceof DefinitionStmt) {
            LValue lvar = ((DefinitionStmt<?, ?>) stmt).getLValue();
            if (lvar instanceof Var && canHoldInt((Var) lvar)) {
                tmp.remove((Var) lvar);
                RValue rvar = ((DefinitionStmt<?, ?>) stmt).getRValue();
                Value v = evaluate(rvar, in);
                tmp.update((Var) lvar, v);
            }
        }
        out.copyFrom(tmp);
        return !(out.equals(OldOut));
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if(exp instanceof IntLiteral) return Value.makeConstant(((IntLiteral)exp).getValue());
        if(exp instanceof Var )return in.get((Var)exp);
        if(exp instanceof BinaryExp){
            Var op1=((BinaryExp) exp).getOperand1();
            Var op2=((BinaryExp) exp).getOperand2();
            if( in.get(op2).isConstant()&& in.get(op2).getConstant()==0 &&
                    exp instanceof ArithmeticExp &&
                    (((ArithmeticExp) exp).getOperator()==ArithmeticExp.Op.DIV ||
                            ((ArithmeticExp) exp).getOperator()==ArithmeticExp.Op.REM))
                return Value.getUndef();//special case
            if(in.get(op1).isConstant()&&in.get(op2).isConstant()){
                int v1=in.get(op1).getConstant();int v2=in.get(op2).getConstant();
                if(exp instanceof ArithmeticExp){
                    if(((ArithmeticExp) exp).getOperator()==ArithmeticExp.Op.ADD)return Value.makeConstant(v1+v2);
                    if(((ArithmeticExp) exp).getOperator()==ArithmeticExp.Op.SUB)return Value.makeConstant(v1-v2);
                    if(((ArithmeticExp) exp).getOperator()== ArithmeticExp.Op.MUL)return Value.makeConstant(v1*v2);
                    if(((ArithmeticExp) exp).getOperator()== ArithmeticExp.Op.DIV){
                        if(v2==0)return Value.getUndef();
                        else return Value.makeConstant(v1/v2);
                    }
                    if(((ArithmeticExp) exp).getOperator()== ArithmeticExp.Op.REM){
                        if(v2==0)return Value.getUndef();
                        else return Value.makeConstant(v1%v2);
                    }
                }
                if(exp instanceof ConditionExp){
                    if(((ConditionExp) exp).getOperator()== ConditionExp.Op.EQ)return Value.makeConstant(v1==v2?1:0);
                    if(((ConditionExp) exp).getOperator()== ConditionExp.Op.GE)return Value.makeConstant(v1>=v2?1:0);
                    if(((ConditionExp) exp).getOperator()== ConditionExp.Op.LE)return Value.makeConstant(v1<=v2?1:0);
                    if(((ConditionExp) exp).getOperator()== ConditionExp.Op.GT)return Value.makeConstant(v1>v2?1:0);
                    if(((ConditionExp) exp).getOperator()== ConditionExp.Op.LT)return Value.makeConstant(v1<v2?1:0);
                    if(((ConditionExp) exp).getOperator()== ConditionExp.Op.NE)return Value.makeConstant(v1!=v2?1:0);
                }
                if(exp instanceof ShiftExp){
                    if(((ShiftExp) exp).getOperator()== ShiftExp.Op.SHL)return Value.makeConstant(v1<<v2);
                    if(((ShiftExp) exp).getOperator()== ShiftExp.Op.SHR)return Value.makeConstant(v1>>v2);
                    if(((ShiftExp) exp).getOperator()== ShiftExp.Op.USHR)return Value.makeConstant(v1>>>v2);
                }
                if(exp instanceof BitwiseExp){
                    if(((BitwiseExp) exp).getOperator()== BitwiseExp.Op.AND)return Value.makeConstant(v1&v2);
                    if(((BitwiseExp) exp).getOperator()== BitwiseExp.Op.OR)return Value.makeConstant(v1|v2);
                    if(((BitwiseExp) exp).getOperator()== BitwiseExp.Op.XOR)return Value.makeConstant(v1^v2);
                }
            }
            if(in.get(op1).isNAC()||in.get(op2).isNAC())return Value.getNAC();
            else return Value.getUndef();
        }
        return Value.getNAC();
    }
}
