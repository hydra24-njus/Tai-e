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
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

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
        var fact = new CPFact();
        cfg.getIR().getParams().forEach(param->{
            if(canHoldInt(param)){
                fact.update(param,Value.getNAC());
            }
        });
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.keySet().forEach(key -> {
            target.update(key,meetValue(fact.get(key),target.get(key)));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.isNAC()||v2.isNAC()){
            return Value.getNAC();
        }
        if(v1.isConstant() && v2.isUndef()){
            return Value.makeConstant(v1.getConstant());
        }
        if(v1.isUndef() && v2.isConstant()){
            return Value.makeConstant(v2.getConstant());
        }
        if(v1.isConstant() && v2.isConstant()){
            if(v1.equals(v2)){
                return Value.makeConstant(v1.getConstant());
            }
            else{
                return Value.getNAC();
            }
        }
        return Value.getUndef();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof DefinitionStmt<?, ?> definitionStmt) {
            LValue lvalue = definitionStmt.getLValue();
            RValue rvalue = definitionStmt.getRValue();
            if (lvalue instanceof Var var && canHoldInt(var)) {
                var newout = in.copy();
                newout.update(var, evaluate(rvalue, in));
                return out.copyFrom(newout);
            }
        }
        return out.copyFrom(in);
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
        if(exp instanceof Var v){
            if(in.get(v).isConstant()){
                return Value.makeConstant(in.get(v).getConstant());
            }
            return in.get(v);
        }
        else if(exp instanceof IntLiteral i){
            return Value.makeConstant(i.getValue());
        }
        else if(exp instanceof BinaryExp b){
            var v1 = in.get(b.getOperand1());
            var v2 = in.get(b.getOperand2());
            if(v2.isConstant()&&v2.getConstant()==0){
                if(b.getOperator() instanceof ArithmeticExp.Op op &&(op==ArithmeticExp.Op.DIV||op==ArithmeticExp.Op.REM)){
                    return Value.getUndef();
                }
            }
            if(v1.isConstant()&&v2.isConstant()){
                if(b.getOperator() instanceof ArithmeticExp.Op op){
                    switch(op){
                        case ADD ->{
                            return Value.makeConstant(v1.getConstant()+v2.getConstant());
                        }
                        case SUB ->{
                            return Value.makeConstant(v1.getConstant()-v2.getConstant());
                        }
                        case MUL ->{
                            return Value.makeConstant(v1.getConstant()*v2.getConstant());
                        }
                        case DIV ->{
                            if(v2.getConstant()==0){
                                return Value.getUndef();
                            }
                            return Value.makeConstant(v1.getConstant()/v2.getConstant());
                        }
                        case REM ->{
                            if(v2.getConstant()==0){
                                return Value.getUndef();
                            }
                            return Value.makeConstant(v1.getConstant()%v2.getConstant());
                        }
                    }
                }
                else if(b.getOperator() instanceof ConditionExp.Op op) {
                    switch(op){
                        case EQ ->{
                            return Value.makeConstant(v1.getConstant()==v2.getConstant()?1:0);
                        }
                        case NE ->{
                            return Value.makeConstant(v1.getConstant()!=v2.getConstant()?1:0);
                        }
                        case LT ->{
                            return Value.makeConstant(v1.getConstant()<v2.getConstant()?1:0);
                        }
                        case GT ->{
                            return Value.makeConstant(v1.getConstant()>v2.getConstant()?1:0);
                        }
                        case LE ->{
                            return Value.makeConstant(v1.getConstant()<=v2.getConstant()?1:0);
                        }
                        case GE ->{
                            return Value.makeConstant(v1.getConstant()>=v2.getConstant()?1:0);
                        }
                    }

                }
                else if(b.getOperator() instanceof ShiftExp.Op op){
                    switch(op){
                        case SHL ->{
                            return Value.makeConstant(v1.getConstant()<<v2.getConstant());
                        }
                        case SHR ->{
                            return Value.makeConstant(v1.getConstant()>>v2.getConstant());
                        }
                        case USHR ->{
                            return Value.makeConstant(v1.getConstant()>>>v2.getConstant());
                        }
                    }
                }
                else if(b.getOperator() instanceof BitwiseExp.Op op){
                    switch(op){
                        case OR ->{
                            return Value.makeConstant(v1.getConstant()|v2.getConstant());
                        }
                        case AND ->{
                            return Value.makeConstant(v1.getConstant()&v2.getConstant());
                        }
                        case XOR ->{
                            return Value.makeConstant(v1.getConstant()^v2.getConstant());
                        }
                    }
                }
            }
            else if(v1.isNAC()||v2.isNAC()){
                return Value.getNAC();
            }
            return Value.getUndef();
        }
        return Value.getNAC();
    }
}
