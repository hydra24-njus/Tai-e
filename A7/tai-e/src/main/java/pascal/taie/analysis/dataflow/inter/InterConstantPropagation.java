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

import java.util.*;
import java.util.stream.Collectors;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private PointerAnalysisResult pta;
    private Multimap<Var, Stmt> storeFields = HashMultimap.create();
    private Multimap<Var, Stmt> storeArrays = HashMultimap.create();
    private Multimap<Var, Stmt> loadFields = HashMultimap.create();
    private Multimap<Var, Stmt> loadArrays = HashMultimap.create();

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
        pta.getVars().forEach(x->{
            pta.getVars().forEach(y->{
                pta.getPointsToSet(x).forEach(obj->{
                    if(pta.getPointsToSet(y).contains(obj)){
                        storeFields.putAll(x , y.getStoreFields());
                        storeArrays.putAll(x , y.getStoreArrays());
                        loadFields.putAll(x , y.getLoadFields());
                        loadArrays.putAll(x , y.getLoadArrays());
                    }
                });
            });
        });
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
        if(stmt instanceof LoadField loadField){
            JField jField=loadField.getRValue().getFieldRef().resolve();
            Set<Value> staticLoad = new HashSet<>();
            Value res = Value.getUndef();
            if(loadField.isStatic()){
                icfg.forEach(allStmt->{
                    if(allStmt instanceof StoreField storeField && storeField.isStatic()){
                        if(jField==storeField.getFieldAccess().getFieldRef().resolve()){
                            staticLoad.add(solver.getResult().getInFact(storeField).get(storeField.getRValue()));
                        }
                    }
                });
            }
            else{
                Var base = ((InstanceFieldAccess) loadField.getFieldAccess()).getBase();
                Set<StoreField> store_to_field = new HashSet<>();
                storeFields.get(base).forEach(storefield->{
                    if(((StoreField)storefield).getFieldRef().resolve()==jField){
                        store_to_field.add((StoreField)storefield);
                    }
                });
                store_to_field.forEach(storeField->{
                    staticLoad.add(solver.getResult().getInFact(storeField).get(storeField.getRValue()));
                });
            }
            for (Value value : staticLoad) {
                res = cp.meetValue(res, value);
            }
            CPFact in_copy = in.copy();
            in_copy.remove(loadField.getLValue());
            in_copy.update(loadField.getLValue(), res);
            return out.copyFrom(in_copy);
        }
        else if(stmt instanceof LoadArray loadArray){
            Var lValue = loadArray.getLValue();
            ArrayAccess arrayAccess = loadArray.getArrayAccess();
            Set<Value> arraystore = new HashSet<>();
            Value res = Value.getUndef();
            
            if (solver.getResult().getInFact(stmt).get(arrayAccess.getIndex()) == Value.getUndef()) {
                CPFact in_copy = in.copy();
                in_copy.update(lValue, Value.getUndef());
                return out.copyFrom(in_copy);
            }

            Set<StoreArray> collects = new HashSet<>();
            for (Object storeArrayObj : storeArrays.get(arrayAccess.getBase())) {
                StoreArray storeArray = (StoreArray) storeArrayObj;
                Value arrayValue = solver.getResult().getInFact(storeArray).get(storeArray.getArrayAccess().getIndex());
                if (arrayValue != Value.getUndef()) {
                    Value stmtValue = solver.getResult().getInFact(stmt)
                                            .get(arrayAccess.getIndex());
                    if (stmtValue == Value.getNAC() || arrayValue == Value.getNAC() || arrayValue == stmtValue) {
                        collects.add(storeArray);
                    }
                }
            }

            collects.forEach(storeArray->{arraystore.add(solver.getResult().getInFact(storeArray).get(storeArray.getRValue()));});
            for (Value value : arraystore) {
                res = cp.meetValue(res, value);
            }
            CPFact in_copy = in.copy();
            in_copy.remove(lValue);
            in_copy.update(lValue, res);
            return out.copyFrom(in_copy);
        }
        else if(stmt instanceof StoreField storeField){
            JField jField = storeField.getFieldRef().resolve();
            Set<Stmt> staticStore = new HashSet<>();
            if (storeField.isStatic()) {
                icfg.forEach(allStmt->{
                    if(allStmt instanceof LoadField loadField && loadField.isStatic()){
                        if(jField==storeField.getFieldAccess().getFieldRef().resolve()){
                            staticStore.add(allStmt);
                        }
                    }
                });
                staticStore.forEach(arg->solver.getWorkList().offer(arg));
            } else {
                loadFields.get(((InstanceFieldAccess) storeField.getFieldAccess()).getBase()).forEach(arg->solver.getWorkList().offer(arg));
            }
            return out.copyFrom(in);
        }
        else if(stmt instanceof StoreArray storeArray){
            Var base = storeArray.getArrayAccess().getBase();
            Var index = storeArray.getArrayAccess().getIndex();
            Value i_value = solver.getResult().getInFact(stmt).get(index);
            if (i_value == Value.getUndef()) {
                return out.copyFrom(in);
            }

            Set<LoadArray> collects = new HashSet<>();
            for (Object loadArrayObj : loadArrays.get(base)) {
                LoadArray loadArray = (LoadArray) loadArrayObj;
                Value arrayValue = solver.getResult().getInFact(loadArray).get(loadArray.getArrayAccess().getIndex());
                if (arrayValue != Value.getUndef()) {
                    if (i_value == Value.getNAC() || arrayValue == Value.getNAC() || arrayValue == i_value) {
                        collects.add(loadArray);
                    }
                }
            }
            collects.forEach(arg->solver.getWorkList().add(arg));
            return out.copyFrom(in);
        }
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        Invoke callSite = (Invoke) edge.getSource();
        Var target = callSite.getResult();
        CPFact ret = out.copy();
        if(target != null){
            ret.remove(target);
        }
        return ret;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        Invoke callSite= (Invoke) edge.getSource();
        List<Var> args=edge.getCallee().getIR().getParams();
        CPFact ret=new CPFact();
        if(args.size()!=callSite.getInvokeExp().getArgCount()){
            //参数个数不一致
            //Do something
            return ret;
        }
        for(int i=0;i<args.size();i++){
            ret.update(args.get(i), callSiteOut.get(callSite.getInvokeExp().getArg(i)));
        }
        return ret;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
         Invoke callSite= (Invoke) edge.getCallSite();
        Var target=callSite.getResult();
        CPFact ret=new CPFact();
        if(target==null){
            // Do something
            return ret;
        }
        for(Var var:edge.getReturnVars()){
            ret.update(target,cp.meetValue(ret.get(target), returnOut.get(var)));
        }

        return ret;
    }
}
