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

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Pair;

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
    public Obj getTaintSource(Invoke callsite, JMethod callee){
        if(config.getSources().contains(new Source(callee, callee.getReturnType()))) 
            return manager.makeTaint(callsite, callee.getReturnType());
        return null;
    }

    public Set<Pair<Var,Obj>> TaintTransfer(CSCallSite csCallSite,JMethod callee,CSVar base){
        Set<Pair<Var, Obj>> ret = new HashSet<>();
        TaintTransfer transfer;
        List<Var> args = csCallSite.getCallSite().getInvokeExp().getArgs();
        PointerAnalysisResult ptares = solver.getResult();
        if(base != null) {
            transfer = new TaintTransfer(callee, TaintTransfer.BASE, TaintTransfer.RESULT, callee.getReturnType());
            if(config.getTransfers().contains(transfer) && csCallSite.getCallSite().getLValue() != null) {
                ptares.getPointsToSet(base).forEach(csObj -> {
                    if(manager.isTaint(csObj.getObject())) {
                        ret.add(new Pair<>(csCallSite.getCallSite().getLValue(), manager.makeTaint(manager.getSourceCall(csObj.getObject()), callee.getReturnType())));
                    }
                });
            }
            for(int i = 0; i < args.size(); ++i) {
                transfer = new TaintTransfer(callee, i, TaintTransfer.BASE, base.getType());
                if(config.getTransfers().contains(transfer)) {
                    ptares.getPointsToSet(csManager.getCSVar(csCallSite.getContext(), args.get(i))).forEach(csObj -> {
                        if(manager.isTaint(csObj.getObject())) {
                            ret.add(new Pair<>(base.getVar(), manager.makeTaint(manager.getSourceCall(csObj.getObject()), callee.getReturnType())));
                        }
                    });
                }
            }
        }
        for(int i=0;i<args.size();i++){
            Var arg = args.get(i);
            transfer = new TaintTransfer(callee, i, TaintTransfer.RESULT, callee.getReturnType());
            if(config.getTransfers().contains(transfer) && csCallSite.getCallSite().getLValue() != null) {
                solver.getResult().getPointsToSet(csManager.getCSVar(csCallSite.getContext(), arg)).forEach(csObj -> {
                    if(manager.isTaint(csObj.getObject())) {
                        ret.add(new Pair<>(csCallSite.getCallSite().getLValue(), 
                                            manager.makeTaint(manager.getSourceCall(csObj.getObject()), 
                                            callee.getReturnType())));
                    }
                });
            }
        }
        return ret;
    }

    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        result.getCSCallGraph().reachableMethods().forEach(method->{
            result.getCSCallGraph().getCallersOf(method).forEach(csCallSite->{
                List<Var> args=csCallSite.getCallSite().getInvokeExp().getArgs();
                for(int i=0;i<args.size();i++){
                    if(config.getSinks().contains(new Sink(method.getMethod(), i))) {
                        Set<Obj> pts = result.getPointsToSet(args.get(i));
                        for(Obj obj : pts) {
                            if(manager.isTaint(obj)) {
                                taintFlows.add(new TaintFlow(manager.getSourceCall(obj), csCallSite.getCallSite(), i));
                            }
                        }
                    }
                }
            });
        });
        return taintFlows;
    }
}
