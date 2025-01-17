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

import java.util.*;

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
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Pair;

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

    private Map<CSVar, Set<Invoke>> taintTransfers;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
        this.taintTransfers = new HashMap<>();
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
        if (!callGraph.addReachableMethod(csMethod))
            return;
        csMethod.getMethod().getIR().getStmts().forEach(stmt -> stmt.accept(new StmtProcessor(csMethod)));
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
            Obj obj = heapModel.getObj(stmt);
            CSObj csobj=csManager.getCSObj(contextSelector.selectHeapContext(csMethod, obj), obj);

            workList.addEntry(csManager.getCSVar(context, stmt.getLValue()),
                    PointsToSetFactory.make(csobj));
            return null;
        }

        public Void visit(Copy stmt) {
            addPFGEdge(csManager.getCSVar(context, stmt.getRValue()), csManager.getCSVar(context, stmt.getLValue()));
            return null;
        }

        public Void visit(StoreField stmt) {
            if (!stmt.isStatic())
                return null;
            JField field = stmt.getFieldRef().resolve();
            addPFGEdge(csManager.getCSVar(context, stmt.getRValue()), csManager.getStaticField(field));
            return null;
        }

        public Void visit(LoadField stmt) {
            if (!stmt.isStatic())
                return null;
            JField field = stmt.getFieldRef().resolve();
            addPFGEdge(csManager.getStaticField(field), csManager.getCSVar(context, stmt.getLValue()));
            return null;
        }

        public Void visit(StoreArray stmt) {
            return null;
        }

        public Void visit(LoadArray stmt) {
            return null;
        }

        public Void visit(Invoke stmt) {
            if (CallGraphs.getCallKind(stmt) == CallKind.STATIC) {
                JMethod m = resolveCallee(null, stmt);
                if(taintAnalysis.getTaintSource(csManager.getCSCallSite(context, stmt).getCallSite(), m) != null && csManager.getCSCallSite(context, stmt).getCallSite().getLValue() != null){
                    Pointer ptr = csManager.getCSVar(csManager.getCSCallSite(context, stmt).getContext(), csManager.getCSCallSite(context, stmt).getCallSite().getLValue());
                    PointsToSet pts = PointsToSetFactory.make(csManager.getCSObj(contextSelector.getEmptyContext(), taintAnalysis.getTaintSource(csManager.getCSCallSite(context, stmt).getCallSite(), m)));
                    workList.addEntry(ptr, pts);
                }
                if (callGraph.addEdge(new Edge<CSCallSite, CSMethod>(
                        CallGraphs.getCallKind(stmt),
                        csManager.getCSCallSite(context, stmt),
                        csManager.getCSMethod(contextSelector.selectContext(csManager.getCSCallSite(context, stmt), m),
                                m)))) {
                    addReachable(csManager.getCSMethod(contextSelector.selectContext((csManager.getCSCallSite(context, stmt)), m), m));
                    for (int i = 0; i < m.getParamCount(); i++) {
                        addPFGEdge(csManager.getCSVar(context, stmt.getRValue().getArg(i)),
                                csManager.getCSVar(contextSelector.selectContext(csManager.getCSCallSite(context,stmt),m), m.getIR().getParam(i)));
                    }
                    if (stmt.getLValue() != null) {
                        for (Var returnVar : m.getIR().getReturnVars()) {
                            addPFGEdge(csManager.getCSVar(contextSelector.selectContext(csManager.getCSCallSite(context,stmt),m), returnVar),
                                    csManager.getCSVar(context, stmt.getLValue()));
                        }
                    }
                }
                transferTaint(csManager.getCSCallSite(context, stmt), m, null);
            }
            List<Stmt> stmts = csMethod.getMethod().getIR().getStmts();
            for(Stmt s: stmts){
                if(s instanceof Invoke inv){
                    inv.getInvokeExp().getArgs().forEach(arg -> {
                        CSVar csvar = csManager.getCSVar(context, arg);
                        Set<Invoke> invokes = taintTransfers.getOrDefault(csvar, new HashSet<>());
                        invokes.add(inv);
                        taintTransfers.put(csvar, invokes);
                    });
                }
            }
            return null;
        }
    }


    private void transferTaint(CSCallSite csCallSite, JMethod callee, CSVar base) {
        Set<Pair<Var, Obj>>res =  taintAnalysis.TaintTransfer(csCallSite, callee, base);
        for(Pair<Var, Obj> pair: res){
            Pointer ptr = csManager.getCSVar(csCallSite.getContext(), pair.first());
            PointsToSet pts = PointsToSetFactory.make(csManager.getCSObj(contextSelector.getEmptyContext(), pair.second()));
            workList.addEntry(ptr, pts);
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            var entry = workList.pollEntry();
            var deltaSet = propagate(entry.pointer(), entry.pointsToSet());
            if (deltaSet == null)
                continue;
            if (entry.pointer() instanceof CSVar csvar) {
                var tar = csvar.getVar();
                deltaSet.forEach(obj -> {
                    tar.getStoreFields().forEach(stmt -> {
                        addPFGEdge(csManager.getCSVar(csvar.getContext(), stmt.getRValue()),
                                csManager.getInstanceField(obj, stmt.getFieldRef().resolve()));
                    });
                    tar.getLoadFields().forEach(stmt -> {
                        addPFGEdge(csManager.getInstanceField(obj, stmt.getFieldRef().resolve()),
                                csManager.getCSVar(csvar.getContext(), stmt.getLValue()));
                    });
                    tar.getStoreArrays().forEach(stmt -> {
                        addPFGEdge(csManager.getCSVar(csvar.getContext(), stmt.getRValue()),
                                csManager.getArrayIndex(obj));
                    });
                    tar.getLoadArrays().forEach(stmt -> {
                        addPFGEdge(csManager.getArrayIndex(obj),
                                csManager.getCSVar(csvar.getContext(), stmt.getLValue()));
                    });
                    processCall(csvar, obj);
                    if(taintAnalysis.isTaint(obj.getObject())) {
                        Set<Invoke> invokes = taintTransfers.getOrDefault(csvar, new HashSet<>());
                        Context ctx = csvar.getContext();
                        for(Invoke inv: invokes){
                            CSCallSite csCallSite = csManager.getCSCallSite(ctx, inv);
                            if(inv.getInvokeExp() instanceof InvokeInstanceExp invokeInstanceExp) {
                                CSVar var = csManager.getCSVar(ctx, invokeInstanceExp.getBase());
                                result.getPointsToSet(var).forEach(recvobj -> {
                                    transferTaint(csCallSite, resolveCallee(recvobj, inv), var);
                                });
                            }
                            else {
                                transferTaint(csCallSite, resolveCallee(null, inv), null);
                            }
                        }
                    }
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet deltaSet = PointsToSetFactory.make();
        pointsToSet.forEach(obj -> {
            if (pointer.getPointsToSet().addObject(obj))
                deltaSet.addObject(obj);
        });
        if (!deltaSet.isEmpty()) {
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> workList.addEntry(succ, deltaSet));
            return deltaSet;
        }
        return null;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        recv.getVar().getInvokes().forEach(stmt -> {
            JMethod m = resolveCallee(recvObj, stmt);
            Context ct = contextSelector.selectContext(csManager.getCSCallSite(recv.getContext(), stmt), recvObj, m);
            workList.addEntry(csManager.getCSVar(ct, m.getIR().getThis()), PointsToSetFactory.make(recvObj));
            if(taintAnalysis.getTaintSource(stmt, m) != null && stmt.getLValue() != null){
                Pointer ptr = csManager.getCSVar(csManager.getCSCallSite(recv.getContext(), stmt).getContext(), stmt.getLValue());
                PointsToSet pts = PointsToSetFactory.make(csManager.getCSObj(contextSelector.getEmptyContext(), taintAnalysis.getTaintSource(stmt, m)));
                workList.addEntry(ptr, pts);
            }
            if (callGraph.addEdge(new Edge<CSCallSite, CSMethod>(CallGraphs.getCallKind(stmt),
                    csManager.getCSCallSite(recv.getContext(), stmt), csManager.getCSMethod(ct, m)))) {
                addReachable(csManager.getCSMethod(ct, m));
                for (int i = 0; i < m.getParamCount(); i++) {
                    addPFGEdge(csManager.getCSVar(recv.getContext(), stmt.getRValue().getArg(i)),
                            csManager.getCSVar(ct, csManager.getCSMethod(ct, m).getMethod().getIR().getParam(i)));
                }
                if (stmt.getLValue() != null) {
                    for (Var returnVar : m.getIR().getReturnVars()) {
                        addPFGEdge(csManager.getCSVar(ct, returnVar),
                                csManager.getCSVar(recv.getContext(), stmt.getLValue()));
                    }
                }
            }
            transferTaint(csManager.getCSCallSite(recv.getContext(), stmt), m, recv);
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
