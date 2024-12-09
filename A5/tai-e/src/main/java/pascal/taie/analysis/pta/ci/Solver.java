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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (!callGraph.addReachableMethod(method))
            return;
        method.getIR().getStmts().forEach(stmt -> stmt.accept(stmtProcessor));
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        // via visitor pattern, then finish me
        public Void visit(New stmt) {
            workList.addEntry(pointerFlowGraph.getVarPtr(stmt.getLValue()), new PointsToSet(heapModel.getObj(stmt)));
            return null;
        }

        public Void visit(Copy stmt) {
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }

        public Void visit(StoreField stmt) {
            if (!stmt.isStatic())
                return null;
            JField field = stmt.getFieldRef().resolve();
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getStaticField(field));
            return null;
        }

        public Void visit(LoadField stmt) {
            if (!stmt.isStatic())
                return null;
            JField field = stmt.getFieldRef().resolve();
            addPFGEdge(pointerFlowGraph.getStaticField(field), pointerFlowGraph.getVarPtr(stmt.getLValue()));
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
                // TODO: finish it
                if (callGraph.addEdge(new Edge<Invoke, JMethod>(CallGraphs.getCallKind(stmt), stmt, m))) {
                    addReachable(m);
                    for (int i = 0; i < m.getParamCount(); i++) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue().getArg(i)),
                                pointerFlowGraph.getVarPtr(m.getIR().getParam(i)));
                    }
                    if (stmt.getLValue() != null) {
                        for (Var returnVar : m.getIR().getReturnVars()) {
                            addPFGEdge(pointerFlowGraph.getVarPtr(returnVar),
                                    pointerFlowGraph.getVarPtr(stmt.getLValue()));
                        }
                    }
                }
            }
            return null;
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
            if (entry.pointer() instanceof VarPtr varPtr) {
                var tar = varPtr.getVar();
                deltaSet.forEach(obj -> {
                    tar.getStoreFields().forEach(stmt -> {
                        addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()),
                                pointerFlowGraph.getInstanceField(obj, stmt.getFieldRef().resolve()));
                    });
                    tar.getLoadFields().forEach(stmt -> {
                        addPFGEdge(pointerFlowGraph.getInstanceField(obj, stmt.getFieldRef().resolve()),
                                pointerFlowGraph.getVarPtr(stmt.getLValue()));
                    });
                    tar.getStoreArrays().forEach(stmt -> {
                        addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getArrayIndex(obj));
                    });
                    tar.getLoadArrays().forEach(stmt -> {
                        addPFGEdge(pointerFlowGraph.getArrayIndex(obj), pointerFlowGraph.getVarPtr(stmt.getLValue()));
                    });
                    processCall(tar, obj);
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
        // removeAll?
        PointsToSet deltaSet = new PointsToSet();
        PointsToSet pointerSet = pointer.getPointsToSet();
        pointsToSet.forEach(obj -> {
            if (!pointerSet.contains(obj)) {
                deltaSet.addObject(obj);
            }
        });
        if (!deltaSet.isEmpty()) {
            deltaSet.forEach(obj -> pointerSet.addObject(obj));
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> workList.addEntry(succ, deltaSet));
            return deltaSet;
        }
        return null;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        var.getInvokes().forEach(stmt -> {
            JMethod m = resolveCallee(recv, stmt);
            workList.addEntry(pointerFlowGraph.getVarPtr(m.getIR().getThis()), new PointsToSet(recv));
            if (callGraph.addEdge(new Edge<Invoke, JMethod>(CallGraphs.getCallKind(stmt), stmt, m))) {
                addReachable(m);
                for (int i = 0; i < m.getParamCount(); i++) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue().getArg(i)),
                            pointerFlowGraph.getVarPtr(m.getIR().getParam(i)));
                }
                if (stmt.getLValue() != null) {
                    for (Var returnVar : m.getIR().getReturnVars()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(returnVar),
                                pointerFlowGraph.getVarPtr(stmt.getLValue()));
                    }
                }
            }
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
