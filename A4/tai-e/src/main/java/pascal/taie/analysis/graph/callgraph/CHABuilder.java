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

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

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
        Queue<JMethod> WL = new LinkedList<>();
        WL.offer(entry);
        while (!WL.isEmpty()) {
            JMethod m = WL.poll();
            if (!callGraph.reachableMethods.contains(m)) {
                callGraph.addReachableMethod(m);
                for (Invoke callsite : callGraph.getCallSitesIn(m)) {
                    Set<JMethod> T = resolve(callsite);
                    for (JMethod m1 : T) {
                        WL.offer(m1);
                        callGraph.addEdge(new Edge<Invoke, JMethod>(CallGraphs.getCallKind(callsite), callsite, m1));
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
        Set<JMethod> T = new HashSet<>();
        MethodRef method = callSite.getMethodRef();
        if (CallGraphs.getCallKind(callSite) == CallKind.STATIC) {
            T.add(method.getDeclaringClass().getDeclaredMethod(method.getSubsignature()));
        } else if (CallGraphs.getCallKind(callSite) == CallKind.SPECIAL) {
            T.add(dispatch(method.getDeclaringClass(), method.getSubsignature()));
            // could be null
        } else if (CallGraphs.getCallKind(callSite) == CallKind.VIRTUAL
                || CallGraphs.getCallKind(callSite) == CallKind.INTERFACE) {
            // bfs
            Queue<JClass> q = new LinkedList<>();
            JClass c = method.getDeclaringClass();
            q.offer(c);
            while (!q.isEmpty()) {
                JClass ci = q.poll();
                T.add(dispatch(ci, method.getSubsignature()));
                if (!ci.isInterface()) {
                    q.addAll(hierarchy.getDirectSubclassesOf(ci));
                } else {
                    q.addAll(hierarchy.getDirectSubinterfacesOf(ci));
                    q.addAll(hierarchy.getDirectImplementorsOf(ci));
                }
            }
        }
        T.remove(null);
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     *         can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if (jclass == null)
            return null;
        if (jclass.getDeclaredMethod(subsignature) == null) {
            return dispatch(jclass.getSuperClass(), subsignature);
        } else {
            if (jclass.getDeclaredMethod(subsignature).isAbstract()) {
                return dispatch(jclass.getSuperClass(), subsignature);
            } else {
                return jclass.getDeclaredMethod(subsignature);
            }
        }
    }
}
