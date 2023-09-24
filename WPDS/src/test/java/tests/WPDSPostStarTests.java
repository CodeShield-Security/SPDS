/*******************************************************************************
 * Copyright (c) 2018 Fraunhofer IEM, Paderborn, Germany.
 * This program and the accompanying materials are made available under the
 * terms of the Eclipse Public License 2.0 which is available at
 * http://www.eclipse.org/legal/epl-2.0.
 *  
 * SPDX-License-Identifier: EPL-2.0
 *
 * Contributors:
 *     Johannes Spaeth - initial API and implementation
 *******************************************************************************/
package tests;

import static org.junit.Assert.assertEquals;
import static tests.TestHelper.ACC;
import static tests.TestHelper.a;
import static tests.TestHelper.t;
import static tests.TestHelper.waccepts;
import static tests.TestHelper.wnormal;
import static tests.TestHelper.wpop;
import static tests.TestHelper.wpush;

import java.util.Map;

import org.junit.Before;
import org.junit.Test;

import tests.TestHelper.Abstraction;
import tests.TestHelper.StackSymbol;
import wpds.impl.PostStar;
import wpds.impl.Transition;
import wpds.impl.WeightedPAutomaton;
import wpds.impl.WeightedPushdownSystem;

public class WPDSPostStarTests {
    private WeightedPushdownSystem<StackSymbol, Abstraction, NumWeight> pds;

    @Before
    public void init() {
        pds = new WeightedPushdownSystem<StackSymbol, Abstraction, NumWeight>();
    }

    @Test
    public void simple() {
        pds.addRule(wnormal(1, "a", 2, "b", w(2)));
        pds.addRule(wnormal(2, "b", 3, "c", w(3)));
        WeightedPAutomaton<StackSymbol, Abstraction, NumWeight> fa = waccepts(1, "a", w(0));
        pds.poststar(fa);
        assertEquals(fa.getTransitions().size(), 3);
        assertEquals(fa.getStates().size(), 4);
        assertEquals(fa.getWeightFor(t(3, "c", ACC)), w(5));
    }

    @Test
    public void branch() {
        pds.addRule(wnormal(1, "a", 1, "b", w(2)));
        pds.addRule(wnormal(1, "b", 1, "c", w(3)));
        pds.addRule(wnormal(1, "a", 1, "d", w(3)));
        pds.addRule(wnormal(1, "d", 1, "c", w(3)));
        WeightedPAutomaton<StackSymbol, Abstraction, NumWeight> fa = waccepts(1, "a", w(0));
        pds.poststar(fa);
        System.out.println(fa);
        assertEquals(fa.getWeightFor(t(1, "c", ACC)), NumWeight.zero());
        assertEquals(fa.getWeightFor(t(1, "b", ACC)), w(2));
        assertEquals(fa.getWeightFor(t(1, "d", ACC)), w(3));
    }

    @Test
    public void push1() {
        pds.addRule(wnormal(1, "a", 1, "b", w(2)));
        pds.addRule(wpush(1, "b", 1, "c", "d", w(3)));
        pds.addRule(wnormal(1, "c", 1, "e", w(1)));
        pds.addRule(wpop(1, "e", 1, w(5)));
        WeightedPAutomaton<StackSymbol, Abstraction, NumWeight> fa = waccepts(1, "a", w(0));
        pds.poststar(fa);
        System.out.println(fa);
        assertEquals(fa.getWeightFor(t(1, "b", ACC)), w(2));
        assertEquals(fa.getWeightFor(t(1, "d", ACC)), w(11));
        assertEquals(fa.getWeightFor(t(1, "e", a(1, "c"))), w(1));
        Map<Transition<StackSymbol, Abstraction>, NumWeight> weights = fa.getTransitionsToFinalWeights();
//        System.out.println(weights);
//        assertEquals(weights.get(t(1, "e", a(1, "c"))), w(6));

    }

    @Test
    public void push2() {
        pds.addRule(wnormal(1, "a", 2, "b", w(2)));
        pds.addRule(wpush(2, "b", 3, "c", "d", w(3)));
        pds.addRule(wnormal(3, "c", 4, "e", w(1)));
        pds.addRule(wpop(4, "e", 5, w(5)));
        WeightedPAutomaton<StackSymbol, Abstraction, NumWeight> fa = waccepts(1, "a", w(0));
        pds.poststar(fa);
        System.out.println(fa);
        assertEquals(fa.getWeightFor(t(5, "d", ACC)), w(11));
    }

    @Test
    public void twoCall() {
        pds.addRule(wnormal(1, "a", 1, "b", w(1)));
        pds.addRule(wpush(1, "b", 2, "call", "d", w(2)));
        pds.addRule(wnormal(2, "call", 2, "e", w(3)));
        pds.addRule(wpop(2, "e", 3, w(4)));
        pds.addRule(wnormal(3, "d", 1, "f", w(5)));
        pds.addRule(wpush(1, "f", 2, "call", "g", w(6)));
        pds.addRule(wnormal(3, "g", 4, "h", w(7)));
        WeightedPAutomaton<StackSymbol, Abstraction, NumWeight> fa = waccepts(1, "a", w(0));
        pds.poststar(fa);
        System.out.println(fa);
        System.out.println(fa.toDotString());
        assertEquals(w(15), fa.getWeightFor(t(1, "f", ACC)));
        assertEquals(w(7), fa.getWeightFor(t(3, "EPS", a(2, "call"))));
        assertEquals(w(10), fa.getWeightFor(t(3, "d", ACC)));

        assertEquals(w(28), fa.getWeightFor(t(3, "g", ACC)));
        assertEquals(w(35), fa.getWeightFor(t(4, "h", ACC)));
    }

    @Test
    public void oneCall() {
        pds.addRule(wnormal(1, "a", 1, "b", w(1)));
        pds.addRule(wpush(1, "b", 2, "call", "d", w(2)));
        pds.addRule(wnormal(2, "call", 2, "e", w(3)));
        pds.addRule(wpop(2, "e", 3, w(4)));
        WeightedPAutomaton<StackSymbol, Abstraction, NumWeight> fa = waccepts(1, "a", w(0));
        pds.poststar(fa);
        System.out.println(fa);
        assertEquals(w(10), fa.getWeightFor(t(3, "d", ACC)));
    }

    @Test
    public void twoCallOnlyReturnWeight() {
        pds.addRule(wnormal(1, "a", 1, "b", w(0)));
        pds.addRule(wpush(1, "b", 2, "call", "d", w(0)));
        pds.addRule(wnormal(2, "call", 2, "e", w(0)));
        pds.addRule(wpop(2, "e", 3, w(4)));
        pds.addRule(wnormal(3, "d", 3, "f", w(0)));
        pds.addRule(wpush(3, "f", 2, "call", "g", w(0)));
        pds.addRule(wnormal(3, "g", 4, "h", w(0)));
        WeightedPAutomaton<StackSymbol, Abstraction, NumWeight> fa = waccepts(1, "a", w(0));
        pds.poststar(fa);
        System.out.println(fa);
        assertEquals(w(4), fa.getWeightFor(t(3, "f", ACC)));
        assertEquals(w(8), fa.getWeightFor(t(3, "g", ACC)));
        assertEquals(w(8), fa.getWeightFor(t(4, "h", ACC)));
    }

    private static NumWeight w(int i) {
        return new NumWeight(i);
    }
}
