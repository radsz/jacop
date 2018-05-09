/*
 * IntDomainTest.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2008 Krzysztof Kuchcinski and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop;

import org.jacop.core.*;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.mockito.Mock;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Collection;

import static org.junit.Assert.assertEquals;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.MockitoAnnotations.initMocks;

/**
 * Tests to test different domain operations for IntDomains in particular SmallDenseDomain and IntervalDomain.
 *
 * @author Mariusz Świerkot and Radoslaw Szymanek
 * @version 4.5
 */
@RunWith(Parameterized.class) public class IntDomainTest {

    private Method prepareMethod;

    public IntDomainTest(String prepareMethodName) throws NoSuchMethodException {
        prepareMethod = this.getClass().getMethod(prepareMethodName, int[].class);
    }

    @Parameterized.Parameters public static Collection parametricTest() {
        return Arrays.asList(new String[] {"prepareSmallDenseDomain"}, new String[] {"prepareIntervalDomain"});
    }


    @Test public void testContains() throws Exception {

        IntDomain testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});

        assertEquals(false, testedDomain.contains(createDomain(new Interval(0, 0))));
        assertEquals(true, testedDomain.contains(createDomain(new Interval(1, 1))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {-3, 4, 5, 5, 9, 10}});

        assertEquals(false, testedDomain.contains(createDomain(new Interval(1, 2), new Interval(6, 6))));

    }



    @Test public void testComplement() throws Exception {
        IntDomain testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
        assertEquals("{" + IntDomain.MinInt + "..0, 4, 8..11, 19.." + IntDomain.MaxInt + "}", testedDomain.complement().toString());

    }

    @Test public void testGetElementAt() throws Exception {
        IntDomain testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
        assertEquals(1, testedDomain.getElementAt(0));
        assertEquals(2, testedDomain.getElementAt(1));


    }

    @Test public void testIntersect() throws Exception {

        IntDomain testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});

        IntDomain goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {2, 2}});
        assertEquals(goldenResultDomain.toString(), testedDomain.intersect(2, 3).toString());

        goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
        assertEquals(goldenResultDomain.toString(), testedDomain.intersect(0, 25).toString());

        goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
        assertEquals(goldenResultDomain.toString(), testedDomain.intersect(1, 2).toString());

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
        assertEquals(0, testedDomain.intersectAdapt(createDomain(new Interval(2, 4))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
        goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {2, 3, 5, 7, 12, 14}});
        assertEquals(goldenResultDomain.toString(), testedDomain.intersect(2, 14).toString());

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
        goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {15, 15}});
        assertEquals(goldenResultDomain.toString(), testedDomain.intersect(15, 15).toString());

    }


    @Test public void testIntersectAdapt() throws Exception {

        IntDomain testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
        assertEquals(0, testedDomain.intersectAdapt(createDomain(new Interval(2, 4))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
        assertEquals(1, testedDomain.intersectAdapt(createDomain(new Interval(14, 20))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
        assertEquals(1, testedDomain.intersectAdapt(createDomain(new Interval(2, 6))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
        assertEquals(1, testedDomain.intersectAdapt(createDomain(new Interval(2, 6), new Interval(8, 15))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
        assertEquals(0, testedDomain.intersectAdapt(createDomain(new Interval(0, 0), new Interval(20, 28))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
        assertEquals(1, testedDomain.intersectAdapt(createDomain(new Interval(2, 2), new Interval(5, 5), new Interval(20, 25))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
        assertEquals(1, testedDomain.intersectAdapt(createDomain(new Interval(1, 3), new Interval(5, 5), new Interval(20, 25))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
        assertEquals(2, testedDomain.intersectAdapt(createDomain(new Interval(1, 3), new Interval(5, 5), new Interval(13, 18))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
        assertEquals(1, testedDomain.intersectAdapt(createDomain(new Interval(4, 9))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
        assertEquals(0, testedDomain.intersectAdapt(createDomain(new Interval(0, 0))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
        assertEquals(0, testedDomain.intersectAdapt(createDomain(new Interval(0, 0), new Interval(2, 2))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        assertEquals(0, testedDomain.intersectAdapt(2, 2));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        assertEquals(0, testedDomain.intersectAdapt(0, 0));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        assertEquals(1, testedDomain.intersectAdapt(1, 9));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        assertEquals(-1, testedDomain.intersectAdapt(0, 26));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        assertEquals(0, testedDomain.intersectAdapt(28, 45));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        assertEquals(1, testedDomain.intersectAdapt(createDomain(new Interval(-4, 3), new Interval(9, 18))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        assertEquals(1, testedDomain.intersectAdapt(createDomain(new Interval(-4, 1))));

    }

    @Test public void testIsIntersecting() throws Exception {

        IntDomain testedDomain =
            (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        assertEquals(false, testedDomain.isIntersecting(28, 45));
        assertEquals(true, testedDomain.isIntersecting(0, 0));

    }

    @Test public void testSubtract() throws Exception {

        IntDomain testedDomain =
            (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        IntDomain goldenResultDomain =
            (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 0, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        assertEquals(goldenResultDomain.toString(), testedDomain.subtract(1, 3).toString());

        goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        assertEquals(goldenResultDomain.toString(), testedDomain.subtract(0, 0).toString());

        goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 0}});
        assertEquals(goldenResultDomain.toString(), testedDomain.subtract(1, 26).toString());

        goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 6}});
        assertEquals(goldenResultDomain.toString(), testedDomain.subtract(8, 26).toString());

    }


    @Test public void testNextValue() throws Exception {

        IntDomain goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
        assertEquals(5, goldenResultDomain.nextValue(3));
    }

    @Test public void testPreviousValue() throws Exception {
        IntDomain goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 12, 18}});
        assertEquals(1, goldenResultDomain.previousValue(2));
    }

    private @Mock IntVar var;

    private IntDomain intDomain;

    @Before public void setUp() throws InvocationTargetException, IllegalAccessException {
        initMocks(this);
        intDomain = new IntervalDomain();

    }

    @Test public void testinterval() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
        intDomain.inComplement(100, var, 2);

        verify(var).domainHasChanged(IntDomain.GROUND);

    }

    @Test public void testinterval2() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
        intDomain.inComplement(100, var, 1);

        verify(var).domainHasChanged(IntDomain.GROUND);

    }

    @Test public void testinterval3() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 1);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test public void testinterval4() throws InvocationTargetException, IllegalAccessException {
        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 2);

        verify(var).domainHasChanged(IntDomain.ANY);

    }

    @Test public void testinterval5() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 5);

        verify(var).domainHasChanged(IntDomain.ANY);
    }

    @Test public void testinterval6() throws InvocationTargetException, IllegalAccessException {
        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
        intDomain.inComplement(100, var, 5);

        verify(var).domainHasChanged(IntDomain.ANY);

    }


    @Test public void testinterval7() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 5, 7, 10}});
        intDomain.inComplement(100, var, 5);

        verify(var).domainHasChanged(IntDomain.ANY);

    }

    @Test public void testinterval8() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 5, 7, 10}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 5);

        verify(var).domainHasChanged(IntDomain.ANY);

    }

    @Test public void testinterval9() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {5, 5, 7, 7}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 5);

        verify(var).domainHasChanged(IntDomain.GROUND);

    }


    @Test public void testinterval10() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 9, 20}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 5);

        verify(var).domainHasChanged(IntDomain.ANY);

    }

    @Test public void testinterval11() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 9, 20}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 1);

        verify(var).domainHasChanged(IntDomain.BOUND);

    }


    @Test public void testinterval12() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 9, 20}});
        intDomain.inComplement(100, var, 1);

        verify(var).domainHasChanged(IntDomain.BOUND);

    }

    @Test public void testinterval13() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7, 9, 20}});
        intDomain.inComplement(100, var, 7);

        verify(var).domainHasChanged(IntDomain.ANY);

    }

    @Test public void testinterval14() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 0, 2, 2}});
        intDomain.inComplement(100, var, 0);

        verify(var).domainHasChanged(IntDomain.GROUND);

    }

    @Test public void testinterval15() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 5}});
        intDomain.inComplement(100, var, 5);

        verify(var).domainHasChanged(IntDomain.BOUND);

    }

    @Test public void testinterval16() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 5, 7, 9, 11, 20}});
        intDomain.inComplement(100, var, 7);

        verify(var).domainHasChanged(IntDomain.ANY);
    }

    @Test public void testinterval17() throws InvocationTargetException, IllegalAccessException {
        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 10);

        verify(var).domainHasChanged(IntDomain.BOUND);

    }


    @Test public void testinterval18() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 5}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 5);

        verify(var).domainHasChanged(IntDomain.BOUND);

    }

    @Test public void testinterval19() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 3, 5, 7}});
        intDomain.inComplement(100, var, 7);

        verify(var).domainHasChanged(IntDomain.BOUND);

    }

    @Test public void testinterval20() throws InvocationTargetException, IllegalAccessException {
        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 2);
        verify(var).domainHasChanged(IntDomain.GROUND);

    }

    @Test public void testinterval21() throws InvocationTargetException, IllegalAccessException {
        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10, 12, 12}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 5);

        verify(var).domainHasChanged(IntDomain.ANY);

    }

    @Test public void testinterval22() throws InvocationTargetException, IllegalAccessException {
        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10, 12, 12, 15, 22}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 5);

        verify(var).domainHasChanged(IntDomain.ANY);

    }


    @Test public void testinterval23() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 1, 2);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval24() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 15}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 5, 5);

        verify(var).domainHasChanged(IntDomain.ANY);
    }

    @Test public void testinterval25a() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10, 12, 33}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 2, 11);

        verify(var).domainHasChanged(IntDomain.ANY);

    }

    @Test public void testinterval25b() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 20}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 2, 11);

        verify(var).domainHasChanged(IntDomain.ANY);
    }


    @Test public void testintervalNoEventGenerated() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 1, 12, 20}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 2, 11);

        verify(var, never()).domainHasChanged(IntDomain.ANY);
        verify(var, never()).domainHasChanged(IntDomain.BOUND);
        verify(var, never()).domainHasChanged(IntDomain.GROUND);
    }


    @Test public void testinterval27() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {3, 6}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 2, 4);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval28() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 20, 22, 24, 26, 28, 30, 32, 34, 36}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 2, 11);

        verify(var).domainHasChanged(IntDomain.ANY);
    }

    @Test public void testinterval29() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {3, 6}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 2, 5);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test public void testinterval30() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
        intDomain.inComplement(100, var, 1, 2);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }


    @Test public void testinterval31() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
        intDomain.inComplement(100, var, 2, 4);

        verify(var).domainHasChanged(IntDomain.ANY);
    }

    @Test public void testinterval32() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
        intDomain.inComplement(100, var, 2, 11);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test public void testinterval33() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 20}});
        intDomain.inComplement(100, var, 2, 11);

        verify(var).domainHasChanged(IntDomain.ANY);
    }

    @Test public void testinterval34() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {3, 6}});
        intDomain.inComplement(100, var, 2, 4);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval35() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {3, 5}});
        intDomain.inComplement(100, var, 2, 4);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }


    @Test public void testinterval36() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
        intDomain.inComplement(100, var, 1, 9);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test public void testinterval37() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
        intDomain.inComplement(100, var, 25, 50);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }


    @Test public void testinterval38() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 5, 35);
        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval39() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
        intDomain.inComplement(100, var, 5, 11);
        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval40() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 11, 41);
        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test public void testinterval41() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 0, 3, 6, 7, 18}});
        intDomain.inComplement(100, var, 2, 4);

        verify(var).domainHasChanged(IntDomain.ANY);
    }

    @Test public void testinterval42() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {18, 20, 22, 23}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 18, 22);
        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test public void testinterval43() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {0, 0, 4, 4, 16, 26}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 5, 17);

        verify(var).domainHasChanged(IntDomain.ANY);
    }

    @Test public void testinterval44() throws InvocationTargetException, IllegalAccessException {

        intDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {1, 2, 4, 10}});
        intDomain.setStamp(100);
        intDomain.inComplement(100, var, 3, 6);

        verify(var).domainHasChanged(IntDomain.ANY);
    }

    private IntDomain createDomain(Interval... intervals) {
        IntDomain result = new IntervalDomain();

        for (Interval interval : intervals) {
            result.addDom(new IntervalDomain(interval.min(), interval.max()));
        }

        return result;
    }

    /**
     * It is used by the reflection used by the parametrization parameters. It has to stay public.
     * @param intervalList list of intervals where each two consequtive numbers specify the minimum and maximum of an interval.
     * @return
     */
    public IntDomain prepareSmallDenseDomain(int[] intervalList) {
        IntDomain domain;

        if (intervalList.length % 2 != 0)
            throw new IllegalArgumentException("List must have an even number of elements"
                + " since the domain is a list of intervals and each interval is denoted by two elements");
        if (intervalList.length < 2)
            throw new IllegalArgumentException("List must have at least two elements since the domain"
                + " must have at least one interval and each interval is denoted by two integers.");

        domain = new SmallDenseDomain(intervalList[0], intervalList[1]);
        for (int i = 2; i < intervalList.length; i += 2) {
            domain.addDom(new SmallDenseDomain(intervalList[i], intervalList[i + 1]));
        }

        return domain;
    }

    /**
     * It is used by the reflection used by the parametrization parameters. It has to stay public.
     * @param intervalList list of intervals where each two consequtive numbers specify the minimum and maximum of an interval.
     * @return
     */
    public IntDomain prepareIntervalDomain(int[] intervalList) {
        IntDomain domain;

        if (intervalList.length % 2 != 0)
            throw new IllegalArgumentException("List must have an even number of elements"
                + " since the domain is a list of intervals and each interval is denoted by two elements");
        if (intervalList.length < 2)
            throw new IllegalArgumentException("List must have at least two elements since the domain"
                + " must have at least one interval and each interval is denoted by two integers.");

        domain = new IntervalDomain(intervalList[0], intervalList[1]);
        for (int i = 2; i < intervalList.length; i += 2) {
            domain.addDom(new IntervalDomain(intervalList[i], intervalList[i + 1]));
        }

        return domain;
    }


}
