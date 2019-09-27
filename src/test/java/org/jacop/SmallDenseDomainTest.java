package org.jacop;

import org.jacop.constraints.In;
import org.jacop.core.*;
import org.junit.Before;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.mockito.Mock;
import org.mockito.Mockito;
import org.mockito.Spy;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Collection;


import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static org.mockito.Mockito.*;
import static org.mockito.MockitoAnnotations.initMocks;

/**
 * @author Mariusz Świerkot
 */
@RunWith(Parameterized.class)
public class SmallDenseDomainTest {

    private Method prepareMethod;

    @SuppressWarnings("unchecked")
    public SmallDenseDomainTest(String prepareMethodName) throws NoSuchMethodException {
        Class<SmallDenseDomainTest> cls = (Class<SmallDenseDomainTest>) this.getClass();
        prepareMethod = cls.getMethod(prepareMethodName, int[].class);
    }

    @Parameterized.Parameters
    public static Collection parametricTest() {

        return Arrays.asList(
                new String[]{"prepareSmallDenseDomain"},
                new String[]{"prepareIntervalDomain"});
    }


    @Test
    public void testContains() throws Exception {

        System.out.println("Contains function test");
        IntDomain testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2}});

            assertEquals(false, testedDomain.contains(createDomain(new Interval(0, 0))));
            assertEquals(true, testedDomain.contains(createDomain(new Interval(1, 1))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{-3,4, 5,5 ,9,10}});

            System.out.println("Test Complement function");
            assertEquals(false, testedDomain.contains(createDomain(new Interval(1, 2),new Interval(6,6))));

           }



    @Test
    public void testComplement() throws Exception {
        System.out.println("Complement function test");
        IntDomain testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 12, 18}});
            assertEquals("{" + IntDomain.MinInt + "..0, 4, 8..11, 19.." + IntDomain.MaxInt + "}", testedDomain.complement().toString());

    }

    @Test
    public void testGetElementAt() throws Exception {
        System.out.println("GetElementAt function test");
        IntDomain testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2}});
            assertEquals(1, testedDomain.getElementAt(0));
            assertEquals(2, testedDomain.getElementAt(1));


    }

    @Test
    public void testIntersect() throws Exception {
        System.out.println("Intersect function test");

        IntDomain testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2}});

        IntDomain goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{2,2}});
        assertEquals(goldenResultDomain.toString(), testedDomain.intersect(2,3).toString());

        goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,2}});
        assertEquals(goldenResultDomain.toString(), testedDomain.intersect(0,25).toString());

        goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,2}});
        assertEquals(goldenResultDomain.toString(), testedDomain.intersect(1,2).toString());

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2}});
        assertEquals(0, testedDomain.intersectAdapt(createDomain(new Interval(2,4))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,3, 5,7, 12,18}});
        goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{2,3, 5,7, 12,14}});
        assertEquals(goldenResultDomain.toString(), testedDomain.intersect(2,14).toString());

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,3, 5,7, 12,18}});
        goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{15,15}});
        assertEquals(goldenResultDomain.toString(), testedDomain.intersect(15,15).toString());

    }


    @Test
    public void testIntersectAdapt() throws Exception {

        System.out.println("IntersectAdapt function test");
        IntDomain testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2}});
        assertEquals(0, testedDomain.intersectAdapt(createDomain(new Interval(2, 4))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 12, 18}});
        assertEquals(1, testedDomain.intersectAdapt(createDomain(new Interval(14, 20))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 12, 18}});
        assertEquals(1, testedDomain.intersectAdapt(createDomain(new Interval(2, 6))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 12, 18}});
        assertEquals(1, testedDomain.intersectAdapt(createDomain(new Interval(2, 6), new Interval(8, 15))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 12, 18}});
        assertEquals(0, testedDomain.intersectAdapt(createDomain(new Interval(0, 0), new Interval(20, 28))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 12, 18}});
        assertEquals(1, testedDomain.intersectAdapt(createDomain(new Interval(2, 2), new Interval(5, 5), new Interval(20, 25))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 12, 18}});
        assertEquals(1, testedDomain.intersectAdapt(createDomain(new Interval(1, 3), new Interval(5, 5), new Interval(20, 25))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 12, 18}});
        assertEquals(2, testedDomain.intersectAdapt(createDomain(new Interval(1, 3), new Interval(5, 5), new Interval(13, 18))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 12, 18}});
        assertEquals(1, testedDomain.intersectAdapt(createDomain(new Interval(4, 9))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 12, 18}});
        assertEquals(0, testedDomain.intersectAdapt(createDomain(new Interval(0, 0))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 12, 18}});
        assertEquals(0, testedDomain.intersectAdapt(createDomain(new Interval(0, 0), new Interval(2, 2))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        assertEquals(0, testedDomain.intersectAdapt(2, 2));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        assertEquals(0, testedDomain.intersectAdapt(0, 0));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        assertEquals(1, testedDomain.intersectAdapt(1, 9));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        assertEquals(-1, testedDomain.intersectAdapt(0, 26));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        assertEquals(0, testedDomain.intersectAdapt(28, 45));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        assertEquals(1, testedDomain.intersectAdapt(createDomain(new Interval(-4, 3), new Interval(9, 18))));

        testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26}});
        assertEquals(1, testedDomain.intersectAdapt(createDomain(new Interval(-4, 1))));

    }

    @Test
    public void testIsIntersecting() throws Exception {

        System.out.println("IsIntersecting function test");
        IntDomain testedDomain  = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0,6,8,10,12,14,16,18,20,22,24,26}});
            assertEquals(false, testedDomain.isIntersecting(28,45));
            assertEquals(true, testedDomain.isIntersecting(0,0));
            assertEquals(true, testedDomain.isIntersecting(0,26));
        }

    @Test
    public void testSubtract() throws Exception {

        System.out.println("Subtract function test");
        IntDomain testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0,6,8,10,12,14,16,18,20,22,24,26}});
        IntDomain goldenResultDomain = (IntDomain)prepareMethod.invoke(this, new Object[]{new int[]{0,0,4,6,8,10,12,14,16,18,20,22,24,26}});
             assertEquals(goldenResultDomain.toString(), testedDomain.subtract(1,3).toString());

        goldenResultDomain = (IntDomain)prepareMethod.invoke(this, new Object[]{new int[]{1,6,8,10,12,14,16,18,20,22,24,26}});
             assertEquals(goldenResultDomain.toString(), testedDomain.subtract(0,0).toString());

             goldenResultDomain = (IntDomain)prepareMethod.invoke(this, new Object[]{new int[]{0,0}});
             assertEquals(goldenResultDomain.toString(), testedDomain.subtract(1,26).toString());

             goldenResultDomain = (IntDomain)prepareMethod.invoke(this, new Object[]{new int[]{0,6}});
             assertEquals(goldenResultDomain.toString(), testedDomain.subtract(8,26).toString());

         }


    @Test
    public void testNextValue() throws Exception {

        System.out.println("NextValue function test");

        IntDomain goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,3, 5,7, 12,18}});
        assertEquals(5, goldenResultDomain.nextValue(3));
    }

    @Test
    public void testPreviousValue() throws Exception {

        System.out.println("previousValue function test");

        IntDomain goldenResultDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,3, 5,7, 12,18}});
        assertEquals(1, goldenResultDomain.previousValue(2));
    }

    @Mock
    IntVar var;


    IntDomain intervalDomain;
    @Before
    public void setUp() throws InvocationTargetException, IllegalAccessException {
        initMocks(this);
        intervalDomain = new IntervalDomain();

    }

    @Test
    public void testinterval() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2}});
        intervalDomain.inComplement(100, var ,2);

        verify(var).domainHasChanged(IntDomain.GROUND);

    }

    @Test
    public void testinterval2() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2}});
        intervalDomain.inComplement(100, var ,1);

        verify(var).domainHasChanged(IntDomain.GROUND);

    }

    @Test
    public void testinterval3() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,1);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test
    public void testinterval4() throws InvocationTargetException, IllegalAccessException {
        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2, 4, 10}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,2);

        verify(var).domainHasChanged(IntDomain.ANY);

    }

    @Test
    public void testinterval5() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2, 4, 10}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,5);

        verify(var).domainHasChanged(IntDomain.ANY);
    }

    @Test
    public void testinterval6() throws InvocationTargetException, IllegalAccessException {
        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2, 4, 10}});
        intervalDomain.inComplement(100, var ,5);

        verify(var).domainHasChanged(IntDomain.ANY);

    }


    @Test
    public void testinterval7() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 5, 7, 10}});
        intervalDomain.inComplement(100, var, 5);

        verify(var).domainHasChanged(IntDomain.ANY);

    }

    @Test
    public void testinterval8() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 5, 7, 10}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var, 5);

        verify(var).domainHasChanged(IntDomain.ANY);

    }

    @Test
    public void testinterval9() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{5, 5, 7, 7}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var, 5);

        verify(var).domainHasChanged(IntDomain.GROUND);

    }


    @Test
    public void testinterval10() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 9, 20}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var, 5);

        verify(var).domainHasChanged(IntDomain.ANY);

    }

    @Test
    public void testinterval11() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 9, 20}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var, 1);

        verify(var).domainHasChanged(IntDomain.BOUND);

    }


    @Test
    public void testinterval12() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 9, 20}});
        intervalDomain.inComplement(100, var, 1);

        verify(var).domainHasChanged(IntDomain.BOUND);

    }

    @Test
    public void testinterval13() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 9, 20}});
        intervalDomain.inComplement(100, var, 7);

        verify(var).domainHasChanged(IntDomain.ANY);

    }

    @Test
    public void testinterval14() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0, 0, 2, 2}});
        intervalDomain.inComplement(100, var, 0);

        verify(var).domainHasChanged(IntDomain.GROUND);

    }
    @Test
    public void testinterval15() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 5 }});
        intervalDomain.inComplement(100, var, 5);

        verify(var).domainHasChanged(IntDomain.BOUND);

    }

    @Test
    public void testinterval16() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 5, 7, 9, 11, 20}});
        intervalDomain.inComplement(100, var, 7);

        verify(var).domainHasChanged(IntDomain.ANY);
    }

    @Test
    public void testinterval17() throws InvocationTargetException, IllegalAccessException {
        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2, 4, 10}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,10);

        verify(var).domainHasChanged(IntDomain.BOUND);

    }


    @Test
    public void testinterval18() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 5}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var, 5);

        verify(var).domainHasChanged(IntDomain.BOUND);

    }

    @Test
    public void testinterval19() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7}});
        intervalDomain.inComplement(100, var, 7);

        verify(var).domainHasChanged(IntDomain.BOUND);

    }

    @Test
    public void testinterval20() throws InvocationTargetException, IllegalAccessException {
        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,2);
        verify(var).domainHasChanged(IntDomain.GROUND);

    }

    @Test
    public void testinterval21() throws InvocationTargetException, IllegalAccessException {
        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,2,4,10,12,12}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,5);

        verify(var).domainHasChanged(IntDomain.ANY);

    }

    @Test
    public void testinterval22() throws InvocationTargetException, IllegalAccessException {
        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,2,4,10,12,12,15,22}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,5);

        verify(var).domainHasChanged(IntDomain.ANY);

    }


    @Test
    public void testinterval23() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2, 4, 10}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,1,2);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test
    public void testinterval24() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2, 4, 15}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,5,5);

        verify(var).domainHasChanged(IntDomain.ANY);
    }

    @Test
    public void testinterval25() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2, 4, 10, 12, 33}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,2,11);

        verify(var).domainHasChanged(IntDomain.ANY);

    }
    public void testinterval26() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 20}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,2,11);

        verify(var).domainHasChanged(IntDomain.ANY);
    }




    @Test
    public void testinterval27() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{3, 6}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,2,4);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test
    public void testinterval28() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 20, 22, 24, 26, 28, 30, 32, 34, 36}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,2,11);

        verify(var).domainHasChanged(IntDomain.ANY);
    }
    @Test
    public void testinterval29() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{3, 6}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,2,5);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test
    public void testinterval30() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2, 4, 10}});
        intervalDomain.inComplement(100, var ,1,2);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }


    @Test
    public void testinterval31() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2, 4, 10}});
        intervalDomain.inComplement(100, var ,2,4);

        verify(var).domainHasChanged(IntDomain.ANY);
    }

    @Test
    public void testinterval32() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2, 4, 10}});
        intervalDomain.inComplement(100, var ,2,11);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test
    public void testinterval33() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 20}});
        intervalDomain.inComplement(100, var ,2,11);

        verify(var).domainHasChanged(IntDomain.ANY);
    }

    @Test
    public void testinterval34() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{3, 6}});
        intervalDomain.inComplement(100, var ,2,4);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test
    public void testinterval35() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{3, 5}});
        intervalDomain.inComplement(100, var ,2,4);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }


    @Test
    public void testinterval36() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2, 4, 10}});
        intervalDomain.inComplement(100, var ,1,9);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test
    public void testinterval37() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{10, 20, 30, 40}});
        intervalDomain.inComplement(100, var ,25,50);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }


    @Test
    public void testinterval38() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{10, 20, 30, 40}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,5,35);
        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test
    public void testinterval39() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{10, 20, 30, 40}});
        intervalDomain.inComplement(100, var ,5,11);
        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test
    public void testinterval40() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{10, 20}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,11,41);
        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test
    public void testinterval41() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0, 0, 3, 6, 7, 18}});
        intervalDomain.inComplement(100, var ,2,4);

        verify(var).domainHasChanged(IntDomain.ANY);
    }

    @Test
    public void testinterval42() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{18, 20,22,23}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,18,22);
        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test
    public void testinterval43() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0,0,4,4,16,26}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var ,5,17);

        verify(var).domainHasChanged(IntDomain.ANY);
    }

    @Test
    public void testinterval44() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2, 4, 10}});
        intervalDomain.setStamp(100);
        intervalDomain.inComplement(100, var, 3, 6);


        verify(var).domainHasChanged(IntDomain.ANY);
    }


    @Test public void testinterval37b() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
        intervalDomain.in(100, var, 11, 50);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval46() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
        intervalDomain.in(100, var, 35, 50);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval47() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
        intervalDomain.in(100, var, 9, 11);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval48() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
        intervalDomain.in(100, var, 9, 21);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval49() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
        intervalDomain.in(100, var, 9, 31);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval50() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
        intervalDomain.in(100, var, 11, 31);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval51() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
        intervalDomain.inMax(100, var, 11);//in(100, var, 29, 41);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval52() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
        intervalDomain.inMax(100, var, 21);//in(100, var, 29, 41);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval53() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
        intervalDomain.inMax(100, var, 32);//in(100, var, 29, 41);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval54() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
        intervalDomain.inMin(200, var, 19);
        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval55() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
        intervalDomain.inMin(200, var, 21);
        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval56() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
        intervalDomain.inShift(100, var, intervalDomain, 2);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval57() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
        intervalDomain.inShift(100, var, intervalDomain, 15);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }


    @Test public void testinterval58() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
        intervalDomain.inValue(100,var, 11);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }


    @Test public void testinterval59() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 11, 13, 15}});
        intervalDomain.in(100, var, 14, 15);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }


    @Test public void testinterval60() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 10, 12, 20, 22, 22}});
        intervalDomain.in(100, var, 10, 11);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test public void testinterval61() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 10, 12, 20, 22, 22}});
        intervalDomain.in(100, var, 22, 23);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }


    @Test public void testinterval62() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 10, 12, 12, 22, 22}});
        intervalDomain.in(100, var, 12, 20);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test public void testinterval63() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 10, 12, 12, 22, 22}});
        intervalDomain.in(100, var, 10, 11);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test public void testinterval64() throws InvocationTargetException, IllegalAccessException {

         intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[] {new int[] {10, 20, 30, 40}});
         intervalDomain.in(100, var, 10,10);

         verify(var).domainHasChanged(IntDomain.GROUND);
            }

    @Test public void testinterval65() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{10, 11, 13, 15}});
        intervalDomain.in(100, var, 10, 11);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval66() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{10, 11, 13, 15}});
        intervalDomain.in(100, var, 14, 15);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }


    @Test public void testinterval67() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{10, 11, 13, 15}});
        intervalDomain.in(100, var, 9, 14);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval68() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{10, 11}});
        intervalDomain.in(100, var, 11, 11);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }


    @Test public void testinterval69() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{10, 11}});
        intervalDomain.in(100, var, 10, 10);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test public void testinterval70() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{10, 12}});
        intervalDomain.in(100, var, 11, 11);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test public void testinterval71() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{10, 12, 14, 21}});
        intervalDomain.inShift(100, var, intervalDomain, 11);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test public void testinterval72() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 1, 3, 3}});
        intervalDomain.in(100, var,  -1 , 1);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }


    @Test public void testinterval73() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 1, 3, 3}});
        intervalDomain.in(100, var,  -1 , 2);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test public void testinterval74() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{-10, -10, 14, 21}});
        intervalDomain.inShift(100, var, intervalDomain, 6);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval75() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{-2, -2, -1, -1}});
        intervalDomain.inShift(100, var, intervalDomain, 1);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test public void testinterval76() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{-10, 10}});
        intervalDomain.inShift(100, var, intervalDomain, 5);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval77() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{-10, -5, -3, 10 }});
        intervalDomain.inShift(100, var, intervalDomain, 5);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval78() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{-10, -5, -3, 10 }});
        intervalDomain.in(100, var, -10, -10);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test public void testinterval79() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{-10, -5, -3, 10 }});
        intervalDomain.in(100, var, -9, 10);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test public void testinterval80() throws InvocationTargetException, IllegalAccessException {

        intervalDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{-10, -5, -3, 10 }});
        intervalDomain.in(100, var, -9, 9);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }



    @Test
    public void testinterval81() throws InvocationTargetException, IllegalAccessException {

        IntDomain intDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2}});
        intDomain.inShift(100, var, intDomain,1);

        verify(var).domainHasChanged(IntDomain.GROUND);
    }

    @Test
    public void testinterval82() throws InvocationTargetException, IllegalAccessException {

        IntDomain intDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 12, 18}});
        intDomain.inShift(100, var, intDomain,1);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }

    @Test
    public void testinterval83() throws InvocationTargetException, IllegalAccessException {

        IntDomain intDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 12, 18}});
        intDomain.inShift(100, var, intDomain,1);

        verify(var).domainHasChanged(IntDomain.BOUND);
    }


    @Test
    public void testinterval84() throws InvocationTargetException, IllegalAccessException {

        IntDomain intDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 12, 18}});

        IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);
        when(intDomain1.contains(anyInt(), anyInt())).thenReturn(true);

        boolean result = intDomain1.contains(intDomain);

        assertTrue(result);

    }


    @Test
    public void testinterval86() throws InvocationTargetException, IllegalAccessException {

        IntDomain intDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 12, 18}});

        IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);

        when(intDomain1.isIntersecting(anyInt(), anyInt())).thenReturn(true);
        when(intDomain1.contains(anyInt())).thenReturn(true);

        boolean result = intDomain1.isIntersecting(intDomain);

        assertTrue(result);

    }


    @Test
    public void testinterval87() throws InvocationTargetException, IllegalAccessException {

        IntDomain intDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{ 5, 5 }});
        IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);

        when(intDomain1.eq(intDomain)).thenReturn(true);
        boolean result = intDomain1.singleton(intDomain);

        assertTrue(result);

    }

    @Test
    public void testinterval88() throws InvocationTargetException, IllegalAccessException {

        IntDomain intDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{5, 5}});

        IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);

        when(intDomain1.getSize()).thenReturn(10);
        boolean result = intDomain1.singleton(intDomain);

        assertFalse(result);

    }

    @Test
    public void testinterval89() throws InvocationTargetException, IllegalAccessException {

        IntDomain intDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{5, 5}});

        IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);

        when(intDomain1.isEmpty()).thenReturn(true);
        boolean result = intDomain1.singleton(intDomain);

        assertFalse(result);

    }


    @Test
    public void testinterval188() throws InvocationTargetException, IllegalAccessException {

        IntDomain intDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 12, 18}});

        IntDomain intDomain1 = mock(IntDomain.class, Mockito.CALLS_REAL_METHODS);

        when(intDomain1.contains(anyInt(), anyInt())).thenReturn(true, true, true, true, true, false  );

        intDomain1.contains(intDomain);
        intDomain1.contains(intDomain);
        intDomain1.contains(intDomain);
        intDomain1.contains(intDomain);
        intDomain1.contains(intDomain);

        boolean result = intDomain1.contains(intDomain);

        assertFalse(result);

    }

    public IntDomain createDomain(Interval... intervals)
    {
        IntDomain result = new IntervalDomain();

        for(Interval interval : intervals){
            result.addDom(new IntervalDomain(interval.min(),interval.max()));
        }


        return result;
    }


    public IntDomain  prepareSmallDenseDomain(int[] intervalList){
        IntDomain domain;

        if(intervalList.length%2 != 0) throw new IllegalArgumentException("List must have an even number of elements" +
                              " since the domain is a list of intervals and each interval is denoted by two elements");
        if(intervalList.length < 2) throw new IllegalArgumentException("List must have at least two elements since the domain" +
                              " must have at least one interval and each interval is denoted by two integers.");

                domain = new SmallDenseDomain(intervalList[0], intervalList[1]);
                for (int i = 2; i < intervalList.length; i += 2) {
                    domain.addDom(new SmallDenseDomain(intervalList[i], intervalList[i + 1]));
                }

        return domain;
    }


    public IntDomain prepareIntervalDomain(int[] intervalList){
        IntDomain domain;

        if(intervalList.length%2 != 0) throw new IllegalArgumentException("List must have an even number of elements" +
                " since the domain is a list of intervals and each interval is denoted by two elements");
        if(intervalList.length < 2) throw new IllegalArgumentException("List must have at least two elements since the domain" +
                " must have at least one interval and each interval is denoted by two integers.");

        domain = new IntervalDomain(intervalList[0], intervalList[1]);
        for (int i = 2; i < intervalList.length; i += 2) {
            domain.addDom(new IntervalDomain(intervalList[i], intervalList[i + 1]));
        }





        return domain;
    }


}
