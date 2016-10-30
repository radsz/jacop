package org.jacop;


import org.jacop.core.*;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Collection;


import static org.junit.Assert.assertEquals;

/**
 * @author Mariusz Świerkot
 */
@RunWith(Parameterized.class)
public class SmallDenseDomainTest {

    private Method prepareMethod;

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
        IntDomain testedDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,3, 5,7, 12,18}});
            assertEquals("{-50000000..0, 4, 8..11, 19..50000000}", testedDomain.complement().toString());

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