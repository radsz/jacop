package org.jacop;


import org.jacop.core.IntDomain;
import org.jacop.core.Interval;
import org.jacop.core.IntervalDomain;
import org.jacop.core.SmallDenseDomain;
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
public class SmallDenseDomainTestIntersect {

    private Method prepareMethod;

    public SmallDenseDomainTestIntersect(String prepareMethodName) throws NoSuchMethodException {
        Class<SmallDenseDomainTestIntersect> cls = (Class<SmallDenseDomainTestIntersect>) this.getClass();
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
//**********************************************************************************************************************

        IntDomain smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2}});


        IntDomain testSmallDomain1 = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{2,2}});
            assertEquals(testSmallDomain1.toString(), smallDomain.intersect(2,3).toString());

        testSmallDomain1 = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,2}});
            assertEquals(testSmallDomain1.toString(), smallDomain.intersect(0,25).toString());

        testSmallDomain1 = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,2}});
            assertEquals(testSmallDomain1.toString(), smallDomain.intersect(1,2).toString());

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2}});
            assertEquals(0, smallDomain.intersectAdapt(createDomain(new Interval(2,4))));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,3, 5,7, 12,18}});
        testSmallDomain1 = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{2,3, 5,7, 12,14}});
            assertEquals(testSmallDomain1.toString(), smallDomain.intersect(2,14).toString());

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,3, 5,7, 12,18}});
        testSmallDomain1 = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{15,15}});
             assertEquals(testSmallDomain1.toString(), smallDomain.intersect(15,15).toString());


    }

    public IntDomain createDomain(Interval... intervals)
    {
        IntDomain result = new IntervalDomain();

        for(Interval interval : intervals){
            result.addDom(new IntervalDomain(interval.min(),interval.max()));
        }
        System.out.println("Domain " + result);

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


            System.out.println("prepareSmallDenseDomain " + domain);


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


        System.out.println("prepareIntervalDomain " + domain);


        return domain;
    }


}