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
//**********************************************************************************************************************

        IntDomain smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1, 2}});


        assertEquals(false, smallDomain.contains(createDomain(new Interval(0, 0))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(1, 1))));
//                assertEquals(false, smallDomain.isIntersecting(createDomain(new Interval(3,3))));
//                assertEquals(true, smallDomain.isIntersecting(createDomain(new Interval(2,2))));
        assertEquals(1, smallDomain.getElementAt(0));
        assertEquals(2, smallDomain.getElementAt(1));


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

        assertEquals("{-50000000..0, 4, 8..11, 19..50000000}", smallDomain.complement().toString());

        assertEquals(5, smallDomain.nextValue(3));
        assertEquals(1, smallDomain.previousValue(2));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,3, 5,7, 12,18}});
        assertEquals(1, smallDomain.intersectAdapt(createDomain(new Interval(14,20))));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,3, 5,7, 12,18}});
        assertEquals(1, smallDomain.intersectAdapt(createDomain(new Interval(2,6))));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,3, 5,7, 12,18}});
        assertEquals(1, smallDomain.intersectAdapt(createDomain(new Interval(2,6), new Interval(8,15))));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,3, 5,7, 12,18}});
        assertEquals(0, smallDomain.intersectAdapt(createDomain(new Interval(0,0), new Interval(20,28))));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,3, 5,7, 12,18}});
        assertEquals(1, smallDomain.intersectAdapt(createDomain(new Interval(2,2), new Interval(5,5), new Interval(20,25))));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,3, 5,7, 12,18}});
        assertEquals(1, smallDomain.intersectAdapt(createDomain(new Interval(1,3), new Interval(5,5), new Interval(20,25))));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,3, 5,7, 12,18}});
        assertEquals(2, smallDomain.intersectAdapt(createDomain(new Interval(1,3), new Interval(5,5), new Interval(13,18))));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,3, 5,7, 12,18}});
        assertEquals(1, smallDomain.intersectAdapt(createDomain(new Interval(4,9))));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,3, 5,7, 12,18}});
        assertEquals(0, smallDomain.intersectAdapt(createDomain(new Interval(0,0))));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{1,3, 5,7, 12,18}});
        assertEquals(0, smallDomain.intersectAdapt(createDomain(new Interval(0,0), new Interval(2,2))));





        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{-3,4, 5,5 ,9,10}});
        assertEquals(false, smallDomain.contains(createDomain(new Interval(1, 2),new Interval(6,6))));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0,6,8,10,12,14,16,18,20,22,24,26}});
        assertEquals(0, smallDomain.intersectAdapt(2,2));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0,6,8,10,12,14,16,18,20,22,24,26}});
        assertEquals(0, smallDomain.intersectAdapt(0,0));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0,6,8,10,12,14,16,18,20,22,24,26}});
        assertEquals(1, smallDomain.intersectAdapt(1,9));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0,6,8,10,12,14,16,18,20,22,24,26}});
        assertEquals(-1, smallDomain.intersectAdapt(0,26));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0,6,8,10,12,14,16,18,20,22,24,26}});
        assertEquals(0, smallDomain.intersectAdapt(28,45));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0,6,8,10,12,14,16,18,20,22,24,26}});
        assertEquals(false, smallDomain.isIntersecting(28,45));
        assertEquals(true, smallDomain.isIntersecting(0,0));


        IntDomain testSmallDomain = (IntDomain)prepareMethod.invoke(this, new Object[]{new int[]{0,0,4,6,8,10,12,14,16,18,20,22,24,26}});
        assertEquals(testSmallDomain.toString(), smallDomain.subtract(1,3).toString());

        testSmallDomain = (IntDomain)prepareMethod.invoke(this, new Object[]{new int[]{1,6,8,10,12,14,16,18,20,22,24,26}});
        assertEquals(testSmallDomain.toString(), smallDomain.subtract(0,0).toString());

        testSmallDomain = (IntDomain)prepareMethod.invoke(this, new Object[]{new int[]{0,0}});
        assertEquals(testSmallDomain.toString(), smallDomain.subtract(1,26).toString());

        testSmallDomain = (IntDomain)prepareMethod.invoke(this, new Object[]{new int[]{0,6}});
        assertEquals(testSmallDomain.toString(), smallDomain.subtract(8,26).toString());

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0,6,8,10,12,14,16,18,20,22,24,26}});
        assertEquals(1, smallDomain.intersectAdapt(createDomain(new Interval(-4,3), new Interval(9,18))));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{0,6,8,10,12,14,16,18,20,22,24,26}});
        assertEquals(1, smallDomain.intersectAdapt(createDomain(new Interval(-4,1))));



/*

/*//**********************************************************************************************************************

//        smallDomain = new SmallDenseDomain(1,3);
//        smallDomain.addDom(new SmallDenseDomain(5,7));
//        smallDomain.addDom(new SmallDenseDomain(12,18));
        smallDomain = (IntDomain)prepareMethod.invoke(this, new Object[]{new int[]{1, 3, 5, 7, 12, 18}});

        assertEquals(false, smallDomain.contains(createDomain(new Interval(0, 0))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(1, 1))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(2, 2))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(2, 3))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 4))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(1, 3), new Interval(7, 10), new Interval(12, 17))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(-1, 1), new Interval(7, 7), new Interval(9, 15), new Interval(4, 5))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 2), new Interval(6, 6), new Interval(15, 18), new Interval(8, 10))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(11, 15), new Interval(1, 7))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(1, 2), new Interval(5, 6), new Interval(12, 15), new Interval(17, 18))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(-11, 2), new Interval(6, 6), new Interval(8, 15))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(0, 5), new Interval(13, 13), new Interval(7, 7), new Interval(18, 20))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(11, 15), new Interval(1, 7), new Interval(22, 33))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(-4, 5), new Interval(7, 10), new Interval(13, 20))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(1, 1), new Interval(6, 7), new Interval(12, 13), new Interval(15, 17))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(-1, -1), new Interval(2, 5), new Interval(13, 15))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(-15, 2), new Interval(7, 8), new Interval(10, 15), new Interval(17, 20))));


/*//***********************************************************************************************************************


//        smallDomain = new SmallDenseDomain(-3,4);
//        smallDomain.addDom(new SmallDenseDomain(6,6));
//        smallDomain.addDom(new SmallDenseDomain(9,10));

        smallDomain = (IntDomain) prepareMethod.invoke(this, new Object[]{new int[]{-3, 4, 6, 6, 9, 10}});

        assertEquals(true, smallDomain.contains(createDomain(new Interval(0, 0))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(1, 1))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(2, 2))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(2, 3))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(2, 4))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(-3, 2))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(-3, 5))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(10, 10))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(-3, -3), new Interval(5, 6))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(-3, 4), new Interval(6, 6), new Interval(9, 10))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(-3, 4), new Interval(6, 6), new Interval(10, 10))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(-3, 4))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(-3, 5), new Interval(12, 16), new Interval(-10, -5), new Interval(8, 8))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(-3, -3), new Interval(6, 6), new Interval(0, 1), new Interval(8, 12))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 4), new Interval(6, 6), new Interval(8, 12), new Interval(-9, 0))));


/*//**********************************************************************************************************************//**//**//**//**//**//**//**//*

//        smallDomain = new SmallDenseDomain(10,10);
        smallDomain = (IntDomain)prepareMethod.invoke(this,  new Object[]{new int[]{10, 10}});

        assertEquals(false, smallDomain.contains(createDomain(new Interval(0, 0))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(1, 1))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 2))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 3))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 4))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(3, 5))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 16))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(5, 7))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 8))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(6, 9))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(3, 4))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(3, 5))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(3, 6))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(10, 10))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(-10, 10))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(1, 12))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(1, 12))));


/*//**********************************************************************************************************************//**//**//**//**//**//**//**//*

//     smallDomain = new SmallDenseDomain(10,10);
//     smallDomain.addDom(new SmallDenseDomain(12,12));
        smallDomain = (IntDomain)prepareMethod.invoke(this, new Object[]{new int[]{10, 10, 12, 12}});

        assertEquals(false, smallDomain.contains(createDomain(new Interval(0, 0))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(1, 1))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 2))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 3))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 4))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(10, 10))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(10, 10), new Interval(12, 12))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(11, 12), new Interval(14, 15))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(1, 7), new Interval(10, 14))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(11, 12), new Interval(10, 12))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(-1, 1), new Interval(10, 22), new Interval(-5, -3))));


/*//**********************************************************************************************************************//**//**//**//**//**//**//**//*

//       smallDomain = new SmallDenseDomain(1,2);
//       smallDomain.addDom(new SmallDenseDomain(5,5));
        smallDomain = (IntDomain)prepareMethod.invoke(this, new Object[]{new int[]{1, 2, 5, 5}});

        assertEquals(true, smallDomain.contains(createDomain(new Interval(1, 2), new Interval(5, 5))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(0, 0))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(1, 1))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(2, 2))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 3))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 5))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(1, 4))));


/*//**********************************************************************************************************************//**//*


//     smallDomain = new SmallDenseDomain(1,4);
//     smallDomain.addDom(new SmallDenseDomain(6,9));
//     smallDomain.addDom(new SmallDenseDomain(12,15));
        smallDomain = (IntDomain)prepareMethod.invoke(this, new Object[]{new int[]{1, 4, 6, 9, 12, 15}});

        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 4), new Interval(6, 9), new Interval(12, 14), new Interval(0, 0))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(1, 1))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(2, 2))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(2, 3))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(2, 4))));


/*//**********************************************************************************************************************

//     smallDomain = new SmallDenseDomain(2,10);
//     smallDomain.addDom(new SmallDenseDomain(12,12));
//     smallDomain.addDom(new SmallDenseDomain(14,15));
//     smallDomain.addDom(new SmallDenseDomain(17,18));
//     smallDomain.addDom(new SmallDenseDomain(20,25));

        smallDomain = (IntDomain)prepareMethod.invoke(this, new Object[]{new int[]{2, 10, 12, 12, 14, 15, 17, 18, 20, 25}});

        assertEquals(false, smallDomain.contains(createDomain(new Interval(0, 0))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(1, 1))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(2, 2))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(2, 3))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(2, 4))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(20, 20))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(20, 24), new Interval(14, 14), new Interval(12, 12), new Interval(2, 3), new Interval(5, 8))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 5), new Interval(7, 9), new Interval(11, 16), new Interval(18, 22))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(-1, 0), new Interval(14, 25), new Interval(2, 12), new Interval(-5, -3))));


/*//***********************************************************************************************************************//**//**//**//**//**//**//**//**//**//**//**//**//**//**//**//*

//     smallDomain = new SmallDenseDomain(5,5);
//     smallDomain.addDom(new SmallDenseDomain(7,19));
//     smallDomain.addDom(new SmallDenseDomain(21,21));
        smallDomain = (IntDomain)prepareMethod.invoke(this, new Object[]{new int[]{5, 5, 7, 19, 21, 21}});

        assertEquals(false, smallDomain.contains(createDomain(new Interval(0, 0))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(1, 1))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 2))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 3))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(2, 4))));
        assertEquals(true, smallDomain.contains(createDomain(new Interval(5, 5), new Interval(8, 17), new Interval(21, 21))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(11, 18), new Interval(7, 9), new Interval(-5, 5))));
        assertEquals(false, smallDomain.contains(createDomain(new Interval(15, 17), new Interval(-15, -5))));*/



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