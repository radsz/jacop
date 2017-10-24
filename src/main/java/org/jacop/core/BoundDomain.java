/*
 * BoundDomain.java
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

package org.jacop.core;

import java.util.Iterator;
import java.util.Random;

import org.jacop.constraints.Constraint;

/**
 * Defines interval of numbers which is part of FDV definition which consist of
 * one or several intervals.
 *
 *
 * @author Radoslaw Szymanek and Krzysztof Kuchcinski
 * @version 4.5
 */

public class BoundDomain extends IntDomain implements Cloneable {


    /**
     * The minimal value of the domain.
     */

    public int min;

    /**
     * The maximal value of the domain.
     */

    public int max;

    /**
     * It predefines empty domain so there is no need to constantly create it when
     * needed.
     */
    final static public BoundDomain emptyDomain = new BoundDomain();


    /**
     * It is a constructor which will create an empty Bound domain. An empty domain
     * has minimum larger than maximum.
     */
    public BoundDomain() {
        min = 1;
        max = 0;
    }

    /** Creates a new instance of BoundDomain. It requires min to be smaller
     * or equal to max.
     * @param min it specifies the left bound of the BoundDomain (inclusive).
     * @param max it specifies the right bound of the BoundDomain (inclusive).
     */
    public BoundDomain(int min, int max) {

        assert min <= max;

        this.min = min;
        this.max = max;

        searchConstraints = null;
        searchConstraintsToEvaluate = 0;
        previousDomain = null;
        searchConstraintsCloned = false;

    }


    /**
     * @param i  interval for union operation
     *
     */
    @Override public void unionAdapt(Interval i) {

        if (min < max) {
            if (i.min < min)
                min = i.min;

            if (i.max > max)
                max = i.max;
        } else {

            min = i.min;
            max = i.max;
        }

    }

    /**
     *
     */
    @Override public void addDom(IntDomain domain) {

        if (min < max) {
            if (domain.min() < min)
                min = domain.min();

            if (domain.max() > max)
                max = domain.max();
        } else {

            min = domain.min();
            max = domain.max();

        }
    }

    @Override public void unionAdapt(int min, int max) {

        if (this.min < this.max) {
            if (this.min < min)
                this.min = min;

            if (this.max > max)
                this.max = max;
        } else {
            this.min = min;
            this.max = max;
        }
    }

    @Override public void clear() {
        min = 1;
        max = 0;
    }

    public IntDomain getPreviousDomain() {
        return previousDomain;
    }

    @Override public BoundDomain clone() {

        BoundDomain cloned;

        if (!isEmpty())
            cloned = new BoundDomain(min, max);
        else
            cloned = new BoundDomain();

        cloned.stamp = stamp;
        cloned.previousDomain = previousDomain;

        cloned.searchConstraints = searchConstraints;
        cloned.searchConstraintsToEvaluate = searchConstraintsToEvaluate;

        cloned.modelConstraints = modelConstraints;
        cloned.modelConstraintsToEvaluate = modelConstraintsToEvaluate;

        cloned.searchConstraintsCloned = searchConstraintsCloned;

        return cloned;
    }

    /**
     * It clones this domain.
     * @return clone of this domain.
     */
    public BoundDomain cloneLight() {
        if (!isEmpty())
            return new BoundDomain(min, max);
        else
            return new BoundDomain();
    }

    @Override public IntDomain complement() {

        if (min == IntDomain.MinInt) {

            if (max == IntDomain.MaxInt)
                return new BoundDomain();

            return new BoundDomain(max + 1, IntDomain.MaxInt);
        }

        if (max == IntDomain.MaxInt)
            return new BoundDomain(IntDomain.MinInt, min - 1);

        IntervalDomain complement = new IntervalDomain();
        complement.unionAdapt(IntDomain.MinInt, min - 1);
        complement.unionAdapt(max + 1, IntDomain.MaxInt);

        return complement;
    }

    @Override public boolean contains(IntDomain domain) {

        if (isEmpty())
            if (domain.isEmpty())
                return true;
            else
                return false;

        if (min <= domain.min() && max >= domain.max())
            return true;

        return false;

    }

    @Override public boolean contains(int value) {

        if (min <= value && max >= value)
            return true;

        return false;

    }

    /**
     * It divides the domain by a given constant.
     * @param div the constant by which the domain should be divided.
     * @return the domain obtained by dividing this domain by a given constant.
     */
    public IntDomain divide(int div) {
        return new BoundDomain(div(min, div), max / div);
    }

    private int div(int A, int B) {
        int Div, Rem;

        Div = A / B;
        Rem = A % B;
        return (Rem > 0) ? Div + 1 : Div;
    }

    @Override public int domainID() {
        return BoundDomainID;
    }

    public boolean eq(IntDomain domain) {

        if (domain.isEmpty() && isEmpty())
            return true;

        if (min == domain.min() && max == domain.max() && (max - min + 1) == domain.getSize())
            return true;

        return false;
    }

    @Override public Interval getInterval(int position) {
        if (position == 0)
            return new Interval(min, max);

        return null;
    }

    @Override public int getSize() {
        return max - min + 1;
    }

    @Override public void in(int storeLevel, Var var, int min, int max) {

        assert (min <= max);

        if (this.max < min || this.min > max)
            throw failException;

        if (min <= this.min && max >= this.max)
            return;

        if (stamp == storeLevel) {

            if (this.min < min)
                this.min = min;

            if (this.max > max)
                this.max = max;

            if (this.min == this.max)
                var.domainHasChanged(GROUND);
            else
                var.domainHasChanged(BOUND);

            return;

        } else {

            assert stamp < storeLevel;

            BoundDomain result;

            if (this.min < min)
                if (this.max > max)
                    result = new BoundDomain(min, max);
                else
                    result = new BoundDomain(min, this.max);
            else
                // case this.min, this.max means no change which is handled above.
                result = new BoundDomain(this.min, max);


            result.modelConstraints = modelConstraints;
            result.searchConstraints = searchConstraints;
            result.stamp = storeLevel;
            result.previousDomain = this;
            result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
            result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
            ((IntVar) var).domain = result;

            if (result.singleton()) {
                var.domainHasChanged(GROUND);
                return;
            } else {
                var.domainHasChanged(BOUND);
                return;
            }

        }

    }

    @Override public void in(int storeLevel, Var var, IntDomain domain) {

        in(storeLevel, var, domain.min(), domain.max());

    }

    @Override public void inComplement(int storeLevel, Var var, int complement) {

        if (this.max == this.min && this.max == complement)
            throw failException;

        // Can not be removed without changing the code below.
        if (complement != this.min && complement != this.max)
            return;

        if (stamp == storeLevel) {

            if (this.min == complement)
                this.min++;
                // Assumes that check that complement must be equal to one of the bounds is
                // done above.
            else
                this.max--;

            if (this.min == this.max)
                var.domainHasChanged(GROUND);
            else
                var.domainHasChanged(BOUND);

            return;

        } else {

            assert stamp < storeLevel;

            BoundDomain result;

            if (this.min == complement)
                result = new BoundDomain(this.min + 1, this.max);
            else
                result = new BoundDomain(this.min, this.max - 1);

            result.modelConstraints = modelConstraints;
            result.searchConstraints = searchConstraints;
            result.stamp = storeLevel;
            result.previousDomain = this;
            result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
            result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
            ((IntVar) var).domain = result;

            if (result.singleton()) {
                var.domainHasChanged(GROUND);
                return;
            } else {
                var.domainHasChanged(BOUND);
                return;
            }

        }

    }

    @Override public void inComplement(int storeLevel, Var var, int min, int max) {

        assert (min <= max);

        // all elements are removed so fail.
        if (this.min >= min && this.max <= max)
            throw failException;

        // Can not be removed without changing the code below.
        // none of the elements are removed can ignore the call.
        if (max < this.min || this.max < min)
            return;

        // For bound domain, creating holes in the domain not possible.
        if (min > this.min && max < this.max)
            return;

        if (stamp == storeLevel) {

            if (max < this.max)
                this.min = max + 1;
            else
                this.max = min - 1;

            if (this.min == this.max)
                var.domainHasChanged(GROUND);
            else
                var.domainHasChanged(BOUND);

            return;

        } else {

            assert stamp < storeLevel;

            BoundDomain result;

            if (max < this.max)
                result = new BoundDomain(max + 1, this.max);
            else
                result = new BoundDomain(this.min, min - 1);

            result.modelConstraints = modelConstraints;
            result.searchConstraints = searchConstraints;
            result.stamp = storeLevel;
            result.previousDomain = this;
            result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
            result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
            ((IntVar) var).domain = result;

            if (result.singleton()) {
                var.domainHasChanged(GROUND);
                return;
            } else {
                var.domainHasChanged(BOUND);
                return;
            }

        }

    }

    @Override public void inMax(int storeLevel, Var var, int max) {

        if (this.min > max)
            throw failException;

        //If removed the code below has to change.
        if (max >= this.max)
            return;

        if (stamp == storeLevel) {

            this.max = max;

            if (this.min == this.max)
                var.domainHasChanged(GROUND);
            else
                var.domainHasChanged(BOUND);

            return;

        } else {

            assert stamp < storeLevel;

            BoundDomain result = new BoundDomain(min, max);

            result.modelConstraints = modelConstraints;
            result.searchConstraints = searchConstraints;
            result.stamp = storeLevel;
            result.previousDomain = this;
            result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
            result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
            ((IntVar) var).domain = result;

            if (result.singleton()) {
                var.domainHasChanged(GROUND);
                return;
            } else {
                var.domainHasChanged(BOUND);
                return;
            }

        }

    }

    @Override public void inMin(int storeLevel, Var var, int min) {

        if (this.max < min)
            throw failException;

        if (min <= this.min)
            return;

        if (stamp == storeLevel) {

            this.min = min;

            if (this.min == this.max)
                var.domainHasChanged(GROUND);
            else
                var.domainHasChanged(BOUND);

            return;

        } else {

            assert stamp < storeLevel;

            BoundDomain result = new BoundDomain(min, this.max);

            result.modelConstraints = modelConstraints;
            result.searchConstraints = searchConstraints;
            result.stamp = storeLevel;
            result.previousDomain = this;
            result.modelConstraintsToEvaluate = modelConstraintsToEvaluate;
            result.searchConstraintsToEvaluate = searchConstraintsToEvaluate;
            ((IntVar) var).domain = result;

            if (result.singleton()) {
                var.domainHasChanged(GROUND);
                return;
            } else {
                var.domainHasChanged(BOUND);
                return;
            }

        }
    }

    @Override public void inShift(int storeLevel, Var var, IntDomain domain, int shift) {
        in(storeLevel, var, domain.min() + shift, domain.max() + shift);
    }

    @Override public IntDomain intersect(IntDomain dom) {

        int inputMin = dom.min();
        int inputMax = dom.max();

        if (inputMin > this.max || inputMax < this.min)
            return emptyDomain;

        if (inputMin >= this.min) // inputMin..
            if (inputMax <= this.max) // inputMin..inputMax
                return new BoundDomain(inputMin, inputMax);
            else // inputMin..max
                return new BoundDomain(inputMin, this.max);
        else // min..
            if (inputMax <= this.max) // min..inputMax
                return new BoundDomain(this.min, inputMax);
            else // min..max
                return new BoundDomain(this.min, this.max);
    }

    @Override public IntDomain intersect(int min, int max) {

        if (min > this.max || max < this.min)
            return emptyDomain;

        if (min >= this.min) // inputMin..
            if (max <= this.max) // inputMin..inputMax
                return new BoundDomain(min, max);
            else // inputMin..max
                return new BoundDomain(min, this.max);
        else // min..
            if (max <= this.max) // min..inputMax
                return new BoundDomain(this.min, max);
            else // min..max
                return new BoundDomain(this.min, this.max);


    }

    @Override public IntDomain subtract(int value) {

        if (this.max == this.min && this.max == value)
            return emptyDomain;

        // Can not be removed without changing the code below.
        if (value != this.min && value != this.max)
            return new BoundDomain(this.min, this.max);

        if (this.min == value)
            return new BoundDomain(this.min + 1, this.max);
        else
            return new BoundDomain(this.min, this.max - 1);

    }

    @Override public IntervalEnumeration intervalEnumeration() {
        return new BoundDomainIntervalEnumeration(this.min, this.max);
    }

    @Override public boolean isEmpty() {
        return min > max;
    }

    @Override public boolean isIntersecting(IntDomain domain) {

        if (domain.min() > this.max || domain.max() < this.min)
            return false;

        return true;

    }

    @Override public boolean isIntersecting(int min, int max) {

        if (min > this.max || max < this.min)
            return false;

        return true;

    }

    @Override public boolean isNumeric() {
        return true;
    }

    @Override public boolean isSparseRepresentation() {
        return false;
    }

    @Override public int leftElement(int intervalNo) {
        assert intervalNo == 0;
        return this.min;
    }

    @Override public int max() {
        return this.max;
    }

    @Override public int min() {
        return this.min;
    }

    /**
     * It multiplies the domain by a given constant.
     * @param mul a factor by which the domain is being multiplied.
     * @return Domain created by multiplication of this domain.
     */
    public IntDomain multiply(int mul) {
        return new BoundDomain(this.min * mul, this.max * mul);
    }

    @Override public int nextValue(int value) {
        if (value < this.min)
            return min;
        if (value < this.max)
            return value + 1;

        return value;
    }

    @Override public int noIntervals() {

        if (isEmpty())
            return 0;
        else
            return 1;

    }

    @Override public IntDomain recentDomainPruning(int storeLevel) {
        if (previousDomain == null)
            return emptyDomain;

        if (stamp < storeLevel)
            return emptyDomain;

        return previousDomain.subtract(this);
    }

    @Override public void removeLevel(int level, Var var) {

        assert (this.stamp <= level);

        if (this.stamp == level) {

            ((IntVar) var).domain = this.previousDomain;
        }

        assert (var.level() < level);

    }


    @Override public int rightElement(int intervalNo) {
        assert (intervalNo == 0);
        return max;
    }

    @Override public void setDomain(IntDomain domain) {

        if (domain.domainID() == BoundDomainID) {

            BoundDomain boundDomain = (BoundDomain) domain;

            this.min = boundDomain.min();
            this.max = boundDomain.max();

            return;
        }

        setDomain(domain.min(), domain.max());

    }

    @Override public void setDomain(int min, int max) {

        assert (min <= max);

        this.min = min;
        this.max = max;

    }

    @Override public boolean singleton() {
        return (min == max);
    }

    @Override public boolean singleton(int c) {
        return (min == c && max == c);
    }

    @Override public int sizeConstraintsOriginal() {

        IntDomain domain = this;

        while (domain.domainID() == BoundDomainID) {

            BoundDomain dom = (BoundDomain) domain;

            if (dom.previousDomain != null)
                domain = dom.previousDomain;
            else
                break;
        }

        if (domain.domainID() == BoundDomainID)
            return (domain.modelConstraintsToEvaluate[0] + domain.modelConstraintsToEvaluate[1] + domain.modelConstraintsToEvaluate[2]);
        else
            return domain.sizeConstraintsOriginal();

    }

    @Override public IntDomain subtract(IntDomain domain) {

        int inputMin = domain.min();
        int inputMax = domain.max();

        if (inputMin <= this.min && inputMax >= this.max)
            return emptyDomain;

        if (this.min < inputMin && inputMax < this.max)
            return new BoundDomain(this.min, this.max);

        if (inputMin > this.min)
            return new BoundDomain(this.min, inputMin - 1);

        if (inputMax < this.max)
            return new BoundDomain(inputMax + 1, this.max);

        assert false;
        return null;
    }


    @Override public BoundDomain subtract(int min, int max) {

        if (min <= this.min && max >= this.max)
            return emptyDomain;

        if (this.min < min && max < this.max)
            return new BoundDomain(this.min, this.max);

        if (min > this.min)
            return new BoundDomain(this.min, min - 1);

        if (max < this.max)
            return new BoundDomain(max + 1, this.max);

        assert false;
        return null;

    }

    @Override public String toString() {

        if (min < max)
            return "{" + min + ".." + max + "}";
        else if (min == max)
            return String.valueOf(min);
        else
            return "{}";

    }

    @Override public String toStringConstraints() {

        StringBuffer S = new StringBuffer("");

        for (Iterator<Constraint> e = searchConstraints.iterator(); e.hasNext(); ) {
            S.append(e.next().id());
            if (e.hasNext())
                S.append(", ");
        }

        return S.toString();

    }

    @Override public String toStringFull() {

        StringBuffer result = new StringBuffer("");

        IntDomain domain = this;

        do {
            if (!domain.singleton()) {
                result.append(toString()).append("(").append(domain.stamp()).append(") ");
            } else
                result.append(min).append("(").append(String.valueOf(domain.stamp())).append(") ");

            result.append("constraints: ");

            for (Iterator<Constraint> e = domain.searchConstraints.iterator(); e.hasNext(); )
                result.append(e.next());

            if (domain.domainID() == IntervalDomainID) {

                IntervalDomain dom = (IntervalDomain) domain;
                domain = dom.previousDomain;

            } else if (domain.domainID() == BoundDomainID) {

                BoundDomain dom = (BoundDomain) domain;
                domain = dom.previousDomain;

            } else {

                // Other type.
            }

        } while (domain != null);

        return result.toString();

    }

    @Override public IntDomain union(IntDomain domain) {

        int min = domain.min();
        int max = domain.max();

        if (min < this.min) // min..
            if (this.max < max) // min..max
                return new BoundDomain(min, max);
            else // min..this.max
                return new BoundDomain(min, this.max);
        else // this.min..
            if (this.max < max) // this.min..max
                return new BoundDomain(this.min, max);
            else // this.min..this.max
                return new BoundDomain(this.min, this.max);

    }

    @Override public IntDomain union(int min, int max) {

        if (min < this.min) // min..
            if (this.max < max) // min..max
                return new BoundDomain(min, max);
            else // min..this.max
                return new BoundDomain(min, this.max);
        else // this.min..
            if (this.max < max) // this.min..max
                return new BoundDomain(this.min, max);
            else // this.min..this.max
                return new BoundDomain(this.min, this.max);
    }

    @Override public IntDomain union(int value) {

        if (value < this.min)
            return new BoundDomain(value, this.max);

        if (value > this.max)
            return new BoundDomain(this.min, value);

        return new BoundDomain(this.min, this.max);
    }

    @Override public ValueEnumeration valueEnumeration() {
        return new BoundDomainValueEnumeration(this);
    }

    @Override public int previousValue(int value) {

        if (value > this.min)
            return value - 1;

        return value;
    }

    /**
     * @return It returns the information about the first invariant which does not hold or null otherwise.
     */
    public String checkInvariants() {

        if (this.min > this.max)
            return "Min value is larger than max value ";

        //Fine, all invariants hold.
        return null;

    }

    @Override public void unionAdapt(int value) {
        unionAdapt(value, value);
    }

    @Override public void subtractAdapt(int complement) {

        // Can not be removed without changing the code below.
        if (complement != this.min && complement != this.max)
            return;

        if (this.min == complement)
            this.min++;
            // Assumes that check that complement must be equal to one of the bounds is
            // done above.
        else
            this.max--;

    }

    @Override public void subtractAdapt(int min, int max) {

        if (min <= this.min) {

            if (max >= this.max) {

                this.clear();

            } else {
                // min <= this.min
                // max < this.max
                this.min = max + 1;

            }

        } else {
            // min > this.min

            if (max >= this.max) {

                this.max = min - 1;

            } else {
                // min > this.min
                // max < this.max

                // removal not possible so nothing is not removed.

            }

        }

    }

    @Override public int intersectAdapt(IntDomain intersect) {

        return intersectAdapt(intersect.min(), intersect.max());

    }

    @Override public int intersectAdapt(int minIntersect, int maxIntersect) {

        if (minIntersect <= min && max <= maxIntersect)
            return Domain.NONE;

        if (minIntersect > max) {
            // Intersection is empty.
            min = 0;
            max = -1;
            return IntDomain.GROUND;
        }

        if (max > maxIntersect)
            max = maxIntersect;

        if (min < minIntersect)
            min = minIntersect;

        return IntDomain.BOUND;

    }

    @Override public int getElementAt(int index) {

        if (this.max - this.min > index)
            throw new RuntimeException("The domain does not have as many elements as indicated by index " + index);

        return this.min + index;

    }

    // TODO, test it.
    @Override public int sizeOfIntersection(IntDomain domain) {

        IntervalEnumeration enumer = domain.intervalEnumeration();

        int result = 0;

        while (enumer.hasMoreElements()) {

            Interval next = enumer.nextElement();

            if (next.max < this.min || this.max < next.min)
                continue;

            int min = Math.max(next.min, this.min);
            int max = Math.min(next.max, this.max);

            result += max - min + 1;

        }

        assert (result <= this.getSize()) : "Invariant violated. Check the code.";
        return result;
    }


    private final static Random generator = new Random();

    @Override public int getRandomValue() {

        if (generator.nextInt(2) == 0)
            return min();
        else
            return max();

    }

    @Override public boolean contains(int min, int max) {

        if (min <= min() && max >= max())
            return true;

        return false;

    }

}
