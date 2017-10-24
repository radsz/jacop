/*
 * Diff2VarValue.java
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

package org.jacop.constraints;

import java.util.List;

import org.jacop.core.MutableVarValue;

/**
 * Defines a current value of the Diff2Var and related operations on it.
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.5
 */

class Diff2VarValue implements MutableVarValue, Cloneable {

    Diff2VarValue previousDiff2VarValue = null;

    Rectangle[] Rects;

    int stamp = 0;

    // Constructors for temporary Duff2VarValue
    Diff2VarValue() {
    }

    Diff2VarValue(Rectangle[] R) {
        Rects = R;
    }

    // Methods

    @Override public Object clone() {

        // Diff2VarValue Val = new Diff2VarValue();
        // Val.Rects = new Rectangle[Rects.length];
        // for (int i = 0; i < Rects.length; i++) {
        // Val.Rects[i] = Rects[i];
        // }

        Diff2VarValue Val = new Diff2VarValue(Rects);
        Val.stamp = stamp;
        Val.previousDiff2VarValue = previousDiff2VarValue;
        return Val;
    }

    public MutableVarValue previous() {
        return previousDiff2VarValue;
    }

    public void setPrevious(MutableVarValue n) {
        previousDiff2VarValue = (Diff2VarValue) n;
    }

    public void setStamp(int s) {
        stamp = s;
    }

    void setValue(List<Rectangle> VR) {
        Rects = new Rectangle[VR.size()];
        for (int i = 0; i < Rects.length; i++)
            Rects[i] = VR.get(i);
        // System.arraycopy(VR.toArray(),0,Rects,0,Rects.length);
    }

    void setValue(Rectangle[] R) {
        Rects = R;
    }

    public int stamp() {
        return stamp;
    }

    @Override public String toString() {

        StringBuffer s = new StringBuffer();

        for (int i = 0; i < Rects.length; i++)
            if (i == Rects.length - 1)
	      s.append(Rects[i]);
            else
	      s.append(Rects[i] + ",");
        return s.toString();
    }
}
