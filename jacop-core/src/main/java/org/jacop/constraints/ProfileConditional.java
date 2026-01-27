/*
 * ProfileConditional.java
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
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.constraints;

import java.io.Serial;
import java.util.ArrayList;
import java.util.Iterator;
import lombok.extern.slf4j.Slf4j;

/**
 * Defines a basic data structure to keep the profile for the disjointConditonal/2
 *
 * @author Krzysztof Kuchcinski and Radoslaw Szymanek
 * @version 4.10
 */
@Slf4j
class ProfileConditional extends ArrayList<ProfileItemCondition> {

  static final boolean trace = false;
  @Serial private static final long serialVersionUID = 8683452581100000010L;
  int MaxProfile;

  ProfileConditional() {}

  void addToProfile(int index, int a, int b, int val, ExclusiveList exList) {
    ProfileItemCondition p;
    int i = 0;
    boolean notFound = true;

    if (trace) {
      log.debug("{}  --------------------------", index);
      log.debug("{}", exList);
    }

    if (size() == 0) {
      if (trace) {
        log.debug("1. Add [{}..{})={} at position 0", a, b, val);
      }
      int[] r = {index, val};
      add(new ProfileItemCondition(a, b, val, r));
      if (MaxProfile < val) {
        MaxProfile = val;
      }
    } else {
      while (i < size() && notFound) {
        p = get(i);
        if (b <= p.min) {
          if (a != b) {
            if (b == p.min && val == p.value) {
              if (trace) {
                log.debug("2a. Change [{}..{})={} at position {}", a, p.max, val, i);
              }
              // !!!! b==p.Min
              // p.Min = a;
              int[] r = {index, val};
              add(i + 1, new ProfileItemCondition(a, b, val, r));
            } else {
              // b < p.Min
              if (i > 0) {
                int[] r = {index, val}; // OK
                add(i, new ProfileItemCondition(a, b, val, r));
              } else {
                if (trace) {
                  log.debug("2b. Add [{}..{})={} at position {}", a, b, val, i);
                }
                int[] r = {index, val}; // OK
                add(i, new ProfileItemCondition(a, b, val, r));
              }
            }
          }
          notFound = false;
          i++;
          if (MaxProfile < val) {
            MaxProfile = val;
          }
        } else {
          // b > p.Min
          if (p.max <= a) {
            if (i == size() - 1) {
              if (a != b) {
                if (trace) {
                  log.debug("3. Add [{}..{})={} at position {}", a, b, val, i + 1);
                }
                int[] r = {index, val}; // OK
                add(i + 1, new ProfileItemCondition(a, b, val, r));
              }
              i++;
              notFound = false;
            } else {
              i++;
            }
          } else {
            // b > p.Min && a < p.Max; [a,b) overlaps p
            ProfileItemCondition new1 = new ProfileItemCondition();
            ProfileItemCondition new2 = new ProfileItemCondition();
            ProfileItemCondition new3 = new ProfileItemCondition();
            int[] r = {index, val};

            if (trace) {
              log.debug("Overlap of [{}..{})={}, [{}]  and {}", a, b, val, index, p);
            }

            p.overlap(new ProfileItemCondition(a, b, val, r), new1, new2, new3, exList, r);
            if (trace) {
              log.debug("Result = {}, {}, {}", new1, new2, new3);
            }

            remove(i);
            // left
            if (new1.min != -1) {
              ProfileItemCondition previous;
              if (i != 0) {
                previous = get(i - 1);
              } else {
                previous = new ProfileItemCondition();
              }
              if (previous.max == new1.min && previous.value == new1.value) {
                if (trace) {
                  log.debug(
                      "4a. Change [{}..{})={} at position {}", previous.min, new1.max, val, i);
                }
                add(i, new1);
              } else {
                if (trace) {
                  log.debug("4b. Adding {}", new1);
                }
                // !!!
                new1.rectangles = p.rectangles;
                add(i, new1);
                if (MaxProfile < new1.value) {
                  MaxProfile = new1.value;
                }
              }
              i++;
            }
            // middle
            if (new2.min != -1) {
              ProfileItemCondition previous;
              if (i != 0) {
                previous = get(i - 1);
              } else {
                previous = new ProfileItemCondition();
              }
              if (previous.max == new2.min && previous.value == new2.value) {
                if (trace) {
                  log.debug("5a. Change [{}..{})={} at position {}", new2.min, new2.max, val, i);
                }
                add(i, new2);
              } else {
                if (trace) {
                  log.debug("5b. Adding {}", new2);
                }
                // !!!
                add(i, new2);
                if (MaxProfile < new2.value) {
                  MaxProfile = new2.value;
                }
              }
              i++;
            }
            // right
            if (new3.min != -1 && new3.min != new3.max) {
              if (new3.max == b) {
                // rest of [a,b)
                // System.out.println("***"+this);
                // System.out.println("adding "+index+", ["+a+",
                // "+b+")="+val);
                addToProfile(index, new3.min, new3.max, val, exList);
              } else {
                // rest of the old profile
                add(i, new3);
              }
              i++;
            }
            notFound = false;
          }
        }
      }
    }
    if (trace) {
      log.debug("########\n{}", this);
    }
  }

  int max() {
    return MaxProfile;
  }

  @Override
  public String toString() {

    StringBuilder result = new StringBuilder("[");

    for (Iterator<ProfileItemCondition> e = iterator(); e.hasNext(); ) {

      result.append(e.next());
      if (e.hasNext()) {
        result.append(", ");
      }
    }

    result.append("]");

    return result.toString();
  }
}
