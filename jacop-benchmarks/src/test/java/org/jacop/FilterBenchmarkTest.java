/*
 * FilterBenchmarkTest.java
 * <p>
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

import static org.assertj.core.api.Assertions.assertThat;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.stream.Stream;
import org.jacop.core.Store;
import org.jacop.examples.fd.filters.Ar;
import org.jacop.examples.fd.filters.Dct;
import org.jacop.examples.fd.filters.Dfq;
import org.jacop.examples.fd.filters.Ewf;
import org.jacop.examples.fd.filters.Fft;
import org.jacop.examples.fd.filters.Filter;
import org.jacop.examples.fd.filters.FilterBenchmark;
import org.jacop.examples.fd.filters.Fir;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

/*
 * This is a test based on the filter scheduling examples, commonly used in High-Level Synthesis.
 *
 * @author Mariusz Świerkot and Radoslaw Szymanek
 */

public class FilterBenchmarkTest extends FilterBenchmark {

  static Stream<Arguments> testData() {
    return Stream.of(
        Arguments.of(new int[] {1, 1}, new Dfq(), "experiment1", 13),
        Arguments.of(new int[] {1, 2}, new Dfq(), "experiment1", 8),
        Arguments.of(new int[] {1, 3}, new Dfq(), "experiment1", 7),
        Arguments.of(new int[] {2, 2}, new Dfq(), "experiment1", 7),
        Arguments.of(new int[] {1, 4}, new Dfq(), "experiment1", 6),
        Arguments.of(new int[] {2, 3}, new Dfq(), "experiment1", 6),
        Arguments.of(new int[] {1, 1}, new Fir(), "experiment1", 18),
        Arguments.of(new int[] {1, 2}, new Fir(), "experiment1", 15),
        Arguments.of(new int[] {2, 2}, new Fir(), "experiment1", 11),
        Arguments.of(new int[] {2, 3}, new Fir(), "experiment1", 10),
        Arguments.of(new int[] {1, 1}, new Ar(1, 1), "experiment2", 18),
        Arguments.of(new int[] {1, 2}, new Ar(1, 1), "experiment2", 13),
        Arguments.of(new int[] {1, 3}, new Ar(1, 1), "experiment2", 13),
        Arguments.of(new int[] {2, 3}, new Ar(1, 1), "experiment2", 10),
        Arguments.of(new int[] {2, 4}, new Ar(1, 1), "experiment2", 8),
        Arguments.of(new int[] {1, 1}, new Ewf(), "experiment1", 28),
        Arguments.of(new int[] {2, 1}, new Ewf(), "experiment1", 21),
        Arguments.of(new int[] {2, 2}, new Ewf(), "experiment1", 18),
        Arguments.of(new int[] {3, 3}, new Ewf(), "experiment1", 17),
        Arguments.of(new int[] {1, 1}, new Ewf(1, 1), "experiment1", 27),
        Arguments.of(new int[] {2, 1}, new Ewf(1, 1), "experiment1", 16),
        Arguments.of(new int[] {2, 2}, new Ewf(1, 1), "experiment1", 16),
        Arguments.of(new int[] {3, 3}, new Ewf(1, 1), "experiment1", 14),
        Arguments.of(new int[] {1, 1}, new Dct(), "experiment1", 34),
        Arguments.of(new int[] {1, 2}, new Dct(), "experiment1", 32),
        Arguments.of(new int[] {2, 2}, new Dct(), "experiment1", 18),
        Arguments.of(new int[] {2, 3}, new Dct(), "experiment1", 16),
        Arguments.of(new int[] {3, 3}, new Dct(), "experiment1", 14),
        Arguments.of(new int[] {3, 4}, new Dct(), "experiment1", 11),
        Arguments.of(new int[] {4, 4}, new Dct(), "experiment1", 10),
        Arguments.of(new int[] {1, 1}, new Dfq(), "experiment1Pm", 8),
        Arguments.of(new int[] {1, 2}, new Dfq(), "experiment1Pm", 6),
        Arguments.of(new int[] {1, 1}, new Fir(), "experiment1Pm", 15),
        Arguments.of(new int[] {2, 1}, new Fir(), "experiment1Pm", 11),
        Arguments.of(new int[] {2, 2}, new Fir(), "experiment1Pm", 10),
        Arguments.of(new int[] {1, 1}, new Ar(), "experiment2Pm", 19),
        Arguments.of(new int[] {2, 1}, new Ar(), "experiment2Pm", 19),
        Arguments.of(new int[] {2, 2}, new Ar(), "experiment2Pm", 13),
        Arguments.of(new int[] {2, 4}, new Ar(), "experiment2Pm", 11),
        Arguments.of(new int[] {2, 1}, new Ewf(), "experiment1Pm", 19),
        Arguments.of(new int[] {3, 1}, new Ewf(), "experiment1Pm", 18),
        Arguments.of(new int[] {3, 2}, new Ewf(), "experiment1Pm", 17),
        Arguments.of(new int[] {1, 1}, new Dct(), "experiment1Pm", 32),
        Arguments.of(new int[] {2, 1}, new Dct(), "experiment1Pm", 19),
        Arguments.of(new int[] {2, 2}, new Dct(), "experiment1Pm", 16),
        Arguments.of(new int[] {3, 2}, new Dct(), "experiment1Pm", 11),
        Arguments.of(new int[] {4, 3}, new Dct(), "experiment1Pm", 9),
        Arguments.of(new int[] {5, 4}, new Dct(), "experiment1Pm", 8),
        Arguments.of(new int[] {6, 5}, new Dct(), "experiment1Pm", 7),
        Arguments.of(new int[] {1, 1, 3}, new Dfq(), "experiment1C", 18),
        Arguments.of(new int[] {1, 2, 3}, new Dfq(), "experiment1C", 13),
        Arguments.of(new int[] {2, 2, 3}, new Dfq(), "experiment1C", 9),
        Arguments.of(new int[] {2, 1, 2}, new Fir(), "experiment1C", 19),
        Arguments.of(new int[] {2, 2, 2}, new Fir(), "experiment1C", 15),
        Arguments.of(new int[] {3, 2, 2}, new Fir(), "experiment1C", 12),
        Arguments.of(new int[] {1, 1, 3}, new Fir(), "experiment1C", 43),
        Arguments.of(new int[] {2, 1, 3}, new Fir(), "experiment1C", 24),
        Arguments.of(new int[] {3, 2, 3}, new Fir(), "experiment1C", 15),
        Arguments.of(new int[] {2, 2, 2}, new Ar(), "experiment1C", 18),
        Arguments.of(new int[] {2, 3, 2}, new Ar(), "experiment1C", 16),
        Arguments.of(new int[] {4, 4, 2}, new Ar(), "experiment1C", 12),
        Arguments.of(new int[] {1, 1, 3}, new Ar(), "experiment1C", 49),
        Arguments.of(new int[] {1, 2, 3}, new Ar(), "experiment1C", 34),
        Arguments.of(new int[] {2, 2, 3}, new Ar(), "experiment1C", 25),
        Arguments.of(new int[] {2, 3, 3}, new Ar(), "experiment1C", 19),
        Arguments.of(new int[] {3, 4, 3}, new Ar(), "experiment1C", 13),
        Arguments.of(new int[] {3, 4, 3}, new Ar(), "experiment1C", 13),
        Arguments.of(new int[] {2, 2, 4}, new Ar(), "experiment1C", 32),
        Arguments.of(new int[] {2, 3, 4}, new Ar(), "experiment1C", 24),
        Arguments.of(new int[] {2, 1, 2}, new Ewf(), "experiment1C", 29),
        Arguments.of(new int[] {3, 1, 2}, new Ewf(), "experiment1C", 21),
        Arguments.of(new int[] {1, 1, 3}, new Ewf(), "experiment1C", 76),
        Arguments.of(new int[] {2, 1, 3}, new Ewf(), "experiment1C", 40),
        Arguments.of(new int[] {3, 1, 3}, new Ewf(), "experiment1C", 30),
        Arguments.of(new int[] {1, 1, 4}, new Ewf(), "experiment1C", 101),
        Arguments.of(new int[] {2, 1, 4}, new Ewf(), "experiment1C", 49),
        Arguments.of(new int[] {3, 1, 4}, new Ewf(), "experiment1C", 35),
        Arguments.of(new int[] {2, 1, 2}, new Dct(), "experiment1C", 35),
        Arguments.of(new int[] {2, 2, 2}, new Dct(), "experiment1C", 31),
        Arguments.of(new int[] {3, 2, 2}, new Dct(), "experiment1C", 21),
        Arguments.of(new int[] {4, 2, 2}, new Dct(), "experiment1C", 19),
        Arguments.of(new int[] {4, 3, 2}, new Dct(), "experiment1C", 15),
        Arguments.of(new int[] {5, 4, 2}, new Dct(), "experiment1C", 13),
        Arguments.of(new int[] {1, 1, 3}, new Dct(), "experiment1C", 94),
        Arguments.of(new int[] {2, 1, 3}, new Dct(), "experiment1C", 48),
        Arguments.of(new int[] {3, 2, 3}, new Dct(), "experiment1C", 31),
        Arguments.of(new int[] {4, 2, 3}, new Dct(), "experiment1C", 24),
        Arguments.of(new int[] {5, 3, 3}, new Dct(), "experiment1C", 19),
        Arguments.of(new int[] {1, 3}, new Dfq(), "experiment1P", 5),
        Arguments.of(new int[] {2, 3}, new Dfq(), "experiment1P", 4),
        Arguments.of(new int[] {2, 2}, new Fir(), "experiment1P", 9),
        Arguments.of(new int[] {3, 3}, new Fir(), "experiment1P", 7),
        Arguments.of(new int[] {3, 4}, new Fir(), "experiment1P", 6),
        Arguments.of(new int[] {2, 4}, new Ar(), "experiment1P", 9),
        Arguments.of(new int[] {2, 6}, new Ar(), "experiment1P", 9),
        Arguments.of(new int[] {3, 8}, new Ar(), "experiment1P", 9),
        Arguments.of(new int[] {3, 2}, new Ewf(), "experiment1P", 17),
        Arguments.of(new int[] {4, 2}, new Ewf(), "experiment1P", 17),
        Arguments.of(new int[] {4, 3}, new Ewf(), "experiment1P", 16),
        Arguments.of(new int[] {5, 4}, new Ewf(), "experiment1P", 15),
        Arguments.of(new int[] {4, 4}, new Dct(), "experiment1P", 10),
        Arguments.of(new int[] {4, 5}, new Dct(), "experiment1P", 9),
        Arguments.of(new int[] {5, 6}, new Dct(), "experiment1P", 7),
        Arguments.of(new int[] {6, 7}, new Dct(), "experiment1P", 7),
        Arguments.of(new int[] {7, 8}, new Dct(), "experiment1P", 6),
        Arguments.of(new int[] {1, 1}, new Fft(), "experiment1P", 8),
        Arguments.of(new int[] {1, 2}, new Fft(), "experiment1P", 6),
        Arguments.of(new int[] {2, 2}, new Fft(), "experiment1P", 4),
        Arguments.of(new int[] {3, 4}, new Fft(), "experiment1P", 2));
  }

  @ParameterizedTest
  @MethodSource("testData")
  @SuppressWarnings("unchecked")
  public void testFilter(
      int[] resourcesConfiguration, Filter filter, String experiment, int costExp)
      throws InvocationTargetException, IllegalAccessException, NoSuchMethodException {

    Class<? extends FilterBenchmarkTest> cls = this.getClass();
    Method exp = cls.getMethod(experiment, Store.class, Filter.class, int[].class);

    int costFound = (Integer) exp.invoke(this, new Store(), filter, resourcesConfiguration);

    assertThat(costFound)
        .as("Test " + experiment + " failed for " + filter.getClass())
        .isEqualTo(costExp);
  }

  /**
   * It optimizes scheduling of filter operations.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   */
  public int experiment1(Store store, Filter filter, int[] configuration) {
    return experiment1(store, filter, configuration[0], configuration[1]);
  }

  public int experiment2(Store store, Filter filter, int[] configuration) {
    return experiment2(store, filter, configuration[0], configuration[1]);
  }

  /**
   * It optimizes scheduling of filter operation in fashion allowing chaining of operations within
   * one clock cycle.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   * @param configuration number of adders available, number of multipliers available, number of
   *     time units within a clock.
   */
  public int experiment1C(Store store, Filter filter, int[] configuration) {

    return experiment1C(store, filter, configuration[0], configuration[1], configuration[2]);
  }

  /**
   * It optimizes scheduling of filter operations in a fashion allowing pipelining of multiplication
   * operations.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   * @param configuration number of adders available, number of multipliers available.
   */
  public int experiment1Pm(Store store, Filter filter, int[] configuration) {
    return experiment1Pm(store, filter, configuration[0], configuration[1]);
  }

  /**
   * It optimizes scheduling of filter operation in fashion allowing pipelining of multiplication
   * operations.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   * @param configuration it specifies number of resource available.
   */
  public int experiment2Pm(Store store, Filter filter, int[] configuration) {

    return experiment2Pm(store, filter, configuration[0], configuration[1]);
  }

  /**
   * It optimizes scheduling of filter operations. It performs algorithmic pipelining.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   * @param configuration number of adders and multipliers.
   */
  public int experiment1P(Store store, Filter filter, int[] configuration) {

    return experiment1P(store, filter, configuration[0], configuration[1]);
  }

  /**
   * It optimizes scheduling of filter operations. It performs algorithmic pipelining three times.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   * @param configuration number of adders and multipliers.
   */
  public int experiment2P(Store store, Filter filter, int[] configuration) {

    return experiment2P(store, filter, configuration[0], configuration[1]);
  }

  /**
   * It optimizes scheduling of filter operation in fashion allowing chaining of operations within
   * one clock cycle.
   *
   * @param store the constraint store in which the constraints are imposed.
   * @param filter the filter being scheduled.
   * @param configuration number of adders, multipliers, and time units within a clock.
   */
  public int experiment2C(Store store, Filter filter, int[] configuration) {

    return experiment2C(store, filter, configuration[0], configuration[1], configuration[2]);
  }
}
