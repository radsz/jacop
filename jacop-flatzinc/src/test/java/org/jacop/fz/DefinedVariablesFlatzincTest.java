/*
 * DefinedVariablesFlatzincTest.java
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

package org.jacop.fz;

import static org.assertj.core.api.Assertions.assertThat;

import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Path;
import org.jacop.core.Var;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/**
 * The variables that defines_var annotations name, which large neighbourhood search leaves out of
 * its neighbourhoods. MiniZinc defines the integer copy of a Boolean by bool2int; the front end
 * merges that copy into the Boolean, and the Boolean must not count as defined for it.
 */
class DefinedVariablesFlatzincTest {

  @TempDir Path dir;

  @Test
  void theBooleanOfBool2intIsNotDefinedByIt() throws IOException {
    Path model = dir.resolve("bool2int.fzn");
    Files.writeString(
        model,
        """
        var bool: b :: output_var;
        var bool: c :: is_defined_var :: output_var;
        var 0..1: i :: is_defined_var;
        var 0..1: x :: output_var;
        constraint bool2int(b, i) :: defines_var(i);
        constraint bool_not(b, c) :: defines_var(c);
        constraint int_le(i, x);
        solve satisfy;
        """);
    Tables tables = load(model);
    Var b = tables.getVariable("b");
    Var c = tables.getVariable("c");
    assertThat(tables.getVariable("i")).isSameAs(b);
    assertThat(tables.definedVariables).doesNotContain(b);
    assertThat(tables.definedVariables).contains(c);
  }

  private static Tables load(Path model) {
    PrintStream out = System.out;
    try (PrintStream quiet = new PrintStream(OutputStream.nullOutputStream())) {
      System.setOut(quiet);
      FlatzincLoader loader = new FlatzincLoader(new String[] {model.toString()});
      loader.load();
      return loader.getTables();
    } finally {
      System.setOut(out);
    }
  }
}
