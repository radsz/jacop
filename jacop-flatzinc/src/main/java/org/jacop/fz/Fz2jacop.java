/*
 * Fz2jacop.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2000-2026 Krzysztof Kuchcinski and Radoslaw Szymanek
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

package org.jacop.fz;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.concurrent.TimeUnit;
import org.jacop.core.FailException;

/**
 * An executable to parse and execute the flatzinc file.
 *
 * @author Krzysztof Kuchcinki
 * @version 5.0
 */
public class Fz2jacop {

  /**
   * Calls the main method with the provided arguments.
   *
   * @param args the command line arguments
   */
  public void callMain(String[] args) {
    main(args);
  }

  /**
   * It parses the provided file and parsing parameters followed by problem solving.
   *
   * <p>TODO what are the conditions for different exceptions being thrown? Write little info below.
   *
   * @param args parameters describing the flatzinc file containing the problem to be solved as well
   *     as options for problem solving.
   */
  void main(String[] args) {

    Options opt = new Options(args);

    // if (opt.getVerbose())
    if (opt.debug()) {
      IO.println("%% Flatzinc2JaCoP: compiling and executing " + args[args.length - 1]);
    }

    Parser parser = new Parser(opt.getFile());
    parser.setOptions(opt);

    RunWhenShuttingDown t = new RunWhenShuttingDown(parser);
    if (opt.getStatistics()) {
      Runtime.getRuntime().addShutdownHook(t);
    }

    try {

      parser.model();

    } catch (FailException _) {
      IO.println("=====UNSATISFIABLE====="); // "*** Evaluation of model resulted in fail.");
      if (!opt.getOutputFilename().isEmpty()) {
        String st = "=====UNSATISFIABLE=====";
        try {
          Files.writeString(Path.of(opt.getOutputFilename()), st);
        } catch (IOException e1) {
          e1.printStackTrace();
        }
      }
      if (opt.getStatistics()) {
        IO.println(
            "%%%mzn-stat: variables="
                + (parser.getStore().size() + parser.getTables().getNumberBoolVariables()));
        IO.println("%%%mzn-stat: propagators=" + parser.getStore().numberConstraints());
        IO.println("\n%%%mzn-stat: propagations=" + parser.getStore().numberConsistencyCalls);
      }
    } catch (ArithmeticException e) {
      System.err.println("%% Evaluation of model resulted in an overflow.");
      if (e.getStackTrace().length > 0) {
        IO.println("%%\t" + e);
      }
    } catch (IllegalArgumentException e) {
      if (e.getStackTrace().length > 0) {
        IO.println("%%\t" + e);
      }
    } catch (ParseException | TokenMgrError e) {
      IO.println("%% Parser exception " + e);
    } catch (ArrayIndexOutOfBoundsException e) {
      IO.println("%% JaCoP internal error. Array out of bound exception " + e);
      if (e.getStackTrace().length > 0) {
        IO.println("%%\t" + e.getStackTrace()[0]);
      }
    } catch (OutOfMemoryError _) {
      IO.println("%% Out of memory error; consider option -Xmx... for JVM");
    } catch (StackOverflowError _) {
      IO.println("%% Stack overflow exception error; consider option -Xss... for JVM");
    } catch (TrivialSolution _) {
      // do nothing
      Runtime.getRuntime().removeShutdownHook(t);
      // return;
    }

    if (opt.getStatistics()) {
      Runtime.getRuntime().removeShutdownHook(t);

      // long execTime = (b.getThreadCpuTime(tread.getId()) - startCPU) / (long) 1e+6;  // in ms
      long execTime = (parser.solver.initTime + parser.solver.searchTime) / (long) 1e+6; // in ms
      final long hr = TimeUnit.MILLISECONDS.toHours(execTime);
      final long min = TimeUnit.MILLISECONDS.toMinutes(execTime - TimeUnit.HOURS.toMillis(hr));
      final long sec =
          TimeUnit.MILLISECONDS.toSeconds(
              execTime - TimeUnit.HOURS.toMillis(hr) - TimeUnit.MINUTES.toMillis(min));
      final long ms =
          TimeUnit.MILLISECONDS.toMillis(
              execTime
                  - TimeUnit.HOURS.toMillis(hr)
                  - TimeUnit.MINUTES.toMillis(min)
                  - TimeUnit.SECONDS.toMillis(sec));
      System.out.printf("%n%%%%%%mzn-stat: time=%.3f ", (double) execTime / 1000.0);
      if (hr == 0) {
        if (min == 0) {
          IO.println(); // String.format("(%d.%03d)", sec, ms));
        } else {
          IO.println("(%d:%02d.%03d)".formatted(min, sec, ms));
        }
      } else {
        IO.println("(%d:%02d:%02d.%03d)".formatted(hr, min, sec, ms));
      }
    }
  }
}
