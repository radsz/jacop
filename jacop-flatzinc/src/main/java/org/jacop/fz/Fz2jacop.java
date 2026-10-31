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

import java.io.FileInputStream;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.concurrent.TimeUnit;
import lombok.extern.slf4j.Slf4j;
import org.jacop.core.FailException;
import org.jacop.core.Store;
import org.jacop.floats.core.FloatDomain;

/**
 * An executable to parse and execute the flatzinc file.
 *
 * @author Krzysztof Kuchcinki
 * @version 5.0
 */
@Slf4j
public class Fz2jacop {

  /**
   * Parses and solves the model like the command line does, without exiting the JVM.
   *
   * @param args the command line arguments
   * @return the exit status: 0 when the model was solved (or shown unsatisfiable), 1 when it was
   *     rejected or solving failed with an error
   */
  public int callMain(String[] args) {
    return run(args);
  }

  /**
   * It parses the provided file and parsing parameters followed by problem solving.
   *
   * @param args parameters describing the flatzinc file containing the problem to be solved as well
   *     as options for problem solving.
   */
  void main(String[] args) {
    int status = run(args);
    // a model JaCoP cannot read or solve must not look like a successful run to MiniZinc or a
    // script, which go by the exit status
    if (status != 0) {
      System.exit(status);
    }
  }

  private int run(String[] args) {

    // The float settings are static: a model solved earlier in the same JVM (its float_search
    // precision, or --precision, --format, --step) must not change this one.
    FloatDomain.setPrecision(FloatDomain.DEFAULT_PRECISION);
    FloatDomain.setFormat(FloatDomain.DEFAULT_FORMAT);
    FloatDomain.setStep(0.0d);
    // without -r the seed is 0, so that the random choices (neighbourhoods of free search,
    // indomain_random, on_restart) repeat from run to run
    Store.setSeed(0);

    Options opt = new Options(args);

    // several objectives: each subproblem is solved by this method in turn
    Goals goals = Goals.of(opt, args);
    if (goals != null) {
      return goals.solve();
    }

    if (opt.threads() > 1) {
      String unsupported = Portfolio.unsupported(opt);
      if (unsupported == null) {
        return Portfolio.solve(args, opt);
      }
      IO.println("%% -p ignored: " + unsupported);
    }

    if (opt.debug()) {
      IO.println("%% Flatzinc2JaCoP: compiling and executing " + args[args.length - 1]);
    }

    // the model file is closed when solving ends, also after an error (an open file cannot be
    // deleted on Windows)
    int status = 1;
    try (FileInputStream file = opt.getFile()) {
      status = solve(opt, file);
    } catch (IOException e) {
      log.error("Failed to close {}", opt.getFileName(), e);
    }
    return status;
  }

  /**
   * Parses and solves the model in a thread of a parallel portfolio.
   *
   * @param opt the options of the thread
   * @param file the model
   * @return the exit status, as {@link #callMain}
   */
  static int solveInPortfolio(Options opt, FileInputStream file) {
    return new Fz2jacop().solve(opt, file);
  }

  private int solve(Options opt, FileInputStream file) {

    Parser parser = new Parser(file);
    parser.setOptions(opt);

    RunWhenShuttingDown t = new RunWhenShuttingDown(parser);
    if (opt.getStatistics()) {
      Runtime.getRuntime().addShutdownHook(t);
    }

    int status = 1;
    try {
      parser.model();
      status = 0;
    } catch (FailException _) {
      handleFailException(opt, parser);
      status = 0;
    } catch (UnsupportedOperationException e) {
      if (opt.proof() == null) {
        throw e;
      }
      // a model that --proof cannot write: no answer rather than one without its proof
      IO.println("%% --proof: " + e.getMessage());
      IO.println("=====UNKNOWN=====");
    } catch (ArithmeticException e) {
      handleArithmeticException(e);
    } catch (IllegalArgumentException e) {
      handleIllegalArgumentException(e);
    } catch (ParseException | TokenMgrError e) {
      FzConsole.printlnErr("%% Parser error: " + e.getMessage());
    } catch (ArrayIndexOutOfBoundsException e) {
      handleArrayIndexOutOfBoundsException(e);
    } catch (OutOfMemoryError _) {
      IO.println("%% Out of memory error; consider option -Xmx... for JVM");
    } catch (StackOverflowError _) {
      IO.println("%% Stack overflow exception error; consider option -Xss... for JVM");
    } catch (TrivialSolution _) {
      Runtime.getRuntime().removeShutdownHook(t);
      status = 0;
    } catch (ModelTimeOut _) {
      IO.println("=====UNKNOWN=====");
      IO.println("%% =====TIME-OUT=====");
      status = 0;
    }

    if (opt.getStatistics()) {
      Runtime.getRuntime().removeShutdownHook(t);
      printStatisticsTime(parser);
    }
    return status;
  }

  private void handleFailException(Options opt, Parser parser) {
    if (parser.getTables().domainsClamped()) {
      // the failure may come from the values cut off by narrowing a domain to JaCoP's range
      IO.println("=====UNKNOWN=====");
    } else {
      IO.println("=====UNSATISFIABLE=====");
    }
    if (opt.proof() != null && !parser.getTables().rootFailureProved) {
      // the model failed while it was translated, before the propagation the proof derives
      IO.println("%% --proof: no proof written, the model fails while it is translated");
    }
    if (!opt.getOutputFilename().isEmpty() && !parser.getTables().domainsClamped()) {
      try {
        Files.writeString(Path.of(opt.getOutputFilename()), "=====UNSATISFIABLE=====");
      } catch (IOException e1) {
        log.error("Failed to write output to {}", opt.getOutputFilename(), e1);
      }
    }
    if (opt.getStatistics()) {
      IO.println(
          "%%%mzn-stat: variables="
              + (parser.getStore().size() + parser.getTables().getNumberBoolVariables()));
      IO.println("%%%mzn-stat: propagators=" + parser.getStore().numberConstraints());
      IO.println("\n%%%mzn-stat: propagations=" + parser.getStore().numberConsistencyCalls);
    }
  }

  // Errors go to stderr, so that stdout holds only solutions and status lines, as MiniZinc
  // expects from a solver that rejects its input.

  private void handleArithmeticException(ArithmeticException e) {
    FzConsole.printlnErr("%% Evaluation of model resulted in an overflow: " + e.getMessage());
  }

  private void handleIllegalArgumentException(IllegalArgumentException e) {
    FzConsole.printlnErr("%% Error: " + e.getMessage());
  }

  private void handleArrayIndexOutOfBoundsException(ArrayIndexOutOfBoundsException e) {
    FzConsole.printlnErr("%% JaCoP internal error. Array out of bound exception " + e);
    if (e.getStackTrace().length > 0) {
      FzConsole.printlnErr("%%\t" + e.getStackTrace()[0]);
    }
  }

  private void printStatisticsTime(Parser parser) {
    long execTime = (parser.solver.initTime + parser.solver.searchTime) / 1_000_000L; // in ms
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
    System.out.printf("%n%%%%%%mzn-stat: time=%.3f ", execTime / 1000.0);
    if (hr == 0) {
      if (min == 0) {
        IO.println();
      } else {
        IO.println("(%d:%02d.%03d)".formatted(min, sec, ms));
      }
    } else {
      IO.println("(%d:%02d:%02d.%03d)".formatted(hr, min, sec, ms));
    }
  }
}
