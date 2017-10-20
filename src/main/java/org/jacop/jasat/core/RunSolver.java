/*
 * RunSolver.java
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

package org.jacop.jasat.core;

import java.io.BufferedInputStream;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.InputStream;

import org.jacop.jasat.modules.DebugModule;
import org.jacop.jasat.modules.SearchModule;
import org.jacop.jasat.modules.StatModule;
import org.jacop.jasat.utils.BasicPreprocessor;
import org.jacop.jasat.utils.CnfParser;
import org.jacop.jasat.utils.CnfParser.ParseException;
import org.jacop.jasat.utils.OptParse;
import org.jacop.jasat.utils.OptParse.OptHandler;
import org.jacop.jasat.utils.structures.IntVec;

/**
 * The main class for the SAT solver when it is used standalone (without being
 * controlled by a master).
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 */

public final class RunSolver {

    private static String filename;

    /**
     * launch the solver on a file, given by command line parameters
     * @param args  command line arguments
     */
    public static void main(String[] args) {

        if (args.length == 0) {
            parser.printHelp();
            System.exit(0);
        }

        // parse arguments and get a config
        Config config = Config.defaultConfig();
        config = parser.parse(args, config);

        // input stream
        InputStream input;
        if (parser.realArgs.length == 0) {
            System.out.println("c no filename provided, reading from stdin");
            input = System.in;
        } else {
            filename = parser.realArgs[0];
            if (filename.equals("-")) {
                System.out.println("c read from stdin");
                input = System.in;
            } else {
                System.out.println("c read file " + filename);
                input = readFile();
            }
        }

        // create a solver instance
        Core core = new Core(config);
        core.markTime("init");
        // protect against brutal terminations
        protectOnTermination(core);

        // add a stats module to the solver, if useful
        if (config.verbosity >= 2) {
            StatModule stats = new StatModule(true);
            core.addComponent(stats);
        }

        // if debug enabled, add debug
        if (config.debug) {
            core.addComponent(new DebugModule());
            core.verbosity = 3;
        }

        // use the basic search control
        SearchModule search = new SearchModule();
        core.addComponent(search);

        core.markTime("init_stop");
        core.logc(2, "initialization time (ms): %d", core.getTimeDiff("init"));

        // parse the problem
        core.logc(2, "starts parsing %s", filename);

        CnfParser parser;
        try {
            parser = new CnfParser(core.pool, input);
        } catch (ParseException e1) {
            System.err.println("error while parsing:");
            e1.printStackTrace();
            System.exit(1);
            return;  // just to prevent the compiler from complaining
        }

        core.logc(2, "read : %d vars and %d clauses", parser.numVars, parser.numClauses);
        core.setMaxVariable(parser.numVars);


        // add all clauses to the core through the preprocessor
        BasicPreprocessor preprocessor = new BasicPreprocessor(core);
        for (IntVec clause : parser)
            preprocessor.addModelClause(clause);

        core.markTime("parse");
        core.logc(2, "parsing time (ms): %d", core.getTimeDiff("init_stop"));

        // do search
        core.start();

        core.logc("solve time (ms): %d", core.getTimeDiff("start"));
        core.logc("total time (ms): %d", core.getTimeDiff("init"));
        core.logc("throughput (assignments/s): %d", (core.assignmentNum * 1000 / (core.getTimeDiff("start") + 1)));

        // print results
        if (core.hasSolution())
            core.printSolution();
        else
            core.logc("solver state : %s", SolverState.show(core.currentState));

        // return with good exit code
        System.exit(core.getReturnCode());
    }

    /**
     * parse the file which name is filename, and returns a stream on success
     * @return an input stream for the content of the file
     */
    private static InputStream readFile() {
        try {
            File file = new File(filename);
            if (!file.exists()) {
                System.err.printf("error: file %s does not exists\n", filename);
                System.exit(1);
            }
            return new BufferedInputStream(new FileInputStream(file));
        } catch (FileNotFoundException e) {
            System.out.println(e.getMessage());
            System.exit(42);
            return null;  // never reached
        }
    }

    /**
     * on forced exit, print solution
     */
    private static void protectOnTermination(final Core core) {
        Thread handler = new Thread() {
            @Override public void run() {
                if (!core.isStopped) {
                    // solver still running
                    core.logc("(forced) exiting...");
                    core.stop();
                    core.currentState = SolverState.UNKNOWN;
                    core.printSolution();
                }
                return;
            }
        };
        handler.setDaemon(true);
        Runtime.getRuntime().addShutdownHook(handler);
    }

    private static OptParse<Config> parser = new OptParse<Config>();

    private static String helpString = "usage : RunSolver [option [option...]] <filename>";

    // set the verbosity
    private static OptHandler<Config> verboseHandler = new OptHandler<Config>() {
        {
            shortOpt = 'v';
            longOpt = "verbosity";
            help = "sets the verbosity";
        }

        @Override public Config handle(OptParse<Config> parser, Config e, String arg) {
            try {
                int i = Integer.parseInt(arg);
                e.verbosity = i;
            } catch (Exception ex) {
                e.verbosity = 1;
                return e;
            }
            return e;
        }
    };

    // prints help
    private static OptHandler<Config> helpHandler = new OptHandler<Config>() {
        {
            shortOpt = 'h';
            longOpt = "help";
            help = "prints this help";
        }

        @Override public Config handle(OptParse<Config> parser, Config e, String arg) {
            parser.printHelp();
            parser.exitParsing(); // no other options
            return null;
        }
    };

    private static OptHandler<Config> timeoutHandler = new OptHandler<Config>() {
        {
            shortOpt = 't';
            longOpt = "timeout";
            help = "set the timeout (in seconds)";
        }

        @Override public Config handle(OptParse<Config> parser, Config e, String arg) {
            Long t = Long.parseLong(arg);
            if (t != null) {
                e.timeout = t * 1000;
            }
            return e;
        }
    };

    private static OptHandler<Config> debugHandler = new OptHandler<Config>() {
        {
            shortOpt = 'd';
            longOpt = "debug";
            help = "set the timeout (in seconds)";
        }

        @Override public Config handle(OptParse<Config> parser, Config e, String arg) {
            e.debug = true;
            return e;
        }
    };

    static {
        parser.setHelp(helpString);
        parser.addHandler(helpHandler);
        parser.addHandler(verboseHandler);
        parser.addHandler(timeoutHandler);
        parser.addHandler(debugHandler);
    }
}
