/*
 * OptParse.java
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

package org.jacop.jasat.utils;

import java.util.*;

/**
 * util to parse command-line arguments
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 4.5
 */
public class OptParse<E> {

    // remaining (true) args
    public String[] realArgs;

    // handlers
    private Map<String, OptHandler<E>> handlers = new HashMap<String, OptHandler<E>>();

    // the main help string
    private String mainHelp = "";

    /**
     * add a handler for some option
     *
     * @param handler the handler
     */
    public void addHandler(OptHandler<E> handler) {
        if (handler.longOpt != null)
            handlers.put("--" + handler.longOpt, handler);
        if (handler.shortOpt != '\0')
            handlers.put("-" + handler.shortOpt, handler);
    }

    /**
     * change the main help string, which will be printed if asked, or
     * if a wrong option is given
     *
     * @param helpString the help string
     */
    public void setHelp(String helpString) {
        this.mainHelp = helpString;
    }

    public E parse(String[] args, E e) {
        realArgs = new String[args.length];
        int realIndex = 0;
        // the object
        E current = e;
        // iterate on arguments
        for (int i = 0; i < args.length; i++) {
            if (args[i].startsWith("-") || args[i].startsWith("--")) {
                if (args[i].equals("-")) {
                    // exception: this is not an option
                    realArgs[realIndex++] = args[i];
                    continue;
                }
                // parse this as an option
                int loc = args[i].indexOf("=");
                String key = (loc > 0) ? args[i].substring(0, loc) : args[i];
                String value = (loc > 0) ? args[i].substring(loc + 1) : "";
                if (!handlers.containsKey(key)) {
                    // this option is not registered
                    System.out.println("unknown option: " + key);
                    printHelp();
                    return null;
                } else {
                    current = handlers.get(key).handle(this, current, value);
                }
            } else {
                realArgs[realIndex++] = args[i];
            }
        }
        // truncate the "real args" array and return the E value
        this.realArgs = Arrays.copyOf(realArgs, realIndex);
        return current;
    }

    /**
     * print help of all options
     */
    public void printHelp() {
        // print the main help message
        System.out.println(mainHelp);
        System.out.println("options:");

        // print (only once for each handler) its help
        Set<OptHandler<E>> printedHelps = new HashSet<OptHandler<E>>();
        for (OptHandler<E> handler : handlers.values()) {
            if (printedHelps.contains(handler))
                continue;
            else
                printedHelps.add(handler);

            // print help for this handler
            String msg = String.format("-%c, --%-16s %s", handler.shortOpt, handler.longOpt, handler.help);
            System.out.println(msg);
        }
    }

    /**
     * a handler can call this to interrupt the parsing
     */
    public void exitParsing() {
        throw new RuntimeException("stop parsing");
    }

    /**
     * a class to handle one option
     *
     * @param E the object to apply modifications to
     * @author simon
     */
    public static abstract class OptHandler<E> {
        // short name of the option
        public char shortOpt;
        // long name of the option
        public String longOpt;
        // help string
        public String help;

        /**
         * handler for the option
         *
         * @param parser the parser object that called this handler
         * @param e      the object to modify according to the option
         * @param arg    the (optional) argument to the option
         * @return a value of the good type (not necessarily the given one)
         */
        public abstract E handle(OptParse<E> parser, E e, String arg);
    }


}
