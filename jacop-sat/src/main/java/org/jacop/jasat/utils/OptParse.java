/*
 * OptParse.java
 * <p>
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
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

package org.jacop.jasat.utils;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import lombok.extern.slf4j.Slf4j;

/**
 * Util to parse command-line arguments.
 *
 * @author Simon Cruanes and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class OptParse<E> {

  // handlers
  private final Map<String, OptHandler<E>> handlers = new HashMap<>();
  // remaining (true) args
  public String[] realArgs;
  // the main help string
  private String mainHelp = "";

  /**
   * Add a handler for some option.
   *
   * @param handler the handler
   */
  public void addHandler(OptHandler<E> handler) {
    if (handler.longOpt != null) {
      handlers.put("--" + handler.longOpt, handler);
    }
    if (handler.shortOpt != '\0') {
      handlers.put("-" + handler.shortOpt, handler);
    }
  }

  /**
   * Change the main help string, which will be printed if asked, or if a wrong option is given.
   *
   * @param helpString the help string
   */
  public void setHelp(String helpString) {
    this.mainHelp = helpString;
  }

  /**
   * Parses command-line arguments and applies handlers.
   *
   * @param args the command-line arguments
   * @param e the initial value of the configuration object
   * @return the modified configuration object after parsing, or null if parsing fails
   */
  public E parse(String[] args, E e) {
    realArgs = new String[args.length];
    int realIndex = 0;
    E current = e;
    for (String arg : args) {
      if (!isOptionArg(arg)) {
        realArgs[realIndex++] = arg;
      } else {
        E next = handleOption(arg, current);
        if (next == null) {
          return null;
        }
        current = next;
      }
    }
    this.realArgs = Arrays.copyOf(realArgs, realIndex);
    return current;
  }

  private boolean isOptionArg(String arg) {
    if (!arg.startsWith("-") && !arg.startsWith("--")) {
      return false;
    }
    if ("-".equals(arg)) {
      return false;
    }
    return true;
  }

  private E handleOption(String arg, E current) {
    int loc = arg.indexOf("=");
    String key = loc > 0 ? arg.substring(0, loc) : arg;
    String value = loc > 0 ? arg.substring(loc + 1) : "";
    if (!handlers.containsKey(key)) {
      log.info("unknown option: " + key);
      printHelp();
      return null;
    }
    return handlers.get(key).handle(this, current, value);
  }

  /** Print help of all options. */
  public void printHelp() {
    // print the main help message
    log.info(mainHelp);
    log.info("options:");

    // print (only once for each handler) its help
    Set<OptHandler<E>> printedHelps = new HashSet<>();
    for (OptHandler<E> handler : handlers.values()) {
      if (printedHelps.contains(handler)) {
        continue;
      } else {
        printedHelps.add(handler);
      }

      // print help for this handler
      String msg = "-%c, --%-16s %s".formatted(handler.shortOpt, handler.longOpt, handler.help);
      log.info(msg);
    }
  }

  /** A handler can call this to interrupt the parsing. */
  public void exitParsing() {
    throw new RuntimeException("stop parsing");
  }

  /**
   * A class to handle one option.
   *
   * @author simon
   */
  public abstract static class OptHandler<E> {
    // short name of the option
    public char shortOpt;
    // long name of the option
    public String longOpt;
    // help string
    public String help;

    /**
     * Handler for the option.
     *
     * @param parser the parser object that called this handler
     * @param e the object to modify according to the option
     * @param arg the (optional) argument to the option
     * @return a value of the good type (not necessarily the given one)
     */
    public abstract E handle(OptParse<E> parser, E e, String arg);
  }
}
