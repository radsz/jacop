/*
 * NativeMetadata.java
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
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Enumeration;
import java.util.TreeSet;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;

/**
 * Writes the reachability metadata ({@code reachability-metadata.json}) that the GraalVM native
 * image of JaCoP needs, for the {@code fzn-jacop-native-build} script:
 *
 * <pre>
 * java -cp jacop-all.jar org.jacop.fz.NativeMetadata jacop-all.jar out/reachability-metadata.json
 * </pre>
 *
 * <p>JaCoP uses reflection in a few places that a native image must know of in advance:
 *
 * <ul>
 *   <li>the FlatZinc front end calls the method of {@code ConstraintFncs} named after each
 *       constraint, so all its public methods are registered;
 *   <li>{@code Constraint}, {@code Copyable} and {@code QueueForward} ask a class whether it
 *       overrides {@code queueVariable} or {@code copy} ({@code Class.getMethod}), and graph
 *       constraints are made by name; the public methods and constructors of every JaCoP class are
 *       therefore registered for queries, which costs no code;
 *   <li>SLF4J finds reload4j through a service file, and reload4j looks for its configuration;
 *   <li>thread CPU times come from the JVM's management classes through JNI.
 * </ul>
 *
 * <p>The list of classes is read from the jar, so that a new constraint class needs no change here.
 */
public final class NativeMetadata {

  private NativeMetadata() {}

  /**
   * Writes the metadata.
   *
   * @param args the JaCoP jar(s) to scan, then the output file
   * @throws IOException if a jar cannot be read or the file cannot be written
   */
  public static void main(String[] args) throws IOException {
    if (args.length < 2) {
      throw new IllegalArgumentException("NativeMetadata: jar... out.json");
    }
    TreeSet<String> classes = new TreeSet<>();
    for (int i = 0; i < args.length - 1; i++) {
      try (JarFile jar = new JarFile(args[i])) {
        Enumeration<JarEntry> entries = jar.entries();
        while (entries.hasMoreElements()) {
          String name = entries.nextElement().getName();
          if (name.startsWith("org/jacop/")
              && name.endsWith(".class")
              && !name.endsWith("module-info.class")) {
            classes.add(name.substring(0, name.length() - ".class".length()).replace('/', '.'));
          }
        }
      }
    }
    Path out = Path.of(args[args.length - 1]);
    if (out.getParent() != null) {
      Files.createDirectories(out.getParent());
    }
    try (PrintWriter w = new PrintWriter(Files.newBufferedWriter(out, StandardCharsets.UTF_8))) {
      w.println("{");
      w.println("  \"reflection\": [");
      for (String c : classes) {
        StringBuilder e = new StringBuilder("    {\"type\": \"").append(c).append("\"");
        e.append(", \"queryAllPublicMethods\": true, \"queryAllPublicConstructors\": true");
        if (c.equals("org.jacop.fz.constraints.ConstraintFncs")) {
          e.append(", \"allPublicMethods\": true");
        }
        if (c.startsWith("org.jacop.constraints.") || c.startsWith("org.jacop.core.")) {
          // graph constraints (GraphConstraints) and domains (IntervalDomain) are made by name
          e.append(", \"allPublicConstructors\": true");
        }
        w.println(e.append("},"));
      }
      w.println("    {\"type\": \"org.jacop.core.Var[]\"},");
      w.println("    {\"type\": \"org.jacop.search.Search[]\"},");
      w.println("    {\"type\": \"org.apache.log4j.Log4jLoggerFactory\"},");
      w.println(
          "    {\"type\": \"org.slf4j.reload4j.Reload4jServiceProvider\", \"allPublicConstructors\": true},");
      w.println(
          "    {\"type\": \"java.lang.Thread\", \"methods\": [{\"name\": \"getContextClassLoader\", \"parameterTypes\": []}]},");
      // thread CPU time (ThreadMXBean) and the number formats of String.format
      w.println(
          "    {\"type\": \"java.lang.Boolean\", \"jniAccessible\": true, \"methods\": [{\"name\": \"getBoolean\", \"parameterTypes\": [\"java.lang.String\"]}]},");
      w.println(
          "    {\"type\": \"sun.management.VMManagementImpl\", \"jniAccessible\": true, \"allDeclaredFields\": true},");
      w.println("    {\"type\": \"sun.text.resources.cldr.FormatData\"},");
      w.println("    {\"type\": \"sun.text.resources.cldr.FormatData_en\"}");
      w.println("  ],");
      w.println("  \"resources\": [");
      w.println("    {\"glob\": \"META-INF/services/org.slf4j.spi.SLF4JServiceProvider\"},");
      w.println("    {\"glob\": \"log4j.properties\"},");
      w.println("    {\"glob\": \"log4j.xml\"}");
      w.println("  ]");
      w.println("}");
    }
  }
}
