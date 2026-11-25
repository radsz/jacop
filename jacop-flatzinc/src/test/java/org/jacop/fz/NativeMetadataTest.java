/*
 * NativeMetadataTest.java
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

import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.jar.JarEntry;
import java.util.jar.JarOutputStream;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

/** The reachability metadata of the native image lists the JaCoP classes of the jar. */
class NativeMetadataTest {

  @Test
  void listsClassesOfTheJar(@TempDir Path dir) throws IOException {
    Path jar = dir.resolve("j.jar");
    try (JarOutputStream out = new JarOutputStream(Files.newOutputStream(jar))) {
      for (String name :
          new String[] {
            "org/jacop/fz/constraints/ConstraintFncs.class",
            "org/jacop/constraints/XeqY.class",
            "org/jacop/search/DepthFirstSearch.class",
            "module-info.class",
            "org/other/Skip.class"
          }) {
        out.putNextEntry(new JarEntry(name));
        out.closeEntry();
      }
    }
    Path json = dir.resolve("out/reachability-metadata.json");
    NativeMetadata.main(new String[] {jar.toString(), json.toString()});
    String text = Files.readString(json);
    assertTrue(
        text.contains(
            "{\"type\": \"org.jacop.fz.constraints.ConstraintFncs\", \"queryAllPublicMethods\": true,"
                + " \"queryAllPublicConstructors\": true, \"allPublicMethods\": true}"),
        text);
    assertTrue(text.contains("\"type\": \"org.jacop.constraints.XeqY\""), text);
    assertTrue(text.contains("\"allPublicConstructors\": true}"), text);
    assertTrue(text.contains("\"type\": \"org.jacop.search.DepthFirstSearch\""), text);
    assertTrue(!text.contains("org.other") && !text.contains("module-info"), text);
    assertTrue(text.contains("META-INF/services/org.slf4j.spi.SLF4JServiceProvider"), text);
  }
}
