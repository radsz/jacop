package org.jacop;

import org.jacop.fz.Fz2jacop;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

/**
 * @author Mariusz Świerkot
 */

@RunWith(Parameterized.class)
public class MinizincBasedTestAbove1Hours extends MinizincBasedTestsHelper{
    protected static final String timeCategory = "above1hour/";

    public MinizincBasedTestAbove1Hours(String testFilename) {

        this.testFilename = testFilename;

    }

    @Parameterized.Parameters
    public static Collection<String> parametricTest() throws IOException {

        return fileReader(timeCategory);
    }

    @Test()
    public void testMinizinc() throws IOException {

        testExecution(timeCategory);
    }



}