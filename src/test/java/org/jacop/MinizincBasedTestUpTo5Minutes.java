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
public class MinizincBasedTestUpTo5Minutes{

    private String testFilename;

    private static Fz2jacop fz2jacop;
    private static final String relativePath = "src/test/fz/";
    private static final String timeCategory = "upTo5min/";
    private static final String listFileName = "list.txt";
    private static final boolean printInfo = true;

    @BeforeClass
    public static void initialize() {
        fz2jacop = new Fz2jacop();
    }

    public MinizincBasedTestUpTo5Minutes(String testFilename) {
        this.testFilename = testFilename;
    }

    @Parameterized.Parameters
    public static Collection<String> parametricTest() throws IOException {

        FileReader file = new FileReader(relativePath + timeCategory + listFileName);
        BufferedReader br = new BufferedReader(file);
        String line = "";
        List<String> list = new ArrayList<String>();
        int i = 0;
        while ((line = br.readLine())!=null) {
            list.add(i, line);
            i++;
        }
        return list;
    }

    @Test(timeout=600000)
    public void testMinizinc() throws IOException {
        List<String> expectedResult = new ArrayList<>();
        List<String> result = new ArrayList<>();

        System.out.println("Test file: " + timeCategory + testFilename);
        expectedResult = expected(timeCategory + testFilename + ".out");
        result = result(timeCategory + testFilename + ".fzn");

        for (int i = 0, j = 0; i < result.size() || j < expectedResult.size();) {
            if (i < result.size() && result.get(i).trim().isEmpty() )
            { i++; continue;}
            if (j < expectedResult.size() && expectedResult.get(j).trim().isEmpty() )
            { j++; continue;}
            if (result.size() == i)
                fail("\n" + "File path: " + timeCategory + testFilename + ".out " + " gave as a result less textlines that was expected. Expected line " + (j+1) + " not found.");
            if (expectedResult.size() == j)
                fail("\n" + "File path: " + timeCategory + testFilename + ".out " + " gave as a result more textlines that was expected. Actual line " + (i + 1) + "not found in expected result");

            assertEquals("\n" + "File path: " + timeCategory + testFilename + ".out " + "\nError line number (expected, actual): (" + (j + 1) + "," + (i + 1) + ")\n",
                    expectedResult.get(j).trim(), result.get(i).trim());
            i++; j++;
        }
    }

    public static List<String> result(String filename) {

        ByteArrayOutputStream baos = new ByteArrayOutputStream();
        PrintStream old = System.out;
        System.setOut(new PrintStream(baos));


        fz2jacop.main(new String[]{relativePath + filename });

        System.out.flush();
        System.setOut(old);

        String result = baos.toString();
        if(printInfo) {
            System.out.println(filename+"\n" + result);
        }

        return Arrays.asList(result.split("\n"));
    }


    public static List<String> expected(String filename) throws IOException {

        String filePath = new File(relativePath + filename ).getAbsolutePath();
        return Files.readAllLines(Paths.get(filePath), StandardCharsets.UTF_8);
    }


}
