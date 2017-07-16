package org.jacop;

import org.jacop.floats.core.FloatDomain;
import org.jacop.fz.Fz2jacop;
import org.jacop.fz.Options;
import org.junit.After;
import org.junit.BeforeClass;

import java.io.*;
import java.nio.charset.Charset;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Stream;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.fail;

/**
 * @author Mariusz Świerkot
 */

public class MinizincBasedTestsHelper {
    protected String testFilename;
    protected static Fz2jacop fz2jacop;
    protected static final String relativePath = "src/test/fz/";
    String timeCategory;
    protected static final String listFileName = "list.txt";
    protected static final boolean printInfo = false;
    private static int counter=0;

    protected MinizincBasedTestsHelper(String timeCategory) {
        this.timeCategory = timeCategory;
    }

    @BeforeClass public static void initialize() {
        fz2jacop = new Fz2jacop();
    }

    @After public void cleanUp() {
        String outputFilename = relativePath + timeCategory + testFilename + ".fzn" + ".out";
        try {
            Files.delete(Paths.get(outputFilename));
        } catch (IOException e) {
            // e.printStackTrace(); // can be helpful when updating code and/or tests instances.
            // File was not created (because the test timeout before it was created so deleting it failed.
        }
    }

    public int counter(){
        return counter;
    }


    protected List<String> computeResult(String filename) throws IOException {
        
        String outputFilename = relativePath + filename + ".out";
        String foo = outputFilename.substring(0, outputFilename.lastIndexOf('/'));

        //If options.opt exist reads parameters from the file and uses them in fzn2jacop program.
        if(Files.exists(Paths.get(foo + "/options.opt"))) {
            try (BufferedReader reader = Files.newBufferedReader(Paths.get(foo + "/options.opt"), Charset.defaultCharset()))
            {
                String line = null;
                ArrayList<String> options = new ArrayList<String>();
                while ((line = reader.readLine()) != null) {
                    options.add(line);
                }

                    fz2jacop.main(new String[]{options.get(0), options.get(1), "-outputfile", outputFilename, relativePath + filename});
                    FloatDomain.setFormat(Double.MAX_VALUE);

            }
        }
        else
               fz2jacop.main(new String[]{"-outputfile", outputFilename, relativePath + filename});

        String result = new String(Files.readAllBytes(Paths.get(outputFilename)));

        if (printInfo) {
            System.out.println(filename + "\n" + result);
        }

        return Arrays.asList(result.split("\n"));

    }


    protected static List<String> expected(String filename) throws IOException {

        String filePath = new File(relativePath + filename).getAbsolutePath();
        return Files.readAllLines(Paths.get(filePath), StandardCharsets.UTF_8);
    }

    protected static Collection<String> fileReader(String timeCategory) throws IOException {
        System.out.println("timeCategory" + timeCategory);
        FileReader file = new FileReader(relativePath + timeCategory + listFileName);
        BufferedReader br = new BufferedReader(file);
        String line = "";
        List<String> list = new ArrayList<String>();
        int i = 0;
        while ((line = br.readLine()) != null) {
            list.add(i, line);
            i++;
        }
        return list;
    }

    protected void testExecution(String timeCategory) throws IOException {

        System.out.println("Test file: " + timeCategory + testFilename);
        List<String> result = new ArrayList<String>();
        List<String> expectedResult = expected(timeCategory + testFilename + ".out"); //path to file name *.out
        List<String> res = computeResult(timeCategory + testFilename + ".fzn"); // path to file name *.fzn

        if(expectedResult.get(expectedResult.size()-1).equals("==========")){
            int i;
            for(i=0; i <res.size(); i++){
                result.add(res.get(i));
            }
            result.add("==========");
//            result.add(res.listIterator() + "\n==========");
        }else
            result = res;

        if (result.size() == 0)
            fail("\n" + "File path: " + timeCategory + testFilename + ".fzn " + " gave no output to compare against.");

        for (int i = 0, j = 0; i < result.size() || j < expectedResult.size(); ) {
            if (i < result.size() && result.get(i).trim().isEmpty()) {
                i++;
                continue;
            }
            if (j < expectedResult.size() && expectedResult.get(j).trim().isEmpty()) {
                j++;
                continue;
            }
            if (result.size() == i)
                fail("\n" + "File path: " + timeCategory + testFilename + ".out "
                    + " gave as a result less textlines that was expected. Expected line " + (j + 1) + " not found.");
            if (expectedResult.size() == j)
                fail("\n" + "File path: " + timeCategory + testFilename + ".out "
                    + " gave as a result more textlines that was expected. Actual line " + (i + 1) + "not found in expected result");

            assertEquals(
                "\n" + "File path: " + timeCategory + testFilename + ".out " + "\nError line number (expected, actual): (" + (j + 1) + ","
                    + (i + 1) + ")\n", expectedResult.get(j).trim(), result.get(i).trim());
            i++;
            j++;
        }


    }



}
