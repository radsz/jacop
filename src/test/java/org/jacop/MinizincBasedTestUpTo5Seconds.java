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

/**
 * @author Mariusz Świerkot
 */

@RunWith(Parameterized.class)
public class MinizincBasedTestUpTo5Seconds {
    private List<String> inputString;
    private static Fz2jacop fz2jacop;
    private static final String relativePath = "src/test/fz/";
    private static final boolean printInfo = true;

    @BeforeClass
    public static void initialize() {
        fz2jacop = new Fz2jacop();
    }


    public MinizincBasedTestUpTo5Seconds(List<String> inputString) {

        this.inputString = new ArrayList<String>();
        for(int i=0; i<inputString.size(); i++) {
            this.inputString.add(inputString.get(i));

        }
    }

    @Parameterized.Parameters
    public static Collection parametricTest() throws IOException {

        FileReader file = new FileReader("src/test/fz/upTo5sec/list.txt");
        BufferedReader br = new BufferedReader(file);
        String line = "";
        List<String> list = new ArrayList<String>();
        int i = 0;
        while ((line = br.readLine())!=null) {
            list.add(i, line);
            i++;
        }

        return Arrays.asList(new Object[][]{
                {list}
        });
    }



    @Test(timeout=5400000)
    public void testMinizinc() throws IOException {
        List<String> expectedResult = new ArrayList<>();
        List<String> result = new ArrayList<>();

        for(int i= 0; i < this.inputString.size(); i++) {
            expectedResult = expected("upTo5sec/" + this.inputString.get(i) + ".out");
            result = result("upTo5sec/" + this.inputString.get(i) + ".fzn");
        }

        for (int i = 0; i < result.size(); i++) {
            assertEquals("\n" + "File path: " + "upTo5sec/" +this.inputString.get(i) + ".out " + "\nError line number: " + (i + 1) + "\n",
                    expectedResult.get(i), result.get(i));
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