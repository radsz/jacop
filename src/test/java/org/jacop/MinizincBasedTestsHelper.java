package org.jacop;

import org.jacop.fz.Fz2jacop;
import org.junit.BeforeClass;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;

/**
 * @author Mariusz Świerkot
*/

public class MinizincBasedTestsHelper {
    protected String testFilename;
    protected static Fz2jacop fz2jacop;
    protected static final String relativePath = "src/test/fz/";
    protected static final String timeCategory = "upTo5sec/";
    protected static final String listFileName = "list.txt";
    protected static final boolean printInfo = true;

    @BeforeClass
    public static void initialize() {
        fz2jacop = new Fz2jacop();
    }


    protected static List<String> result(String filename) {

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


    protected static List<String> expected(String filename) throws IOException {

        String filePath = new File(relativePath + filename ).getAbsolutePath();
        return Files.readAllLines(Paths.get(filePath), StandardCharsets.UTF_8);
    }



}
