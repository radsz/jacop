package org.jacop;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.*;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.*;


/**
 * @author Mariusz Świerkot
 */

/*
 * At the beginning of the operation, program run the copyFolders function. Function copies files from the scriptTest
 * directory to test directory. Then runBashScript () function runs a listgenerator script which generates file list.txt
 * and runs the fznFileGenerator.sh script. Conditional statements check in which time category is checked test and then
 * compares using diff with test folder in the scriptgolden directory.
*/

@RunWith(Parameterized.class)
public class FznFileGeneratorTest extends MinizincBasedTestsHelper {
    private static String testFolderName = "test";
    private static File sourceFolder = new File("src/test/fz/scriptTest");
    private static File destinationFolder = new File("src/test/fz/" + testFolderName);
    private static List<String> goldList;
    private static List<String> scriptTest;
    private static Iterator<String> itrScriptGold;
    private static Iterator<String> itrScriptTest;
    private static Path expectedDir;
    protected static final String Category = "scriptTest/";
    String testFilename;

    public FznFileGeneratorTest(String testFilename) {
        super(testFolderName);
        this.testFilename = testFilename;

    }

    @Parameterized.Parameters
    public static Collection<String> parametricTest() throws IOException, InterruptedException {
        runListGenerator();
        copyFolders(sourceFolder, destinationFolder);
        runBashScript();
        Files.copy(Paths.get("src/test/fz/scriptGolden/listtmp.txt"),Paths.get("src/test/fz/scriptTest/list.txt"),StandardCopyOption.REPLACE_EXISTING);
        goldList = (List<String>) fileReader("scriptGolden/");
        scriptTest = (List<String>) fileReader("scriptTest/");
        itrScriptGold = goldList.iterator();
        itrScriptTest = scriptTest.iterator();
        return fileReader(Category);
    }

    @Test
    public void testMinizinc() throws IOException, InterruptedException {
        String expected = "";//"src/test/fz/scriptGolden/" + expectedDir;
        String res = "";
        String expectedFzn = "";
        String resFzn = "";

        expectedDir = Paths.get(itrScriptGold.next());
        Path resultDir = Paths.get(itrScriptTest.next());


        File file = new File("src/test/fz/scriptGolden");
        String[] directories = file.list(new FilenameFilter() {
            @Override
            public boolean accept(File current, String name) {
                return new File(current, name).isDirectory();
            }
        });




        for(int i=0; i<directories.length; i++) {
            if(new File("src/test/fz/scriptGolden/" + directories[i] + "/" + resultDir + ".fzn").exists() ){

                expectedDir =  Paths.get( directories[i]+"/" + resultDir );
            }
        }

        if (new File("src/test/fz/upTo5sec/" + Paths.get(this.testFilename).getParent()).isDirectory()) {
            res = "src/test/fz/upTo5sec/" + resultDir + ".out";
            expected = "src/test/fz/scriptGolden/" + expectedDir + ".out";
            resFzn = "src/test/fz/upTo5sec/" + resultDir + ".fzn";
            expectedFzn = "src/test/fz/scriptGolden/" + expectedDir + ".fzn";
        } else if (new File("src/test/fz/upTo30sec/" + Paths.get(this.testFilename).getParent()).isDirectory()) {
            res = "src/test/fz/upTo30sec/" + resultDir + ".out";
            expected = "src/test/fz/scriptGolden/" + expectedDir + ".out";
            resFzn = "src/test/fz/upTo30sec/" + resultDir + ".fzn";
            expectedFzn = "src/test/fz/scriptGolden/" + expectedDir + ".fzn";
        } else if (new File("src/test/fz/upTo1min/" + Paths.get(this.testFilename).getParent()).isDirectory()) {
            res = "src/test/fz/upTo1min/" + resultDir + ".out";
            expected = "src/test/fz/scriptGolden/" + expectedDir + ".out";
            resFzn = "src/test/fz/upTo1min/" + resultDir + ".fzn";
            expectedFzn = "src/test/fz/scriptGolden/" + expectedDir + ".fzn";
        } else if (new File("src/test/fz/upTo5min/" + Paths.get(this.testFilename).getParent()).isDirectory()) {
            res = "src/test/fz/upTo5min/" + resultDir + ".out";
            expected = "src/test/fz/scriptGolden/" + expectedDir + ".out";
            resFzn = "src/test/fz/upTo5min/" + resultDir + ".fzn";
            expectedFzn = "src/test/fz/scriptGolden/" + expectedDir + ".fzn";
        } else if (new File("src/test/fz/upTo1hour/" + Paths.get(this.testFilename).getParent()).isDirectory()) {
            res = "src/test/fz/upTo1hour/" + resultDir + ".out";
            expected = "src/test/fz/scriptGolden/" + expectedDir + ".out";
            resFzn = "src/test/fz/upTo1hour/" + resultDir + ".fzn";
            expectedFzn = "src/test/fz/scriptGolden/" + expectedDir + ".fzn";
        } else if (new File("src/test/fz/above1hour/" + Paths.get(this.testFilename).getParent()).isDirectory()) {
            res = "src/test/fz/above1hour/" + resultDir + ".out";
            expected = "src/test/fz/scriptGolden/" + expectedDir + ".out";
            resFzn = "src/test/fz/above1hour/" + resultDir + ".fzn";
            expectedFzn = "src/test/fz/scriptGolden/" + expectedDir + ".fzn";
        } else if (new File("src/test/fz/flakyTest/" + Paths.get(this.testFilename).getParent()).isDirectory()) {
            res = "src/test/fz/flakyTest/" + resultDir + ".out";
            expected = "src/test/fz/scriptGolden/" + expectedDir + ".out";
            resFzn = "src/test/fz/flakyTest/" + resultDir + ".fzn";
            expectedFzn = "src/test/fz/scriptGolden/" + expectedDir + ".fzn";
        } else if (new File("src/test/fz/errors/" + Paths.get(this.testFilename).getParent()).isDirectory()) {
            res = "src/test/fz/errors/" + resultDir + ".out";
            expected = "src/test/fz/scriptGolden/" + expectedDir + ".out";
            resFzn = "src/test/fz/errors/" + resultDir + ".fzn";
            expectedFzn = "src/test/fz/scriptGolden/" + expectedDir + ".fzn";
        }

//            System.out.println(expected);
        ProcessBuilder pb1 = new ProcessBuilder("diff", "-r", res, expected);
        Process p2 = pb1.start();
        p2.waitFor();

        ProcessBuilder pb3 = new ProcessBuilder("diff", "-r", resFzn, expectedFzn);
        Process p4 = pb3.start();
        p4.waitFor();

        boolean result = false;

        if (0 == p2.waitFor() && 0 == p4.waitFor() ) {
            result = true;
            System.out.println(expected +"\n" + expectedFzn);
        }


        String s = null;
        String ss = null;
        BufferedReader stdInput = new BufferedReader(new InputStreamReader(p2.getInputStream()));
        BufferedReader stdInputFzn = new BufferedReader(new InputStreamReader(p4.getInputStream()));
        while ((s = stdInput.readLine()) != null || (ss = stdInputFzn.readLine()) != null) {
            if( s != null) {
                System.out.println(expected + "\n" + s);
            }
            if( ss != null) {
                System.out.println(expectedFzn + "\n" + ss);
            }
        }

        Assert.assertEquals(true, result);


    }

    private static void copyFolders(File sourceFolder, File destinationFolder) throws IOException {
        if (sourceFolder.isDirectory()) {
            if (!destinationFolder.exists()) {
                destinationFolder.mkdir();
            }

            String files[] = sourceFolder.list();
            for (String file : files) {
                if(!file.equals("list.txt") && !file.equals("listgenerator")) {
                    File srcFile = new File(sourceFolder, file);
                    File dstFile = new File(destinationFolder, file);
                    copyFolders(srcFile, dstFile);
                }
            }


        } else
            Files.copy(sourceFolder.toPath(), destinationFolder.toPath(), StandardCopyOption.REPLACE_EXISTING);

    }

    private static void runListGenerator() throws IOException, InterruptedException {

        ProcessBuilder pb2 = new ProcessBuilder("/bin/bash", "listgenerator.sh");
        pb2.directory(new File("src/test/fz/scriptGolden"));
        Process p2 = pb2.start();
        p2.waitFor();

        ProcessBuilder pb1 = new ProcessBuilder("/bin/bash", "listgenerator.sh");
        pb1.directory(new File("src/test/fz/scriptTest"));
        Process p1 =pb1.start();
        p1.waitFor();

    }

    private static void runBashScript() throws IOException, InterruptedException {

        ProcessBuilder pb3 = new ProcessBuilder("/bin/bash", "fznFileGenerator.sh" , testFolderName.toString() );
        pb3.directory(new File("src/test/fz/"));
        Process p = pb3.start();
        p.waitFor();

        String s = null;
        BufferedReader stdInput = new BufferedReader(new InputStreamReader(p.getInputStream()));

        while ((s = stdInput.readLine()) != null) {
            System.out.println(s);
        }
    }
}

