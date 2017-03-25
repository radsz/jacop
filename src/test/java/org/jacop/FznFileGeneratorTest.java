package org.jacop;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;
import java.util.Collection;


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

    protected static final String Category = "scriptTest/";

//    @BeforeClass
//    public static void inicjalize() throws IOException {
//        copyFolders(sourceFolder, destinationFolder);
//
//
//    }

    public FznFileGeneratorTest(String testFilename)  {

        this.testFilename = testFilename;

    }

    @Parameterized.Parameters
    public static Collection<String> parametricTest() throws IOException {
        copyFolders(sourceFolder, destinationFolder);
        runBashScript();

        return fileReader(Category);
    }

    @Test
    public void testMinizinc() throws IOException, InterruptedException {
        Path expectedDir = Paths.get(this.testFilename).getParent();

        String expected = "";//"src/test/fz/scriptGolden/" + expectedDir;

        String res = "";

        if(new File("src/test/fz/upTo5sec/" + Paths.get(this.testFilename).getParent()).isDirectory()) {
            res = "src/test/fz/upTo5sec/" + Paths.get(this.testFilename).getParent();
            expected = "src/test/fz/scriptGolden/upTo5sec/" + expectedDir;
        } else
        if (new File("src/test/fz/upTo30sec/" + Paths.get(this.testFilename).getParent()).isDirectory()){
            res = "src/test/fz/upTo30sec/" + Paths.get(this.testFilename).getParent();
            expected = "src/test/fz/scriptGolden/upTo30sec/" + expectedDir;
        } else
        if (new File("src/test/fz/upTo1min/" + Paths.get(this.testFilename).getParent()).isDirectory()){
            res = "src/test/fz/upTo1min/" + Paths.get(this.testFilename).getParent();
            expected = "src/test/fz/scriptGolden/upTo1min/" + expectedDir;
        } else
        if (new File("src/test/fz/upTo5min/" + Paths.get(this.testFilename).getParent()).isDirectory()){
            res = "src/test/fz/upTo5min/" + Paths.get(this.testFilename).getParent();
            expected = "src/test/fz/scriptGolden/upTo5min/" + expectedDir;
        } else
        if (new File("src/test/fz/upTo1hour/" + Paths.get(this.testFilename).getParent()).isDirectory()){
            res = "src/test/fz/upTo1hour/" + Paths.get(this.testFilename).getParent();
            expected = "src/test/fz/scriptGolden/upTo1hour/" + expectedDir;
        } else
        if (new File("src/test/fz/above1hour/" + Paths.get(this.testFilename).getParent()).isDirectory()){
            res = "src/test/fz/above1hour/" + Paths.get(this.testFilename).getParent();
            expected = "src/test/fz/scriptGolden/above1hour/" + expectedDir;
        } else
        if (new File("src/test/fz/flakyTest/" + Paths.get(this.testFilename).getParent()).isDirectory()){
            res = "src/test/fz/flakyTest/" + Paths.get(this.testFilename).getParent();
            expected = "src/test/fz/scriptGolden/flakyTest/" + expectedDir;
        } else
        if (new File("src/test/fz/errors/" + Paths.get(this.testFilename).getParent()).isDirectory()){
            res = "src/test/fz/errors/" + Paths.get(this.testFilename).getParent();
            expected = "src/test/fz/scriptGolden/errors/" + expectedDir;
        }

        System.out.println(expected);
        ProcessBuilder pb1 = new ProcessBuilder("diff", "-r", res, expected);
        Process p2 = pb1.start();
        boolean result = false;
        if( 0 == p2.waitFor() ) {
            result = true;
            System.out.println(expected);
        }
        String s = null;
        BufferedReader stdInput = new BufferedReader(new InputStreamReader(p2.getInputStream()));

        while ((s = stdInput.readLine()) != null) {
            System.out.println(expected + "\n" + s);
        }

        Assert.assertEquals(true, result );



    }


    private static void copyFolders(File sourceFolder, File destinationFolder) throws IOException {

        if (sourceFolder.isDirectory()) {
            if (!destinationFolder.exists()) {
                destinationFolder.mkdir();
//                System.out.println("Create folder" + destinationFolder);
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

    private static void runBashScript() throws IOException {
        ProcessBuilder pb1 = new ProcessBuilder("/bin/bash", "listgenerator");
        pb1.directory(new File("src/test/fz/scriptTest"));
        pb1.start();

        ProcessBuilder pb2 = new ProcessBuilder("/bin/bash", "fznFileGenerator.sh" , testFolderName.toString() );
        pb2.directory(new File("src/test/fz/"));
        Process p = pb2.start();

        String s = null;
        BufferedReader stdInput = new BufferedReader(new InputStreamReader(p.getInputStream()));

        while ((s = stdInput.readLine()) != null) {
            System.out.println(s);
        }
    }
}

