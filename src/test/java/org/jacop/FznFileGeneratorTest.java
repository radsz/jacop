package org.jacop;

import org.apache.commons.io.FileUtils;
import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.util.Collection;

/**
 * @author Mariusz Świerkot
 */

@RunWith(Parameterized.class)
public class FznFileGeneratorTest extends MinizincBasedTestsHelper {
    private static File sourceFolder = new File("src/test/fz/scriptTest");
    private static File destinationFolder = new File("src/test/fz/test");

    protected static final String Category = "scriptTest/";

    @BeforeClass
    public static void inicjalize() throws IOException {
        copyFolders(sourceFolder, destinationFolder);
        runBashScript();

    }

    public FznFileGeneratorTest(String testFilename)  {
        this.testFilename = testFilename;
    }

    @Parameterized.Parameters
    public static Collection<String> parametricTest() throws IOException {

        return fileReader(Category);
    }

    @Test
    public void testMinizinc() throws IOException {

        String expected = "src/test/fz/scriptGolden/" + this.testFilename +".out";
        String result = null;

        if(new File("src/test/fz/upTo5sec/" + this.testFilename+".out").exists()) {
            result = "src/test/fz/upTo5sec/" + this.testFilename +".out";
        } else
            if (new File("src/test/fz/upTo30sec/" + this.testFilename+".out").exists()){
                result = "src/test/fz/upTo30sec/" + this.testFilename +".out";
            } else
                if (new File("src/test/fz/upTo1min/" + this.testFilename+".out").exists()){
                    result = "src/test/fz/upTo1min/" + this.testFilename +".out";
                } else
                    if (new File("src/test/fz/upTo5min/" + this.testFilename+".out").exists()){
                        result = "src/test/fz/upTo5min/" + this.testFilename +".out";
                    } else
                        if (new File("src/test/fz/upTo1hour/" + this.testFilename+".out").exists()){
                            result = "src/test/fz/upTo1hour/" + this.testFilename +".out";
                        } else
                            if (new File("src/test/fz/above1hour/" + this.testFilename+".out").exists()){
                                result = "src/test/fz/above1hour/" + this.testFilename +".out";
                            } else
                                if (new File("src/test/fz/flakyTest/" + this.testFilename+".out").exists()){
                                    result = "src/test/fz/flakyTest/" + this.testFilename +".out";
                                } else
                                    if (new File("src/test/fz/errors/" + this.testFilename+".out").exists()){
                                        result = "src/test/fz/errors/" + this.testFilename +".out";
                                    }

        System.out.println(expected);
        Assert.assertEquals(FileUtils.readLines(new File(expected)), FileUtils.readLines(new File(result)));

    }



    private static void copyFolders(File sourceFolder, File destinationFolder) throws IOException {

        if (sourceFolder.isDirectory()) {
            if (!destinationFolder.exists()) {
                destinationFolder.mkdir();
                System.out.println("Create folder" + destinationFolder);
            }

            String files[] = sourceFolder.list();
            for (String file : files) {
             if(file != "list.txt" || file != "listgenerator") {
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

            ProcessBuilder pb2 = new ProcessBuilder("/bin/bash", "fznFileGenerator.sh");
            pb2.directory(new File("src/test/fz/"));
            Process p = pb2.start();

            String s = null;
            BufferedReader stdInput = new BufferedReader(new InputStreamReader(p.getInputStream()));

            while ((s = stdInput.readLine()) != null) {
                System.out.println(s);
            }
    }
}

