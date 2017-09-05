package org.jacop.jasat.utils;

import java.io.IOException;
import java.io.InputStream;
import java.util.Iterator;

import org.jacop.jasat.utils.structures.IntVec;

/**
 * CNF file format (low-level) parser.
 *
 * @author simon
 */
public final class CnfParser implements Iterable<IntVec>, Iterator<IntVec> {

    // data of the problem
    public int numClauses = 0;
    public int numVars = 0;

    // stream from which to read values
    private InputStream stream;

    // memory pool
    private MemoryPool pool;

    // current char
    private int c = 0;

    // next clause
    private IntVec nextClause = null;

    // have we already given an iterator on clauses
    private boolean hasGivenIterator = false;

    /**
     * reads an int from the stream
     *
     * @throws IOException
     * @return the parsed int
     */
    private int parseInt() throws IOException {
        int answer = 0;
        if (c == -1)
            throw new IOException();
        assert (c == '-') || (c >= '0' && c <= '9');

        boolean negative = (c == '-');
        if (negative)
            c = stream.read();

        // read digits
        while (c >= '0' && c <= '9') {
            int i = Character.digit(c, 10);
            answer = 10 * answer + i;
            c = stream.read();
        }

        return (negative ? -answer : answer);
    }


    /**
     * skips comment lines from the current position
     *
     * @throws IOException
     */
    private void skipComments() throws IOException {
        if (c != 'c')
            return;

        // skip lines which begin with 'c'
        while (c == 'c')
            skipLine();

    }

    /**
     * skip the rest of the line (\n included)
     *
     * @throws IOException
     */
    private void skipLine() throws IOException {
        // read until \n
        while (c != '\n')
            c = stream.read();

        // skip \n
        assert c == '\n';
        c = stream.read();
    }

    /**
     * skips white spaces and carriage returns
     *
     * @throws IOException
     */
    private void skipSpaces() throws IOException {
        while (c == ' ' || c == '\t' || c == '\n')
            c = stream.read();
    }


    /**
     * reads number of clauses and number of vars
     *
     * @throws IOException
     */
    private void readProblemDef() throws IOException {

        // read "p cnf"
        assert c == 'p';
        c = stream.read();
        skipSpaces();
        assert c == 'c';
        c = stream.read();
        assert c == 'n';
        c = stream.read();
        assert c == 'f';
        c = stream.read();

        // spaces -> int -> spaces -> int
        skipSpaces();
        numVars = parseInt();
        skipSpaces();
        numClauses = parseInt();
    }


    /**
     * parses the next clause from the stream
     */
    private void parseNextClause() {
        IntVec answer = new IntVec(pool);

        try {
            // maybe we just read a clause, so we must discard the 0
            if (c == '0')
                c = stream.read();
        } catch (IOException e1) {
            return;
        }

        while (true) {
            try {
                skipSpaces();
                int curInt = parseInt();
                if (curInt == 0)
                    break;
                else
                    answer.add(curInt);
            } catch (IOException e) {
                break;
            }
        }

        // set nextClause
        if (answer.isEmpty())
            nextClause = null;
        else
            nextClause = answer;
    }



    public boolean hasNext() {
        return nextClause != null;
    }



    public IntVec next() {
        assert nextClause != null;

        IntVec answer = nextClause;
        // prepare next clause
        parseNextClause();
        return answer;
    }



    public void remove() {
        throw new UnsupportedOperationException();
    }

    /**
     * to be called only once!
     */

    public Iterator<IntVec> iterator() {
        if (hasGivenIterator)
            throw new AssertionError("should only iterate once on Parser");
        hasGivenIterator = true;
        return this;
    }


    /**
     * creates an instance of the parser for some input stream
     *
     * @param pool   the memory pool to use
     * @param stream the stream from which to read clauses
     * @throws ParseException excpetion when parsing fails
     */
    public CnfParser(MemoryPool pool, InputStream stream) throws ParseException {
        this.pool = pool;
        this.stream = stream;

        // begin parsing the problem
        try {
            c = stream.read();
            skipComments();
            readProblemDef();

            // prepare the first clause
            parseNextClause();
        } catch (IOException e) {
            System.err.println("error while reading: unable to parse problem");
            throw new ParseException("unable to parse problem");
        }
    }

    /**
     * exception occurring during parse
     *
     * @author simon
     */
    @SuppressWarnings("serial") public static final class ParseException extends Exception {
        public ParseException(String msg) {
            super(msg);
        }

    }

}
