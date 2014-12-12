/**
 *  LexicalAnalyzer.java 
 *  This file is part of JaCoP.
 *
 *  JaCoP is a Java Constraint Programming solver. 
 *	
 *	Copyright (C) 2008 Polina Maakeva and Radoslaw Szymanek
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU Affero General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Affero General Public License for more details.
 *  
 *  Notwithstanding any other provision of this License, the copyright
 *  owners of this work supplement the terms of this License with terms
 *  prohibiting misrepresentation of the origin of this work and requiring
 *  that modified versions of this work be marked in reasonable ways as
 *  different from the original version. This supplement of the license
 *  terms is in accordance with Section 7 of GNU Affero General Public
 *  License version 3.
 *
 *  You should have received a copy of the GNU Affero General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 *
 */

package org.jacop.util.fsm;

import java.io.IOException;
import java.io.StreamTokenizer;
import java.io.StringReader;

/**
 * @author Polina Maakeva and Radoslaw Szymanek
 * @version 4.2
 */

class LexicalAnalyzer {
	
    private StreamTokenizer input;

    // constants to identify the type of the last recognized token.
    static final int INVALID_CHAR = -1;// unexpected character found.
    static final int NO_TOKEN = 0;// No tokens recognized yet.

    static final int PLUS = 3;
    static final int DOT = 4;
    static final int WORD = 5;
    static final int LEFT_PAREN = 6;
    static final int RIGHT_PAREN = 7;
    static final int STAR = 8;
    static final int EOF = 9;
    
    static final int Operator = 10;
    static final int Beginning = 11;
    
    /**
     * Constructor creating a Lexical Analyzer.
     * @param in the StringReader providing the characters which are being analyzed.
     */
    LexicalAnalyzer(StringReader in) {
    	
    	input = new StreamTokenizer(in);
        input.resetSyntax();
        input.eolIsSignificant(false);
        input.wordChars('a', 'z');
        input.wordChars('A','Z');
        input.wordChars('0','9');
        input.wordChars('\u0000',' '-1);
        input.ordinaryChar('(');
        input.ordinaryChar(')');
        input.quoteChar('"');
    } 
    
    /**
     * Return the string recognized as word token or the body of a
     * quoted string.
     */
    String getString() {
        return input.sval;
    }
    
    /**
     * Return the type of the next token.  For word and quoted string
     * tokens, the string that the token represents can be fetched by
     * calling the getString method.
     */
    int nextToken() {
    
    	int token;
        
    	try {
            switch (input.nextToken()) {
              case StreamTokenizer.TT_EOF:
                  token = EOF;
                  break;
              case StreamTokenizer.TT_WORD:
                  token = WORD;
                  break;
              case '(':
                  token = LEFT_PAREN;
                  break;
              case ')':
                  token = RIGHT_PAREN;
                  break;
              case '*':
                  token = STAR;
                  break;
              case '+':
                  token = PLUS;
                  break;
              case '.':
                  token = DOT;
                  break;
              default:
                  token = INVALID_CHAR;
                  break;
            } // switch
        } catch (IOException e) {
            // Treat an IOException as an end of file
            token = EOF;
        } 
        return token;
    } 
} 
