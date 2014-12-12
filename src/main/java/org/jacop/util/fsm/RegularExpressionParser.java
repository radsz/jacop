/**
 *  RegularExpressionParser.java 
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

import java.io.StringReader;
import java.util.ArrayList;

import org.jacop.constraints.regular.Regular;
import org.jacop.core.IntDomain;
import org.jacop.core.IntervalDomain;

/**
 * Instances of this class parse the word combination little language.
 * 
 * @author Polina Makeeva and Radoslaw Szymanek
 * @version 4.2
 */

public class RegularExpressionParser {

	private LexicalAnalyzer lexer; // lexical analyzer that parser uses
	
	private int token;

	/**
	 * It constructs a parser of the regular expression.
	 * @param input string reader containing the regular expression.
	 * @throws SyntaxException if first token is neither word or left parenthesis. 
	 */
	public RegularExpressionParser(StringReader input) throws SyntaxException {
		
		lexer = new LexicalAnalyzer(input);
		
		lexer.nextToken();
		
		if (token != LexicalAnalyzer.WORD
				&& token != LexicalAnalyzer.LEFT_PAREN) {
			// print error message and throw SyntaxException
			expect(LexicalAnalyzer.Beginning);
		} 
	}

	/**
	 * This method parses an expression that it reads from a given input stream.
	 * @param parseOneNext if parsing should parse only one item.
	 * 
	 * @return An expression that is the root of the parse tree produced by the parser.
	 * @throws SyntaxException 
	 */
	public Expression parse(boolean parseOneNext) throws SyntaxException {

		Expression c = null;

		boolean contin = true;

		while (contin) {
			contin = false;

			switch (token) {
			case LexicalAnalyzer.PLUS:
				lexer.nextToken();
				if (token != LexicalAnalyzer.WORD
						&& token != LexicalAnalyzer.LEFT_PAREN) {
					// print error message and throw SyntaxException
					expect(LexicalAnalyzer.Beginning);
				} // if
				Expression c2 = parse(false);
				if (c.getType() == RegularExpressionParser.Sum
						&& c2.getType() == RegularExpressionParser.Sum)
					((Sum) c).addSum((Sum) c2);

				if (c.getType() == RegularExpressionParser.Sum
						&& c2.getType() != RegularExpressionParser.Sum)
					((Sum) c).addExp(c2);

				if (c.getType() != RegularExpressionParser.Sum
						&& c2.getType() == RegularExpressionParser.Sum) {
					((Sum) c2).addExp(c);
					c = c2;
				}

				if (c.getType() != RegularExpressionParser.Sum
						&& c2.getType() != RegularExpressionParser.Sum)
					c = new Sum(c, c2);

				break;

			case LexicalAnalyzer.DOT:

				lexer.nextToken();
				if (token != LexicalAnalyzer.WORD
						&& token != LexicalAnalyzer.LEFT_PAREN) {
					// print error message and throw SyntaxException
					expect(LexicalAnalyzer.Beginning);
				} // if

				Expression c3 = parse(true);
				c = new Concatination(c, c3);
				while (token == LexicalAnalyzer.DOT) {
					lexer.nextToken();
					c3 = parse(true);
					c = new Concatination(c, c3);
				}

				if (token != LexicalAnalyzer.EOF)
					contin = true;
				break;

			case LexicalAnalyzer.LEFT_PAREN:
				lexer.nextToken();
				c = parse(false);
				expect(LexicalAnalyzer.RIGHT_PAREN);
				lexer.nextToken();
				if (token != LexicalAnalyzer.EOF)
					contin = true;
				break;

			case LexicalAnalyzer.STAR:
				c = new Star(c);
				lexer.nextToken();
				if (token != LexicalAnalyzer.EOF)
					contin = true;
				break;

			case LexicalAnalyzer.WORD:
				c = new Literal(lexer.getString());
				lexer.nextToken();
				if (token != LexicalAnalyzer.RIGHT_PAREN
						&& token != LexicalAnalyzer.EOF) {
					if (token != LexicalAnalyzer.DOT
							&& token != LexicalAnalyzer.STAR
							&& token != LexicalAnalyzer.PLUS) {
						// print error message and throw SyntaxException
						expect(LexicalAnalyzer.Operator);
					} // if
					contin = true;
				}

				break;
			}

			if (parseOneNext == true && !(token == LexicalAnalyzer.STAR))
				contin = false;

		}

		if (Regular.debugAll)
			System.out.println("Succesful parsing of " + c);

		return c;
	}

	/**
	 * Complain if the current token is not the specified kind of token.
	 * 
	 * @param t The type of token that is expected.
	 */
	private void expect(int t) throws SyntaxException {

		if (token != t) {
			
			String msg = "found " + tokenName(token) + " when expecting "
					+ tokenName(t);
			
			System.err.println("Syntax error: " + msg);
		
		} 

	} 
	
	private String tokenName(int t) {
	
		switch (t) {
		case LexicalAnalyzer.WORD:
			return "word";
		case LexicalAnalyzer.LEFT_PAREN:
			return "(";
		case LexicalAnalyzer.RIGHT_PAREN:
			return ")";
		case LexicalAnalyzer.EOF:
			return "end of file";
		case LexicalAnalyzer.Beginning:
			return "literal or right parenthesis";
		case LexicalAnalyzer.Operator:
			return "operator . or *";
		default:
			return "???";
		} 

	} 
	
	/**
	 * Constant denoting an expression.
	 */
	public static final int Expression = 0;
	
	/**
	 * The constant denoting simple literal.
	 */
	public static final int Literal = 1;
	/**
	 * The constant denoting concatenation expression.
	 */
	public static final int Concatenation = 2;
	/**
	 * The constant denoting star expression.
	 */
	public static final int Star = 3;
	/**
	 * The constant denoting sum expression.
	 */
	public static final int Sum = 4;

	
	/**
	 * SyntaxException raised if not regular expression is being parsed.
	 *
	 */
	public class SyntaxException extends Exception {

		/**
		 * 
		 */
		private static final long serialVersionUID = 5532774111743285222L;

		/**
		 * The constructor to create an syntax exception without the message.
		 */
		public SyntaxException() {
		}

		/**
		 * The constructor to create an syntax exception with a given message.
		 * @param msg
		 */
		public SyntaxException(final String msg) {
			super(msg);
		}
	}

	/**
	 * It creates an abstract class expression which specifies basic methods of 
	 * the expression.
	 *
	 */
	public abstract class Expression {

		/**
		 * If the given string contains the words that this Expression object
		 * requires, this method returns an array of ints. In most cases, the
		 * array contains the offsets of the words in the string that are
		 * required by this combination. However, if the array is empty, then
		 * all the words in the string satisfy the Expression. If the given
		 * string does not contain the words that this Expression object
		 * requires, then this method returns null.
		 * 
		 * @param set
		 *            The string that this method will search for the words it
		 *            requires.
		 */

		abstract int getType();

		/**
		 * It specifies if the expression is simple.
		 * @return true if expression is a literal or disjunction of literals.
		 */
		public boolean isSimple() {
			return false;
		}

		/**
		 * It creates Finite State Machine from the expression.
		 * @return Finite State Machine corresponding 
		 */
		public abstract FSM parseToFSM();

	}

	class Concatination extends Expression {

		public Expression a;
		public Expression b;

		public Concatination(Expression a, Expression b) {
			super();
			this.a = a;
			this.b = b;
		}

		@Override
		public String toString() {
			return "" + a + "." + b;
		}

		@Override
		public int getType() {
			return Concatenation;
		}

		@Override
		public FSM parseToFSM() {
			return a.parseToFSM().concatenation(b.parseToFSM());
		}
	}

	class Star extends Expression {

		public Expression inStar;

		public Star(Expression inStar) {
			super();
			this.inStar = inStar;
		}

		@Override
		public String toString() {
			return "(" + inStar + ")*";
		}

		@Override
		public int getType() {
			return Star;
		}

		@Override
		public FSM parseToFSM() {
			return this.inStar.parseToFSM().star();
		}

	}

	class Sum extends Expression {

		public ArrayList<Expression> disj;

		public Sum(Expression a, Expression b) {
			super();
			this.disj = new ArrayList<Expression>();
			addExp(a);
			addExp(b);
		}

		@Override
		public String toString() {

			StringBuffer result = new StringBuffer("(");
			
			for (Expression e : this.disj)
				result.append(e.toString()).append("+");
			result.deleteCharAt(result.length() - 1);			
			result.append(")");
			
			return result.toString();

		}

		@Override
		public int getType() {
			return RegularExpressionParser.Sum;
		}

		@Override
		public boolean isSimple() {

			for (Expression e : this.disj)
				if (!e.isSimple())
					return false;
			return true;
		}

		public void addExp(Expression e) {
			if (e.isSimple())
				this.disj.add(0, e);
			else
				this.disj.add(e);
		}

		public void addSum(Sum s) {
			for (Expression e : s.disj)
				addExp(e);
		}

		@Override
		public FSM parseToFSM() {

			boolean first = true;
			FSM tmp = null;

			boolean isSimple = true;

			for (Expression e : this.disj) {
				if (first) {
					tmp = e.parseToFSM();
					first = false;
					if (e.getType() != RegularExpressionParser.Literal)
						isSimple = false;
				} else if (e.getType() == RegularExpressionParser.Literal && isSimple) {

					IntDomain dom = tmp.initState.transitions.iterator().next().domain;
					int val = Integer.parseInt(((Literal) e).lit);

					tmp.initState.transitions.iterator().next().domain = dom.union(val);

				} else {
					tmp = tmp.union(e.parseToFSM());
					isSimple = false;
				}
			}
			return tmp;
		}
	}

	/**
	 * It specifies a simple literal.
	 */
	
	public class Literal extends Expression {

		/**
		 * String denoting the literal.
		 */
		public String lit;

		
		/**
		 * It constructs a literal.
		 * @param lit string representation of the literal.
		 */
		public Literal(String lit) {
			this.lit = lit;
		}

		@Override
		public int getType() {
			return RegularExpressionParser.Literal;
		}

		@Override
		public String toString() {
			return lit;
		}

		@Override
		public boolean equals(Object c) {
			return lit.equals(c);
		}

		@Override
		public boolean isSimple() {
			return true;
		}

		@Override
		public FSM parseToFSM() {

			FSM c = new FSM();
			FSMState fin = new FSMState();

			c.initState = new FSMState();

			c.allStates.add(c.initState);
			c.allStates.add(fin);

			c.finalStates.add(fin);

			int val = Integer.parseInt(lit);
			IntervalDomain dom = new IntervalDomain(val, val);
			c.initState.addTransition(new FSMTransition(dom, fin));

			return c;
		}

	}

} // class RegularExpressionParser

