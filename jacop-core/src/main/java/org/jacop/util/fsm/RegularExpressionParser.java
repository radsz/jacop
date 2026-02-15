/*
 * RegularExpressionParser.java
 * This file is part of JaCoP.
 * <p>
 * JaCoP is a Java Constraint Programming solver.
 * <p>
 * Copyright (C) 2008 Polina Maakeva and Radoslaw Szymanek
 * <p>
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * <p>
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 * <p>
 * Notwithstanding any other provision of this License, the copyright
 * owners of this work supplement the terms of this License with terms
 * prohibiting misrepresentation of the origin of this work and requiring
 * that modified versions of this work be marked in reasonable ways as
 * different from the original version. This supplement of the license
 * terms is in accordance with Section 7 of GNU Affero General Public
 * License version 3.
 * <p>
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see http://www.gnu.org/licenses/.
 */

package org.jacop.util.fsm;

import java.io.Serial;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.List;
import lombok.EqualsAndHashCode;
import lombok.extern.slf4j.Slf4j;
import org.jacop.constraints.regular.Regular;
import org.jacop.core.IntDomain;
import org.jacop.core.IntervalDomain;

/**
 * Instances of this class parse the word combination little language.
 *
 * @author Polina Makeeva and Radoslaw Szymanek
 * @version 5.0
 */
@Slf4j
public class RegularExpressionParser {

  /** Constant denoting an expression. */
  public static final int EXPRESSION = 0;

  /** The constant denoting simple literal. */
  public static final int LITERAL = 1;

  /** The constant denoting concatenation expression. */
  public static final int CONCATENATION = 2;

  /** The constant denoting star expression. */
  public static final int STAR = 3;

  /** The constant denoting sum expression. */
  public static final int SUM = 4;

  private final LexicalAnalyzer lexer; // lexical analyzer that parser uses
  private int token;

  /**
   * It constructs a parser of the regular expression.
   *
   * @param input string reader containing the regular expression.
   */
  public RegularExpressionParser(StringReader input) {

    lexer = new LexicalAnalyzer(input);

    lexer.nextToken();

    if (token != LexicalAnalyzer.WORD && token != LexicalAnalyzer.LEFT_PAREN) {
      // print error message and throw SyntaxException
      expect(LexicalAnalyzer.BEGINNING);
    }
  }

  /**
   * This method parses an expression that it reads from a given input stream.
   *
   * @param parseOneNext if parsing should parse only one item.
   * @return An expression that is the root of the parse tree produced by the parser.
   */
  public Expression parse(boolean parseOneNext) {
    Expression c = null;
    boolean contin = true;
    while (contin) {
      contin = false;
      switch (token) {
        case LexicalAnalyzer.PLUS:
          c = parsePlus(c);
          break;
        case LexicalAnalyzer.DOT:
          c = parseDot(c);
          contin = token != LexicalAnalyzer.EOF;
          break;
        case LexicalAnalyzer.LEFT_PAREN:
          c = parseParen(c);
          contin = token != LexicalAnalyzer.EOF;
          break;
        case LexicalAnalyzer.STAR:
          c = new Star(c);
          lexer.nextToken();
          contin = token != LexicalAnalyzer.EOF;
          break;
        case LexicalAnalyzer.WORD:
          c = parseWord(c);
          contin = token != LexicalAnalyzer.RIGHT_PAREN && token != LexicalAnalyzer.EOF;
          break;
        default:
          break;
      }
      if (parseOneNext && token != LexicalAnalyzer.STAR) {
        contin = false;
      }
    }
    if (Regular.DEBUG_ALL) {
      log.debug("Successful parsing of {}", c);
    }
    return c;
  }

  private Expression parsePlus(Expression c) {
    lexer.nextToken();
    if (token != LexicalAnalyzer.WORD && token != LexicalAnalyzer.LEFT_PAREN) {
      expect(LexicalAnalyzer.BEGINNING);
    }
    Expression c2 = parse(false);
    if (c.getType() == SUM && c2.getType() == SUM) {
      ((Sum) c).addSum((Sum) c2);
    } else if (c.getType() == SUM && c2.getType() != SUM) {
      ((Sum) c).addExp(c2);
    } else if (c.getType() != SUM && c2.getType() == SUM) {
      ((Sum) c2).addExp(c);
      c = c2;
    } else if (c.getType() != SUM && c2.getType() != SUM) {
      c = new Sum(c, c2);
    }
    return c;
  }

  private Expression parseDot(Expression c) {
    lexer.nextToken();
    if (token != LexicalAnalyzer.WORD && token != LexicalAnalyzer.LEFT_PAREN) {
      expect(LexicalAnalyzer.BEGINNING);
    }
    Expression c3 = parse(true);
    c = new Concatenation(c, c3);
    while (token == LexicalAnalyzer.DOT) {
      lexer.nextToken();
      c3 = parse(true);
      c = new Concatenation(c, c3);
    }
    return c;
  }

  private Expression parseParen(Expression c) {
    lexer.nextToken();
    c = parse(false);
    expect(LexicalAnalyzer.RIGHT_PAREN);
    lexer.nextToken();
    return c;
  }

  private Expression parseWord(Expression c) {
    c = new Literal(lexer.getString());
    lexer.nextToken();
    if (token != LexicalAnalyzer.RIGHT_PAREN && token != LexicalAnalyzer.EOF) {
      if (token != LexicalAnalyzer.DOT
          && token != LexicalAnalyzer.STAR
          && token != LexicalAnalyzer.PLUS) {
        expect(LexicalAnalyzer.OPERATOR);
      }
      // contin will be set by caller from switch
    }
    return c;
  }

  /**
   * Complain if the current token is not the specified kind of token.
   *
   * @param t The type of token that is expected.
   */
  private void expect(int t) {

    if (token != t) {

      String msg = "found " + tokenName(token) + " when expecting " + tokenName(t);

      log.error("Syntax error: {}", msg);
    }
  }

  private String tokenName(int t) {

    return switch (t) {
      case LexicalAnalyzer.WORD -> "word";
      case LexicalAnalyzer.LEFT_PAREN -> "(";
      case LexicalAnalyzer.RIGHT_PAREN -> ")";
      case LexicalAnalyzer.EOF -> "end of file";
      case LexicalAnalyzer.BEGINNING -> "literal or right parenthesis";
      case LexicalAnalyzer.OPERATOR -> "operator . or *";
      default -> "???";
    };
  }

  /** SyntaxException raised if not regular expression is being parsed. */
  public static class SyntaxException extends Exception {

    /** Serial version UID for serialization. */
    @Serial private static final long serialVersionUID = 5532774111743285222L;

    /** The constructor to create an syntax exception without the message. */
    public SyntaxException() {}

    /**
     * The constructor to create an syntax exception with a given message.
     *
     * @param msg message for the syntax exception
     */
    public SyntaxException(final String msg) {
      super(msg);
    }
  }

  /** It creates an abstract class expression which specifies basic methods of the expression. */
  public abstract static class Expression {

    /**
     * Returns the type of this expression.
     *
     * @return type
     */
    abstract int getType();

    /**
     * It specifies if the expression is simple.
     *
     * @return true if expression is a literal or disjunction of literals.
     */
    public boolean isSimple() {
      return false;
    }

    /**
     * It creates Finite State Machine from the expression.
     *
     * @return Finite State Machine corresponding
     */
    public abstract Fsm parseToFsm();
  }

  static class Concatenation extends Expression {

    public final Expression a;
    public final Expression b;

    public Concatenation(Expression a, Expression b) {
      super();
      this.a = a;
      this.b = b;
    }

    @Override
    public String toString() {
      return a + "." + b;
    }

    @Override
    public int getType() {
      return CONCATENATION;
    }

    @Override
    public Fsm parseToFsm() {
      return a.parseToFsm().concatenation(b.parseToFsm());
    }
  }

  static class Star extends Expression {

    public final Expression inStar;

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
      return STAR;
    }

    @Override
    public Fsm parseToFsm() {
      return this.inStar.parseToFsm().star();
    }
  }

  static class Sum extends Expression {

    public final List<Expression> disj;

    public Sum(Expression a, Expression b) {
      super();
      this.disj = new ArrayList<>();
      addExp(a);
      addExp(b);
    }

    @Override
    public String toString() {

      StringBuilder result = new StringBuilder("(");

      for (Expression e : this.disj) {
        result.append(e.toString()).append("+");
      }
      result.deleteCharAt(result.length() - 1);
      result.append(")");

      return result.toString();
    }

    @Override
    public int getType() {
      return SUM;
    }

    @Override
    public boolean isSimple() {

      for (Expression e : this.disj) {
        if (!e.isSimple()) {
          return false;
        }
      }
      return true;
    }

    public void addExp(Expression e) {
      if (e.isSimple()) {
        this.disj.addFirst(e);
      } else {
        this.disj.add(e);
      }
    }

    public void addSum(Sum s) {
      for (Expression e : s.disj) {
        addExp(e);
      }
    }

    @Override
    public Fsm parseToFsm() {

      boolean first = true;
      Fsm tmp = null;

      boolean isSimple = true;

      for (Expression e : this.disj) {
        if (first) {
          tmp = e.parseToFsm();
          first = false;
          if (e.getType() != LITERAL) {
            isSimple = false;
          }
        } else if (e.getType() == LITERAL && isSimple) {

          IntDomain dom = tmp.initState.transitions.iterator().next().domain;
          int val = Integer.parseInt(((Literal) e).lit);

          tmp.initState.transitions.iterator().next().domain = dom.union(val);

        } else {
          tmp = tmp.union(e.parseToFsm());
          isSimple = false;
        }
      }
      return tmp;
    }
  }

  /** It specifies a simple literal. */
  @EqualsAndHashCode(callSuper = false)
  public static class Literal extends Expression {

    /** String denoting the literal. */
    public final String lit;

    /**
     * It constructs a literal.
     *
     * @param lit string representation of the literal.
     */
    public Literal(String lit) {
      this.lit = lit;
    }

    @Override
    public int getType() {
      return LITERAL;
    }

    @Override
    public String toString() {
      return lit;
    }

    @Override
    public boolean isSimple() {
      return true;
    }

    @Override
    public Fsm parseToFsm() {

      Fsm c = new Fsm();
      FsmState fin = new FsmState();

      c.initState = new FsmState();

      c.allStates.add(c.initState);
      c.allStates.add(fin);

      c.finalStates.add(fin);

      int val = Integer.parseInt(lit);
      IntervalDomain dom = new IntervalDomain(val, val);
      c.initState.addTransition(new FsmTransition(dom, fin));

      return c;
    }
  }
} // class RegularExpressionParser
