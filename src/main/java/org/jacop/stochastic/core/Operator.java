package org.jacop.stochastic.core;

/**
 * Defines an Operator class.  
 */
public class Operator {
	
    /**
     * Defines an enumeration for Binary Arithmetic Operations: 
     * "+", "-", "*", "/", "max" and "min".
     */
    public enum ArithOp {
	ADD, SUBTRACT, MULTIPLY, DIVIDE, MAX, MIN, INVALID
	    }
	
    /**
     * Defines an enumeration for Comparision Operators :
     * "<", "<=", "==", ">" and ">=".
     */
    public enum CompOp {
	LESS, LESS_EQUAL, EQUAL, NOT_EQUAL, GREATER, GREATER_EQUAL, INVALID
	    }
	
    /**
     * Binary arithmetic operation.
     */
    public ArithOp aOp;
	
    /**
     * Comparision operation.
     */
    public CompOp cOp;
	
    /**
     * This constructor creates an Operator instance based on the input 
     * String parameter. The operator is either a comparision operator
     * or an arithmetic operator.
     * @param input : Input String
     */
    public Operator(String input){
		
	if (input.equals("<")) {
	    cOp = CompOp.LESS;
	    aOp = ArithOp.INVALID;
	}
		
	else if (input.equals("<=")){
	    cOp = CompOp.LESS_EQUAL;
	    aOp = ArithOp.INVALID;
	}
		
	else if (input.equals("==")){
	    cOp = CompOp.EQUAL;
	    aOp = ArithOp.INVALID;
	}

        else if (input.equals("!=")){
            cOp = CompOp.NOT_EQUAL;
            aOp = ArithOp.INVALID;
        }

	else if (input.equals(">")){
	    cOp = CompOp.GREATER;
	    aOp = ArithOp.INVALID;
	}
		
	else if (input.equals(">=")){
	    cOp = CompOp.GREATER_EQUAL;
	    aOp = ArithOp.INVALID;
	}
		
	else if (input.equals("+")){
	    aOp = ArithOp.ADD;
	    cOp = CompOp.INVALID;
	}
		
	else if (input.equals("-")){
	    aOp = ArithOp.SUBTRACT;
	    cOp = CompOp.INVALID;
	}
		
	else if (input.equals("*")){
	    aOp = ArithOp.MULTIPLY;
	    cOp = CompOp.INVALID;
	}
		
	else if (input.equals("/")){
	    aOp = ArithOp.DIVIDE;
	    cOp = CompOp.INVALID;
	}
		
	else if (input.equals("max")){
	    aOp = ArithOp.MAX;
	    cOp = CompOp.INVALID;
	}
		
	else if (input.equals("min")){
	    aOp = ArithOp.MIN;
	    cOp = CompOp.INVALID;
	}
		
	else{
	    aOp = ArithOp.INVALID;
	    cOp = CompOp.INVALID;	
	}	
    }
	
    /**
     * This constructor creates an Operator instance for an 
     * arithmetic operation.
     * @param aOp : Aritmetic Operation
     */
    public Operator(ArithOp aOp){
	this.aOp = aOp;
	this.cOp = CompOp.INVALID;
    }
	
    /**
     * This constructor creates an Operator instance for a 
     * comparision operation.
     * @param cOp : Comparision Operation
     */
    public Operator(CompOp cOp){
	this.cOp = cOp;
	this.aOp = ArithOp.INVALID;
    }
	
    /**
     * This method performs the required comparision operation between
     * 2 input parameters.
     * @param x : Parameter
     * @param y : Parameter
     * @return x op y
     */
    public boolean doCompOp(int x, int y){
		
	assert (cOp != CompOp.INVALID) : "Invalid Comparison Operation";
		
	boolean result = false;
		
	switch (cOp){
		
	case LESS:
	    result = (x < y); 
	    break;
			
	case LESS_EQUAL:
	    result = (x <= y); 
	    break;
			
	case EQUAL:
	    result = (x == y); 
	    break;
			
        case NOT_EQUAL:
            result = (x != y);
            break;

	case GREATER:
	    result = (x > y); 
	    break;
			
	case GREATER_EQUAL:
	    result = (x >= y); 
	    break;				
	}
		
	return result;
    }
	
    /**
     * This method performs the required arithmetic operation between
     * 2 input parameters.
     * @param x : Parameter
     * @param y : Parameter
     * @return x op y
     */
    public int doArithOp(int x, int y){
		
	assert (aOp != ArithOp.INVALID) : "Invalid Arithmetic Operation";

	int result = 0;
		
	switch (aOp){
		
	case ADD:
	    result = (x + y); 
	    break;
			
	case SUBTRACT:
	    result = (x - y); 
	    break;
			
	case MULTIPLY:
	    result = (x * y); 
	    break;
			
	case DIVIDE:
	    result = (x / y); 
	    break;

	case MAX:
	    result = (x >= y) ? x : y; 
	    break;

	case MIN:
	    result = (x <= y) ? x : y; 
	    break;
	}
		
	return result;
    }
}