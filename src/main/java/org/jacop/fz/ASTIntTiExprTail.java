/* Generated By:JJTree: Do not edit this line. ASTIntTiExprTail.java Version 4.1 */
/* JavaCCOptions:MULTI=true,NODE_USES_PARSER=true,VISITOR=false,TRACK_TOKENS=false,NODE_PREFIX=AST,NODE_EXTENDS=,NODE_FACTORY=,SUPPORT_CLASS_VISIBILITY_PUBLIC=true */
package org.jacop.fz;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public
class ASTIntTiExprTail extends SimpleNode { private static Logger logger = LoggerFactory.getLogger(ASTIntTiExprTail.class);
  public ASTIntTiExprTail(int id) {
    super(id);
  }

  public ASTIntTiExprTail(Parser p, int id) {
    super(p, id);
  }

    //type 0=int; 1=interval; 2=list
    int type=-1;
    int low, high;

    public void setType(int t) {
	type=t;
    }
    public int getType() {
	return type;
    }

    public void setLowHigh(int l, int h) {
	low=l; high=h;
    }
    public int getLow() {
	return low;
    }
    public int getHigh() {
	return high;
    }

    public String toString() {
	String limits = type==1 ? ""+low+".."+high : "";
	String typeS=null;
	switch (type) {
	case 0: typeS = "(int): "; break;
	case 1: typeS = "(interval): "; break;
	case 2: typeS = "(list): "; break;
	}
	return super.toString() + typeS + limits;
    }
}
/* JavaCC - OriginalChecksum=f5ca97a90bb21060f4d23a3ce57ab48b (do not edit this line) */
