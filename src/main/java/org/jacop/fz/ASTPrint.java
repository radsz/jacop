package org.jacop.fz;

/**
 *
 * ASTPrint.java
 *
 * Prinitng of AST nodes generated bt jjtree
 *
 */

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ASTPrint { private static Logger logger = LoggerFactory.getLogger(ASTPrint.class);
  private int indent = 1;

  private String indentString() {
    StringBuffer sb = new StringBuffer();
    for (int i = 0; i < indent; ++i) {
      sb.append("  ");
    }
    return sb.toString();
  }

  public void print(Node node) {
	  logger.info("\nPrinting the tree ...");
	  dfs_visit(node);
  }

  private void dfs_visit(Node node) {
    logger.info(indentString() + node.toString());
    ++indent;
    int count = node.jjtGetNumChildren();
    for (int i=0;i<count;i++) {
	    Node child = node.jjtGetChild(i);
	    dfs_visit(child);
    }
    --indent;
  }

}
