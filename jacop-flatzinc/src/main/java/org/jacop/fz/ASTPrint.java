package org.jacop.fz;

import lombok.extern.slf4j.Slf4j;

/**
 * ASTPrint.java
 *
 * <p>Prinitng of AST nodes generated bt jjtree
 */
@Slf4j
public class ASTPrint {
  private int indent = 1;

  private String indentString() {
    return "  ".repeat(Math.max(0, indent));
  }

  public void print(Node node) {
    log.info("\nPrinting the tree ...");
    dfs_visit(node);
  }

  private void dfs_visit(Node node) {
    log.info(indentString() + node.toString());
    ++indent;
    int count = node.jjtGetNumChildren();
    for (int i = 0; i < count; i++) {
      Node child = node.jjtGetChild(i);
      dfs_visit(child);
    }
    --indent;
  }
}
