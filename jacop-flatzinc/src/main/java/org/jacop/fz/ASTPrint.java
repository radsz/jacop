package org.jacop.fz;

/**
 * ASTPrint.java
 *
 * <p>Prinitng of AST nodes generated bt jjtree
 */
public class ASTPrint {
  private int indent = 1;

  private String indentString() {
    StringBuilder sb = new StringBuilder();
    for (int i = 0; i < indent; ++i) {
      sb.append("  ");
    }
    return sb.toString();
  }

  public void print(Node node) {
    System.out.println("\nPrinting the tree ...");
    dfs_visit(node);
  }

  private void dfs_visit(Node node) {
    System.out.println(indentString() + node.toString());
    ++indent;
    int count = node.jjtGetNumChildren();
    for (int i = 0; i < count; i++) {
      Node child = node.jjtGetChild(i);
      dfs_visit(child);
    }
    --indent;
  }
}
