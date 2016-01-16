package org.jacop.jasat.utils.structures;


/**
 * an efficient Set for unboxed int. It is just a subclass for the
 * IntTrie, with a more convenient interface (no generics, simpler constructor).
 * It also provides a part of the interface of BitSet.
 * @author simon
 *
 */
public final class IntSet extends IntTrie<IntTrie.SimpleNode> {

	
	public void set(int i) {
		add(i);
	}
	
	public boolean get(int i) {
		return contains(i);
	}
	
	public void clear(int i) {
		remove(i);
	}
	
	/**
	 * simple initialization of a Set
	 */
	public IntSet() {
		super(new IntTrie.SimpleNode());
	}

	/**
	 * initializes the set with the given integers
	 * @param toAdd	the collection of integers to add
	 */
	public IntSet(Iterable<Integer> toAdd) {
		this();
		for (int i : toAdd)
			add(i);
	}

}
