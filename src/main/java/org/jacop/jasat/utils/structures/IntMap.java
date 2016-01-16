package org.jacop.jasat.utils.structures;

public final class IntMap<E> {

	// the inner trie
	private final IntTrie<MapNode> map; 
	
	/**
	 * predicate to check if the key is associated to any value
	 * @param key	the key
	 * @return true if the key is associated to some value
	 */
	public boolean containsKey(int key) {
		return map.contains(key);
	}
	
	/**
	 * get the value associated with the key, or null
	 * @param key	the key
	 * @return the value or null
	 */
	public E get(int key) {
		MapNode n = map.getNode(key);
		boolean isPos = key >= 0;
		if (n == null)
			return null;
		if (isPos && n.posMember)
			return n.posValue;
		else if (n.negMember)
			return n.negValue;
		else
			return null;
	}
	
	/**
	 * associates key with value
	 * @param key	the key
	 * @param value	the value
	 * @return the old value, if any, or null
	 */
	public E put(int key, E value) {
		MapNode n = map.add(key);
		boolean isPos = key >= 0;
		E answer = null;
		
		if (isPos) {
			if (n.posMember)
				answer = n.posValue;
			n.posValue = value;
		} else {
			if (n.negMember)
				answer = n.negValue;
			n.negValue = value;
		}
		return answer; 
	}
	
	/**
	 * remove the association key/value (if any)
	 * @param key	the key to remove from the Map
	 * @return true if key was associated with some value
	 */
	public boolean remove(int key) {
		return map.remove(key);
	}
	
	/**
	 * @return the number of keys in the map
	 */
	public int size() {
		return map.size();
	}
	
	/**
	 * predicate to check if the map is empty
	 *
	 * @return true if the map is empty, false otherwise
	 */
	public boolean isEmpty() {
		return map.isEmpty();
	}
	
	/**
	 * clear the map (removes everything inside)
	 */
	public void clear() {
		map.clear();
	}
	
	/**
	 * initializes the map
	 */
	public IntMap() {
		map = new IntTrie<MapNode>(new MapNode());
	}
	
	/**
	 * Node that carries the data needed for a map
	 * @author simon
	 *
	 */
	private final class MapNode extends IntTrie.Node<MapNode> {
		
		// value carried by the node for positive key
		E posValue;
		
		// value carried by the node for negative key
		E negValue;
		
		@Override
		public MapNode getNew() {
			return new MapNode();
		}
	}
}
