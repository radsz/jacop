package org.jacop.satwrapper;

/**
 * a component that is aware of the existence of a SatWrapper
 * @author simon
 *
 */
public interface WrapperComponent {

	/**
	 * connect the component to the wrapper
	 * @param wrapper	the wrapper
	 */
  void initialize(SatWrapper wrapper);
	
}
