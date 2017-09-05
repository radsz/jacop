package org.jacop.jasat.utils;

/**
 * a factory for type E
 *
 * @param E the type to produce
 * @author simon
 */
public interface Factory<E> {

    /**
     * method to call to get a new instance of the type E
     *
     * @return a new instance of E
     */
    E newInstance();


}
