package qwirkle.tile;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Random;

/**
 * Created by martijn on 18-12-15.
 */
public enum Shape {
    CIRCLE('o'), DIAMOND('d'), SQUARE('s'), CLOVER('c'), STAR('*'), NINJASTAR('x'), NONE('-'); //TODO discuss types of enum during protocol meeting

    public static final List<Shape> shapeList = Collections.unmodifiableList(Arrays.asList(values()));

    private char id;

    /**
     * Sets the identifier for a Shape
     *
     * @param identifier Char identifier of the Shape.
     */
    Shape(char identifier) {
        id = identifier;
    }

    @Deprecated //Only used for testing
    public static Shape getRandomShape() {
        Random rand = new Random();
        return shapeList.get(rand.nextInt(shapeList.size()));
    }

    /**
     * Returns all shapes, except Shape.None
     *
     * @return Shape[] of all possible Shapes.
     */
    public static Shape[] getShapes() {
        return new Shape[]{Shape.CIRCLE, Shape.DIAMOND, Shape.SQUARE, Shape.CLOVER, Shape.STAR, Shape.NINJASTAR};
    }

    /**
     * Returns the Char that belongs to the current Shape object
     *
     * @return Char identifier
     */
    public char getChar() { //TODO discuss types of enum during protocol meeting
        return id;
    }

    @Override
    public String toString() {
        return "" + id;
    }
}
