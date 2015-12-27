package qwirkle.tile;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Random;

/**
 * Created by martijn on 18-12-15.
 */
public enum Shape{
	CIRCLE('o'), DIAMOND('d'), SQUARE('s'), CLOVER('c'), STAR('*'), NINJASTAR('x'), NONE('-'); //TODO discuss types of enum during protocol meeting

	public static final List<Shape> shapeList = Collections.unmodifiableList(Arrays.asList(values()));

	private char id;

	Shape(char identifier){
		id = identifier;
	}

	public char getCharFromTile(){ //TODO discuss types of enum during protocol meeting
		return id;
	}

	@Deprecated //Only used for testing
	public static Shape getRandomShape(){
		Random rand = new Random();
		return shapeList.get(rand.nextInt(shapeList.size()));
	}

	/**
	 * Returns all shapes, except Shape.None
	 *
	 * @return Shape[] of all possible Shapes.
	 */
	public static Shape[] getShapes(){
		return new Shape[]{Shape.CIRCLE, Shape.DIAMOND, Shape.SQUARE, Shape.CLOVER, Shape.STAR, Shape.NINJASTAR};
	}

	@Override
	public String toString(){
		return "" + id;
	}
}
