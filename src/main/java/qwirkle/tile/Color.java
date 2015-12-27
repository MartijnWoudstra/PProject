package qwirkle.tile;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Random;

/**
 * Created by martijn on 18-12-15.
 */
public enum Color{
	RED('r'), ORANGE('o'), BLUE('b'), PURPLE('p'), YELLOW('y'), GREEN('g'), NONE('-'); //TODO discuss types of enum during protocol meeting

	public static final List<Color> colorList = Collections.unmodifiableList(Arrays.asList(values()));

	private char id;

	Color(char identifier){
		id = identifier;
	}

	public char getCharFromTile(){ //TODO discuss types of enum during protocol meeting
		return id;
	}

	@Deprecated //Only used for testing
	public static Color getRandomColor(){
		Random random = new Random();
		return colorList.get(random.nextInt(colorList.size()));
	}

	/**
	 * Returns all colors, except Color.NONE
	 *
	 * @return Color[] of all possible Colors.
	 */
	public static Color[] getColors(){
		return new Color[]{Color.RED, Color.ORANGE, Color.BLUE, Color.PURPLE, Color.YELLOW, Color.GREEN};
	}

	@Override
	public String toString(){
		return "" + id;
	}
}
