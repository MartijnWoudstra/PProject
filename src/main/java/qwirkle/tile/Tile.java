package qwirkle.tile;

/**
 * Created by martijn on 18-12-15.
 */
public class Tile{

	private Color color;
	private Shape shape;

	/**
	 * Creates a tile object
	 * @param c
	 * 		Color object which the tile should have
	 * @param s
	 * 		Shape object which the tile should have
     */
	public Tile(Color c, Shape s){
		this.color = c;
		this.shape = s;
	}

	/**
	 * Returns the Color of of the Tile
	 *
	 * @return Color color object
	 */
	//@pure
	public Color getColor(){
		return color;
	}

	/**
	 * Returns the Shape of the Tile
	 *
	 * @return Shape shape object
	 */
	//@pure
	public Shape getShape(){
		return shape;
	}

	@Override
	public String toString(){
		return "Tile has color " + color + " and shape " + shape;
	}
}
