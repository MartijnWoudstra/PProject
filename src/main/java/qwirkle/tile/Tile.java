package qwirkle.tile;

/**
 * Created by martijn on 18-12-15.
 */
public class Tile{

	private Color color;
	private Shape shape;

	public Tile(Color arg0, Shape arg1){
		this.color = arg0;
		this.shape = arg1;
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
