package main.java.qwirkle.tile;

/**
 * Created by martijn on 18-12-15.
 */
public class Tile {

    private Color color;
    private Shape shape;

    public Tile(Color arg0, Shape arg1) {
        this.color = arg0;
        this.shape = arg1;
    }

    public Color getColor() {
        return color;
    }

    public Shape getShape() {
        return shape;
    }

    @Override
    public String toString() {
        return "Tile has color " + color + " and shape " + shape;
    }
}
