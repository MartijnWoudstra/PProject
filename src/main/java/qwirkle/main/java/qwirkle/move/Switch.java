package main.java.qwirkle.main.java.qwirkle.move;

import main.java.qwirkle.Board;
import main.java.qwirkle.exception.EmptyTileStackException;
import main.java.qwirkle.tile.Tile;

/**
 * Created by Martijn on 18-Dec-15.
 */
public class Switch extends Move {

    /**
     * Makes a switch move.
     * Each Tile in the Tile Array is swapped individually.
     * Catches EmptyTileStackException if the Board Stack is empty.
     * @param tiles Tile[] of Tiles that the player wants to swap.
     * @param board Board object
     * @return Tile[] the new Tiles
     */
    public Tile[] makeSwitchMove(Tile[] tiles, Board board) {
        Tile[] swappedTiles = new Tile[tiles.length];
        for (int i = 0; i < tiles.length; i++) {
            try {
                swappedTiles[i] = board.switchTile(tiles[i]);
            } catch (EmptyTileStackException e) {
                e.printStackTrace(); //TODO Add implementation later
            }
        }
        return swappedTiles;
    }
}
