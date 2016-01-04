package qwirkle.move;

import qwirkle.Board;
import qwirkle.Game;
import qwirkle.exception.EmptyTileStackException;
import qwirkle.tile.Tile;

/**
 * Created by Martijn on 18-Dec-15.
 */
public class SwitchMove implements Move {

    private Board board;
    private Tile[] tiles;

    public SwitchMove(Board b) {
        board = b;
        tiles = new Tile[Game.MAX_HAND_SIZE];
    }

    public boolean addSwitchMove(Tile tile) {
        tiles[tiles.length - 1] = tile;
        return true;
    }

    @Override
    public boolean confirm() {
        Tile[] tilesCopy = tiles;
        Board b = board.deepCopy();
        for (int i = 0; i < tiles.length; i++) {
            try {
                tilesCopy[i] = b.switchTile(tiles[i]);
            } catch (EmptyTileStackException e) {
                return false;
            }
        }
        for (int i = 0; i < tiles.length; i++) {
            try {
                tiles[i] = b.switchTile(tiles[i]);
            } catch (EmptyTileStackException e) {
                //Not Reachable
            }
        }
        return true; //TODO give new tiles.
    }

    @Override
    public void removeMove() {
        tiles = new Tile[Game.MAX_HAND_SIZE];
    }
}
