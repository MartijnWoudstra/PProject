package qwirkle.move;

import qwirkle.Board;
import qwirkle.Game;
import qwirkle.tile.Tile;

/**
 * Created by Martijn on 18-Dec-15.
 */
public class PlaceMove implements Move{

	private Board board;
	private Tile[] tiles;
	private int[] rows;
	private int[] colums;

	/**
	 * Creates a PlaceMove object.
	 * @param b
	 * 		Board where the game is played on.
     */
	private PlaceMove(Board b){
		board = b;
		tiles = new Tile[Game.MAX_HAND_SIZE];
		rows = new int[Game.MAX_HAND_SIZE];
		colums = new int[Game.MAX_HAND_SIZE];
	}

	/**
	 * A PlaceMove can consist of more than one tile to place.
	 * This method adds every move to the PlaceMove
	 * @param tile
	 * 		Tile to place
	 * @param row
	 * 		Int row to place tile
	 * @param col
	 * 		Int column to place tile
     * @return Boolean true if success, otherwise false.
     */
	public boolean addPlaceMove(Tile tile, int row, int col){
		if(row <= Game.BOARD_ROWS && col <= Game.BOARD_COLUMS && tile != null)
			if(tiles.length == colums.length && colums.length == rows.length){
				int i = tiles.length;
				tiles[i] = tile;
				rows[i] = row;
				colums[i] = col;
				return true;
			}
		return false;
	}

	@Override
	public boolean confirm(){
		Board b = board.deepCopy();
		for(int i = 0; i < tiles.length; i++)
			if(!b.placeTile(tiles[i], rows[i], colums[i]))
				return false;
		for(int i = 0; i < tiles.length; i++)
			board.placeTile(tiles[i], rows[i], colums[i]);
		return true;
	}

	@Override
	public void removeMove(){
		tiles = new Tile[Game.MAX_HAND_SIZE];
		rows = new int[Game.MAX_HAND_SIZE];
		colums = new int[Game.MAX_HAND_SIZE];
	}
}
