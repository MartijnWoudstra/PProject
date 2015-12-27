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

	private PlaceMove(Board b){
		board = b;
		tiles = new Tile[Game.MAX_HAND_SIZE];
		rows = new int[Game.MAX_HAND_SIZE];
		colums = new int[Game.MAX_HAND_SIZE];
	}

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
		for(int i = 0; i < tiles.length; i++){
			if(!b.placeTile(tiles[i], rows[i], colums[i])) //TODO on dummy board.
				return false;
		}
		for(int i = 0; i < tiles.length; i++){
			board.placeTile(tiles[i], rows[i], colums[i]);
		}
		return true;
	}

	@Override
	public void removeMove(){
		tiles = new Tile[Game.MAX_HAND_SIZE];
		rows = new int[Game.MAX_HAND_SIZE];
		colums = new int[Game.MAX_HAND_SIZE];
	}
}
