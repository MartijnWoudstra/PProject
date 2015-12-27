package qwirkle.player.local;

import qwirkle.Board;
import qwirkle.Game;
import qwirkle.tile.Tile;

/**
 * Created by Martijn on 18-Dec-15.
 */
public class HumanPlayer extends LocalPlayer{

	private Tile[] hand;
	private String name;

	public HumanPlayer(String playerName){
		hand = new Tile[Game.MAX_HAND_SIZE];
		name = playerName;
	}

	@Override
	public void determineMove(Board board){
		//TODO implement
	}
}
