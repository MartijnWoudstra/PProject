package qwirkle.player;

import qwirkle.Board;
import qwirkle.Game;
import qwirkle.tile.Tile;

/**
 * Created by Martijn on 18-Dec-15.
 */
public class ComputerPlayer extends LocalPlayer{

	private String name;

	public ComputerPlayer(String playerName){
		hand = new Tile[Game.MAX_HAND_SIZE]; //TODO oncreate new hand.
		name = playerName;
	}

	@Override
	public void determineMove(Board board){

	}

	@Override
	public boolean isHandEmpty(){
		return false;
	}
}
