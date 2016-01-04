package qwirkle.player.local;

import qwirkle.Board;
import qwirkle.Game;
import qwirkle.tile.Tile;

/**
 * Created by Martijn on 18-Dec-15.
 */
public class ComputerPlayer extends LocalPlayer{

	/**
	 * Creates a ComputerPlayer object.
	 * @param playerName
	 * 		String name of the player. Used in GUI/TUI
     */
	public ComputerPlayer(String playerName){
		hand = new Tile[Game.MAX_HAND_SIZE];
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
