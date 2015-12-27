package qwirkle.player.local;

import qwirkle.Board;
import qwirkle.tile.Tile;

/**
 * Created by Martijn on 18-Dec-15.
 */
public class ComputerPlayer extends LocalPlayer{

	private String name;
	private Tile[] hand;

	public ComputerPlayer(String playerName){
		this.hand = super.hand;
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
