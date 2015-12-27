package qwirkle.player.local;

import qwirkle.Board;
import qwirkle.player.Player;
import qwirkle.tile.Tile;

/**
 * Created by Martijn on 18-Dec-15.
 */
public abstract class LocalPlayer extends Player{

	protected Tile[] hand; //TODO can other player get this now?

	/**
	 * Determines the move of a player.
	 * For HumanPlayer it is based on input.
	 * For ComputerPlayers it is based on an algorithm.
	 *
	 * @param board
	 * 		Board object.
	 */
	public abstract void determineMove(Board board);//TODO return type

	/**
	 * Checks if a players hand is empty.
	 * Does this by checking if the Tile[] hand has size 0
	 *
	 * @return Boolean true if hand is empty, otherwise false
	 */
	//@ ensures \result == (hand.length() == 0);
	public boolean isHandEmpty(){
		return hand.length == 0;
	}
}
