package qwirkle;

import qwirkle.annotation.Unfinished;
import qwirkle.player.HumanPlayer;
import qwirkle.player.Player;

import java.util.Scanner;

/**
 * Created by martijn on 18-12-15.
 */

//TODO JML
public class Game{

	public static final int MAX_HAND_SIZE = 6;
	public static final int BOARD_ROWS = 5; //TODO Discuss during protocol meeting
	public static final int BOARD_COLUMS = BOARD_ROWS;
	public static final int MIDDLE_TILE = Board.index(BOARD_COLUMS / 2, BOARD_ROWS / 2);
	public static final int MAX_PLAYERS = 8;
	private Board board;

	// @ private invariant players.length() <= Game.MAX_PLAYERS;
	private Player[] players;

	// @ private invariant 0 <= current  && current < NUMBER_PLAYERS;
	private int current;

	// @ requires playerArray != null && 0 < playerArray.length();
	public Game(String[] args){
		players = extractPlayers(args);
		current = 0;
		board = new Board();
		start();
	}


	@Unfinished(value = "To extract the players from args[]. This is discussed during Protocol meeting. Also order is discussed.", priority = Unfinished.Priority.LOW)
	private Player[] extractPlayers(String[] args){
		Player[] playerList = new Player[args.length];
		for(int i = 0; i < args.length; i++)
			//TODO check args for number of players (MAX_PLAYERS)
			playerList[i] = new HumanPlayer(args[i]);
		return playerList;
	}

	/**
	 * This is the main loop for the game.
	 * Only if the user types ´n´ the game will terminate.
	 */
	public void start(){
		boolean hasEnded = false;
		while(!hasEnded){
			reset();
			play();
			hasEnded = promtRestart("\n> Play another time? (y/n)?", "y", "n");
		}
	}

	/**
	 * Prompts if the game needs to be restarted
	 *
	 * @param prompt
	 * 		String message to print
	 * @param yes
	 * 		String the user needs to type to answer yes
	 * @param no
	 * 		String the user needs to type to answer no
	 * @return boolean true if user types yes, false if user types no
	 */
	//@ requires promt != null && yes != null && no != null;
	private boolean promtRestart(String prompt, String yes, String no){
		String answer;
		do{
			System.out.print(prompt);
			try(Scanner scanner = new Scanner(System.in)){
				answer = scanner.hasNextLine() ? scanner.nextLine() : null;
			}
		}while(answer == null || (!answer.equals(yes) && !answer.equals(no)));
		return answer.equals(yes);
	}

	/**
	 * Resets the game.
	 * Sets the current player to 0, and resets the board.
	 */
	// @ ensures current = 0;
	private void reset(){
		current = 0;
		board.reset();
	}

	/**
	 * Loop for what a player can do in his turn.
	 * Sub loop for the game.
	 */
	@Unfinished(value = "Playloop is not defined yet.", priority = Unfinished.Priority.LOW)
	private void play(){
		//TODO
	}

	/**
	 * Sets the current current value to the next value.
	 * Goes back to the first player index if all players have had their turn.
	 */
	// @ ensures current = (\old(current) + 1) % (players.length);
	public void nextPlayer(){
		current = (current + 1) % (players.length);
	}

	/**
	 * Gets the current player
	 *
	 * @return Player current player.
	 */
	// @ pure
	public Player getCurrentPlayer(){
		return players[current];
	}

	/**
	 * Gets the current player as index of the players array.
	 *
	 * @return Int index of player in player array.
	 */
	// ensures current < players.length();
	// @ pure
	public int getCurrentPlayerAsInt(){
		return current;
	}
}
