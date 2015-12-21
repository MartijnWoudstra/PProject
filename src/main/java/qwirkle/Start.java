package qwirkle;

import qwirkle.player.HumanPlayer;
import qwirkle.player.Player;

/**
 * Created by martijn on 21-12-15.
 */
public class Start{

	public static void main(String[] args){
		Player[] players = new Player[args.length];
		for(int i = 0; i < args.length; i++)
			players[i] = new HumanPlayer(args[i]);
		Game g = new Game(players);
		g.start();
	}
}
