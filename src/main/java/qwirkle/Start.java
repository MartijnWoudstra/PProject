package qwirkle;

import qwirkle.player.HumanPlayer;
import qwirkle.player.Player;

/**
 * Created by martijn on 21-12-15.
 */
public class Start{

	public static void main(String[] args){
		Game g = new Game(args);
		g.start();
	}
}
