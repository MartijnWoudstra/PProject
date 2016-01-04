import org.junit.Before;
import org.junit.Test;
import qwirkle.Board;
import qwirkle.player.local.HumanPlayer;
import qwirkle.player.Player;

import static junit.framework.TestCase.assertEquals;

/**
 * Created by Martijn on 18-Dec-15.
 */
public class BoardSetupTest{

	public Board board;
	public Player player;
	public Player[] players;
	public static final String HUMAN_PLAYER_NAME = "myName";
	public static  final int STACKSIZE_INITIAL = 108;

	@Before
	public void setup(){
		players = new Player[1];
		players[0] = new HumanPlayer(HUMAN_PLAYER_NAME);
		player = players[0];
		board = new Board();
	}

	@Test
	public void stackTest(){
		assertEquals(STACKSIZE_INITIAL, board.getStackSize());
	}

	@Test
	public void nameTest(){
		assertEquals(player.name, HUMAN_PLAYER_NAME);
	}
}
