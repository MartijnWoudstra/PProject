package qwirkle.player.local;

import qwirkle.Board;
import qwirkle.Game;
import qwirkle.tile.Tile;

/**
 * Created by Martijn on 18-Dec-15.
 */
public class HumanPlayer extends LocalPlayer {

    /**
     * Creates a HumanPlayer.
     *
     * @param playerName String name of the player. Used in GUI/TUI
     */
    public HumanPlayer(String playerName) {
        hand = new Tile[Game.MAX_HAND_SIZE];
        name = playerName;
    }

    @Override
    public void determineMove(Board board) {
        //TODO implement
    }
}
