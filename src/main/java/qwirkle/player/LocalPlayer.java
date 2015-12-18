package main.java.qwirkle.player;

import main.java.qwirkle.Board;

/**
 * Created by Martijn on 18-Dec-15.
 */
public abstract class LocalPlayer extends Player {

    /**
     * Determines the move of a player.
     * For HumanPlayer it is based on input.
     * For ComputerPlayers it is based on an algorithm.
     * @param board Board object.
     */
    public abstract void determineMove(Board board);//TODO return type
}
