package main.java.qwirkle;

/**
 * Created by martijn on 18-12-15.
 */
public class Game {

    public static final int MAX_HAND_SIZE = 6;
    public static final int BOARD_ROWS = 11; //TODO Discuss during protocol meeting
    public static final int BOARD_COLUMS = 11; //TODO Discuss during protocol meeting
    public static final int MIDDLE_TILE = Board.index(BOARD_COLUMS / 2, BOARD_ROWS / 2);

    public static void main(String[] args) {
        Board b = new Board();
    }
}
