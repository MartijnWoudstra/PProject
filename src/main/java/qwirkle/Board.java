package main.java.qwirkle;

import main.java.qwirkle.exception.EmptyTileStackException;
import main.java.qwirkle.tile.Color;
import main.java.qwirkle.tile.Shape;
import main.java.qwirkle.tile.Tile;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;

/**
 * Created by martijn on 18-12-15.
 */
public class Board {

    private List<Tile> stack;
    private Tile[][] matrix;

    public Board() {
        stack = new ArrayList<>();
        matrix = new Tile[Game.BOARD_COLUMS][Game.BOARD_ROWS]; //TODO Discuss during protocol meeting
        fillStack();
    }

    /**
     * Fills the game stack with tiles.
     * All possible combinations of colors and shapes are added 3 times.
     * The stack is then shuffeled, to make sure the order is random.
     */
    //@ ensures stack.size() == 3 * Color.values() * Shape.values();
    private void fillStack() {
        for (int i = 0; i < 3; i++) {
            for (Color c : Color.values())
                for (Shape s : Shape.values()) {
                    stack.add(new Tile(c, s));
                    System.out.println(stack.get(stack.size() - 1));
                }
        }
        shuffleStack();
    }

    /**
     * Shuffles the stack.
     * Used when a player switches, or the stack is created.
     */
    //@ ensures \old(stack.size()) == stack.size();
    private void shuffleStack() {
        long seed = System.nanoTime();
        Collections.shuffle(stack, new Random(seed));
    }

    /**
     * Switches a Tile of a LocalPlayer with the stack
     * First the Tile is drawn from the shuffeled stack.
     * After that the Tile of the LocalPlayer is added to the stack.
     * Finally the stack is shuffeled.
     *
     * @param tile Tile of the LocalPlayer that he wants to switch
     * @return Tile the tile that the LocalPlayer will receive.
     */
    public Tile switchTile(Tile tile) throws EmptyTileStackException {
        if (stack.size() == 0)
            throw new EmptyTileStackException();
        else {
            Tile result = stack.get(0);
            stack.add(tile);
            shuffleStack();
            return result;
        }
    }

    /**
     * Converts a row and colum to an index
     * @param row Int row
     * @param col Int colum
     * @return Int index of the row and colum
     */
    //@ ensures \result == (col * Game.BOARD_ROWS - 1) - Game.BOARD_COLUMS - col;
    public static int index(int row, int col){
        return (col * Game.BOARD_ROWS - 1) - Game.BOARD_COLUMS - col;
    }

    /**
     * Converts an index to a row and colum
     * These values are stored in an int[].
     * int[0] = row;
     * int[1] = column;
     * @param index Int index
     * @return Int[] corresponding col and row to the index
     */
    //@ensures \result[0] == (index / Game.BOARD_COLUMS) + 1
    //      && \result[1] == index - (\result[0] - 1) * (Game.BOARD_COLUMS);
    public static int[] indexToRowCol (int index){
        int colIndexInArray = 0;
        int rowIndexInArray = 1;
        int [] ans = new int[2]; //{col, row}
        ans[colIndexInArray]= (index / Game.BOARD_COLUMS) + 1;
        int remainder = index - (ans[colIndexInArray] - 1) * (Game.BOARD_COLUMS);
        ans[rowIndexInArray] = remainder + 1;
        return ans;
    }

    public int getStackSize(){
        return stack.size();
    }
}