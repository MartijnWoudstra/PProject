package main.java.qwirkle;

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

    public static final int BOARD_ROWS = 10; //TODO Discuss during protocol meeting
    public static final int BOARD_COLUMS = 10; //TODO Discuss during protocol meeting

    private List<Tile> stack;
    private Tile[][] matrix;

    public Board() {
        stack = new ArrayList<>();
        matrix = new Tile[BOARD_ROWS][BOARD_COLUMS]; //TODO Discuss during protocol meeting
        fillStack();
    }

    /**
     * Fills the game stack with tiles.
     * All possible combinations of colors and shapes are added 3 times.
     * The stack is then shuffeled, to make sure the order is random.
     */
    private void fillStack(){
        for(int i = 0; i < 3; i++) {
            for(Color c : Color.values())
                for(Shape s : Shape.values()){
                    stack.add(new Tile(c, s));
                    System.out.println(stack.get(stack.size() - 1));
                }
        }
        long seed = System.nanoTime();
        Collections.shuffle(stack, new Random(seed));
    }
}