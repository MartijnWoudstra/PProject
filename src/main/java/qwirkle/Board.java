package main.java.qwirkle;

import main.java.qwirkle.tile.Color;
import main.java.qwirkle.tile.Shape;
import main.java.qwirkle.tile.Tile;

import java.util.ArrayList;
import java.util.List;

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
        matrix = new Tile[BOARD_ROWS][BOARD_COLUMS];
        fillStack();
    }

    private void fillStack(){
        for(int i = 0; i < 3; i++) {
            for(Color c : Color.values())
                for(Shape s : Shape.values())
                    stack.add(new Tile(c, s));
        }
        System.out.println(stack.size());
    }
}
