package qwirkle;

import qwirkle.annotation.Unfinished;
import qwirkle.exception.EmptyTileStackException;
import qwirkle.tile.Color;
import qwirkle.tile.Shape;
import qwirkle.tile.Tile;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Random;

/**
 * Created by martijn on 18-12-15.
 */
public class Board{

	public static final Tile NONE_TILE = new Tile(Color.NONE, Shape.NONE);
	// @ private invariant 0 <= stack.size() < 3 * Color.values() * Shape.values();
	private List<Tile> stack;

	// @ private invariant matrix.length() == Game.BOARD_COLUMS;
	// @ private invariant (\forall int i; 0 <= i < Game.BOARD_COLUMS; matrix[i].length() == Game.BOARD_ROWS)
	private Tile[][] matrix;

	// @ ensures {
	// matrix.length() == Game.BOARD_COLUMS;
	// (\forall int i; 0 <= i < Game.BOARD_COLUMS; matrix[i].length() == Game.BOARD_ROWS
	// }

	/**
	 * Creates the board object.
	 * Also creates a stack, and a matrix.
	 * Calles reset();
	 */
	public Board(){
		stack = new ArrayList<Tile>();
		matrix = new Tile[Game.BOARD_COLUMS][Game.BOARD_ROWS]; //TODO Discuss during protocol meeting
		reset();
	}

	/**
	 * Method for setting up a new board.
	 * Called by the constructor.
	 */
	public void reset(){
		fillStack();
		setEmptyMatrix();
	}

	/**
	 * Sets the matrix to an empty matrix.
	 * Used when board is reset.
	 */
	/* @ ensures \forall(
	 	int i; 0 <= i < BOARD_COLUMS - 1 {
	 		\forall(
	 		int j; 0 <= j < BOARD_COLUMS - 1;
	 		matrix[i][j] == Tile.getEmptyTile();
	 	}
	*/
	private void setEmptyMatrix(){
		for(int i = 0; i < Game.BOARD_COLUMS - 1; i++)
			for(int j = 0; j < Game.BOARD_COLUMS - 1; j++)
				matrix[i][j] = NONE_TILE;

	}

	/**
	 * Fills the game stack with tiles.
	 * All possible combinations of colors and shapes are added 3 times.
	 * The stack is then shuffeled, to make sure the order is random.
	 */
	//@ ensures \forall(int i; 0 < i < 3 * Color.getColors().length() * Shape.getShapes().length(); stack[i] != null);
	private void fillStack(){
		for(int i = 0; i < 3; i++)
			for(Color c : Color.getColors())
				for(Shape s : Shape.getShapes())
					stack.add(new Tile(c, s));
		shuffleStack();
	}

	/**
	 * Shuffles the stack.
	 * Used when a player switches, or the stack is created.
	 */
	//@ ensures \old(stack.size()) == stack.size());
	private void shuffleStack(){
		long seed = System.nanoTime();
		Collections.shuffle(stack, new Random(seed));
	}

	/**
	 * Converts a row and colum to an index
	 * NOTE: First row and col are int 0
	 *
	 * @param row
	 * 		Int row
	 * @param col
	 * 		Int colum
	 * @return Int index of the row and colum
	 */
	//@ ensures \result == (col * Game.BOARD_ROWS + row);
	//@ requires row < Game.BOARD_ROWS && col < Game.BOARD_COLUMS;
	//@ pure
	public static int index(int row, int col){
		return (row * Game.BOARD_COLUMS + col);
	}

	/**
	 * Converts an index to a row and colum
	 * These values are stored in an int[].
	 * int[0] = row;
	 * int[1] = column;
	 *
	 * @param index
	 * 		Int index
	 * @return Int[] corresponding col and row to the index
	 */
	// @ ensures \result[0] == index % Game.BOARD_ROWS
	//      && \result[1] == index / Game.BOARD_ROWS;
	// @ requires index < (Game.BOARD_ROWS - 1) * (Game.BOARD_COLUMS - 1)
	// @ pure
	public static int[] indexToRowCol(int index){
		int[] ans = new int[2];
		ans[0] = index / Game.BOARD_ROWS;
		ans[1] = index % Game.BOARD_ROWS;
		return ans;
	}

	/**
	 * Switches a Tile of a LocalPlayer with the stack
	 * First the Tile is drawn from the shuffeled stack.
	 * After that the Tile of the LocalPlayer is added to the stack.
	 * Finally the stack is shuffeled.
	 *
	 * @param tile
	 * 		Tile of the LocalPlayer that he wants to switch
	 * @return Tile the tile that the LocalPlayer will receive.
	 */
	//TODO JML
	public Tile switchTile(Tile tile) throws EmptyTileStackException{ //TODO check current
		if(stack.size() == 0)
			throw new EmptyTileStackException();
		else {
			Tile result = stack.get(0);
			stack.add(tile);
			shuffleStack();
			return result;
		}
	}

	/**
	 * Converts index into a row and column, and then  calles placeTile(Tile tile, int row, int col)
	 *
	 * @param tile
	 * 		Tile to place at the index.
	 * @param index
	 * 		Int index on the board.
	 * @return Boolean true if placed tile on index, otherwise false.
	 */
	public boolean placeTile(Tile tile, int index){
		int[] a = indexToRowCol(index);
		return placeTile(tile, a[0], a[1]);
	}

	/**
	 * Checks if matrix[row][col] is empty, and if the move is valid.
	 * If conditions are met, calles setField(tile, row, col).
	 *
	 * @param tile
	 * 		Tile tile to place at matrix[row][col]
	 * @param row
	 * 		Int row to place tile
	 * @param col
	 * 		Int column to place tile.
	 * @return Boolean true if tile has been placed, otherwise false.
	 */
	public boolean placeTile(Tile tile, int row, int col){
		if(getField(row, col).equals(NONE_TILE) && isValidMove(tile, row, col))
			return false;
		setField(tile, row, col);
		return true;
	}

	/**
	 * Converts index into a row and column, and then  calles setField(Tile tile, int row, int col)
	 *
	 * @param tile
	 * 		Tile tile to place at index
	 * @param index
	 * 		Int index where to place tile
	 */
	private void setField(Tile tile, int index){
		int[] a = indexToRowCol(index);
		setField(tile, a[0], a[1]);
	}

	/**
	 * Sets the field to tile
	 *
	 * @param tile
	 * 		Tile tile to place
	 * @param row
	 * 		Int row to place tile
	 * @param col
	 * 		Int column to place tile.
	 */
	// @ requires isValidMove(tile, row, col);
	private void setField(Tile tile, int row, int col){
		matrix[row][col] = tile;
	}

	//TODO
	@Unfinished(value = "This method is not done yet, since much play features still have to be implemented")
	private boolean isValidMove(Tile tile, int row, int col){
		return false;
	}

	/**
	 * Gets the size of the stack of the board.
	 *
	 * @return Int amount of tiles in stack.
	 */
	//@ pure
	public int getStackSize(){
		return stack.size();
	}

	/**
	 * Returns the Tile on a field
	 * @param row
	 *		Int row
	 * @param col
	 *		Int column
	 * @return Tile on the selected field.
	 */
	public Tile getField(int row, int col){
		return matrix[row][col];
	}

	/**
	 * Deep copies the board.
	 * Usefull for simulation
	 * @return Board board object same as this one, except for the stack.
	 */
	public Board deepCopy(){
		Board b = new Board();
		for(int i = 0; i < Game.BOARD_COLUMS; i++)
			for(int j = 0; j < Game.BOARD_ROWS; j++)
				b.setField(getField(i, j), i, j);
		return b;
	}
}