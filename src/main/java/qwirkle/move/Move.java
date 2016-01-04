package qwirkle.move;

/**
 * Created by Martijn on 18-Dec-15.
 */
public interface Move {

    /**
     * Confirms that the move is complete, and sends it to the server.
     *
     * @return Boolean if move has been accepted and executed.
     */
    boolean confirm();

    /**
     * Removes all moves from the current object, to start again.
     */
    void removeMove();
}
