import org.junit.Before;
import org.junit.Test;
import qwirkle.Board;

import static junit.framework.TestCase.assertEquals;

/**
 * Created by Martijn on 18-Dec-15.
 */
public class BoardSetupTest {

    Board board;
    public int STACKSIZE_INITIAL = 108;

    @Before
    public void setup(){
        board = new Board();
    }

    @Test
    public void stackTest(){
        assertEquals(STACKSIZE_INITIAL, board.getStackSize());
    }
}
