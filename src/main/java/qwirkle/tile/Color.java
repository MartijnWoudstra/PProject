package main.java.qwirkle.tile;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Random;

/**
 * Created by martijn on 18-12-15.
 */
public enum Color {
    RED('r'), ORANGE('o'), BLUE('b'), PURPLE('p'), YELLOW('y'), GREEN('g'); //TODO discuss types of enum during protocol meeting

    public static final List<Color> colorList = Collections.unmodifiableList(Arrays.asList(values()));

    private char id;

    Color (char identifier){
        id = identifier;
    }

    public char getCharFromTile(){
        return id;
    }

    public static char getCharFromEnum(Color color){
        switch (color){
            case RED: return RED.id;
            case ORANGE: return ORANGE.id;
            case BLUE: return BLUE.id;
            case PURPLE: return PURPLE.id;
            case YELLOW: return YELLOW.id;
            case GREEN: return GREEN.id;
            default: return '-';
        }
    }

    public static Color getRandomColor(){
        Random random = new Random();
        return colorList.get(random.nextInt(colorList.size()));
    }

    @Override
    public String toString() {
        return "" + id;
    }
}
