package qwirkle.annotation;

//Test
public @interface Unfinished{
	String value();

	Priority priority() default Priority.MEDIUM;

	String createdBy() default "Martijn Woudstra";

	public enum Priority{LOW, MEDIUM, HIGH}
}