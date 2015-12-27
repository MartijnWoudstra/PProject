package qwirkle.annotation;

public @interface Unfinished{
	public enum Priority{LOW, MEDIUM, HIGH}

	String value();

	Priority priority() default Priority.MEDIUM;

	String createdBy() default "Martijn Woudstra";
}