package edu.osu.cse.pa.spg;


import soot.Scene;
import soot.Type;

public class ClassConstNode extends AbstractAllocNode {
    public static ClassConstNode node = new ClassConstNode();
	ClassConstNode() {
		super(null);
	}

	public Type getType() {
		return Scene.v().getRefType("java.lang.Class");
	}

	public String toString() {
		return "class constant ";
	}

}
