package edu.osu.cse.pa.spg.symbolic;

import soot.SootField;
import soot.SootMethod;

public class SymbolicInstanceFieldObject extends SymbolicObject {

	private SootField field;

	public SymbolicInstanceFieldObject(SootMethod m, SootField field) {
		super(field.getType(), m);
		this.field = field;

	}

	public SootField getField() {
		return field;
	}


	public String toString() {
		return "SIF@" + Integer.toHexString(hashCode()) + " for " + method.getSignature();
	}
}
