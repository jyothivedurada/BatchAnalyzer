package edu.osu.cse.pa.spg.symbolic;

import edu.osu.cse.pa.spg.ExceptionVarNode;
import soot.SootMethod;


public class SymbolicExceptionObject extends SymbolicObject {

	public SymbolicExceptionObject(SootMethod m) {
		super(ExceptionVarNode.node.getType(), m);
	}
	

	public String toString() {
		return "SE@" + Integer.toHexString(hashCode());
	}
}
