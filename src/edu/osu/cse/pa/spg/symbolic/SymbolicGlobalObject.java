package edu.osu.cse.pa.spg.symbolic;

import edu.osu.cse.pa.spg.GlobalVarNode;
import soot.SootField;
import soot.SootMethod;


public class SymbolicGlobalObject extends SymbolicObject {
	private GlobalVarNode var;

	public SymbolicGlobalObject(SootMethod m, GlobalVarNode var) {
		super(var.getType(), m);
		this.var = var;
	}

	public SootField getField() {
		return var.getFieldRef();
	}


	public GlobalVarNode getGlobalVarNode(){
		return var;
	}


	public String toString() {
		return "SG@" + Integer.toHexString(hashCode()) + " for " + method.getSignature();
	}
}
