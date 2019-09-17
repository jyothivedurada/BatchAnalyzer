package edu.osu.cse.pa.spg.symbolic;

import soot.SootMethod;
import soot.jimple.IdentityRef;

public class SymbolicParamObject extends SymbolicObject {

	private IdentityRef ref;

	public SymbolicParamObject(SootMethod m, IdentityRef ref) {
		super(ref.getType(), m);
		this.ref = ref;
	}

	public IdentityRef getIdentityRef() {
		return ref;
	}


	public String toString() {
		return "SP@" + Integer.toHexString(hashCode()) + " for " + method.getSignature();
	}
}
