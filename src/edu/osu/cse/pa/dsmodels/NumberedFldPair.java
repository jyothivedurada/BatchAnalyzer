package edu.osu.cse.pa.dsmodels;

import edu.osu.cse.pa.spg.AbstractSPGEdge;

public class NumberedFldPair extends FldPair {
	
	private int ctxHash;
	
	public NumberedFldPair(AbstractSPGEdge edge, boolean isBar, int ctxHash) {
		super(edge, isBar);
		this.ctxHash = ctxHash;
	}
	
	public int getCtxHash() {
		return ctxHash;
	}
}
