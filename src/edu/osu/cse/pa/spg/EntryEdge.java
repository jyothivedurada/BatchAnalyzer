package edu.osu.cse.pa.spg;

import edu.osu.cse.pa.dsmodels.Util;
import soot.jimple.toolkits.callgraph.Edge;

public class EntryEdge extends AbstractSPGEdge {	
	private Edge e;
	
	private int id;
	
	private int virtualID;

	public EntryEdge(AbstractAllocNode src, AbstractAllocNode tgt, Edge e, Integer virtualId) {
		super(src, tgt);
		this.e = e;
		this.id = Util.ctxId++;
		this.virtualID = virtualId;
	}

	public Edge getCallGraphEdge() {
		return e;
	}
	
	public int getId() {
		return id;
	}
	
	public int getReverseId() {
		return id + Util.ctxId;
	}

	public int getVirtualID() {
		return virtualID;
	}

	/*public void setVirtualID(int virtualID) {
		this.virtualID = virtualID;
	}*/
}
