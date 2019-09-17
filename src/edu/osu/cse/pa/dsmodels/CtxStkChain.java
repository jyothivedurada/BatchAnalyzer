package edu.osu.cse.pa.dsmodels;

import java.util.LinkedList;

import edu.osu.cse.pa.spg.FieldPTEdge;
import soot.jimple.toolkits.callgraph.Edge;

/**
 * @author Jyothi Vedurada
 * @since Jun 25, 2019
 */
public class CtxStkChain {
	private LinkedList<Edge> current;
	private CtxStkChain previous;
	private boolean oldStkLinkLost = false;
	
	public CtxStkChain(){
		
	}
	
	public CtxStkChain(LinkedList<Edge> current, CtxStkChain previous){
		this.current = current;
		this.previous = previous;
	}
	
	public CtxStkChain(LinkedList<Edge> current, CtxStkChain previous, boolean oldStkLinkLost){
		this.current = current;
		this.previous = previous;
		this.oldStkLinkLost = oldStkLinkLost;
	}
	
	public LinkedList<Edge> getCurrent() {
		return current;
	}
	public void setCurrent(LinkedList<Edge> current) {
		this.current = current;
	}
	public CtxStkChain getPrevious() {
		return previous;
	}
	public void setPrevious(CtxStkChain previous) {
		this.previous = previous;
	}

	public boolean isOldStkLinkLost() {
		return oldStkLinkLost;
	}

	public void setOldStkLinkLost(boolean oldStkLinkLost) {
		this.oldStkLinkLost = oldStkLinkLost;
	}
}
