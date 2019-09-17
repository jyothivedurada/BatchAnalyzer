package edu.osu.cse.pa.dsmodels;

import java.util.LinkedList;

import edu.osu.cse.pa.spg.FieldPTEdge;
import soot.jimple.toolkits.callgraph.Edge;

/**
 * @author Jyothi Vedurada
 * @since Jun 25, 2019
 */
public class FldStkChain {
	private LinkedList<FieldPTEdge> current;
	private FldStkChain previous;
	private boolean oldStkLinkLost = false;
	
	public FldStkChain(){
		
	}

	public FldStkChain(LinkedList<FieldPTEdge> current, FldStkChain previous){
		this.current = current;
		this.previous = previous;
	}
	
	public FldStkChain(LinkedList<FieldPTEdge> current, FldStkChain previous, boolean oldStkLinkLost){
		this.current = current;
		this.previous = previous;
		this.oldStkLinkLost = oldStkLinkLost;
	}
	
	public LinkedList<FieldPTEdge> getCurrent() {
		return current;
	}
	public void setCurrent(LinkedList<FieldPTEdge> current) {
		this.current = current;
	}
	public FldStkChain getPrevious() {
		return previous;
	}
	public void setPrevious(FldStkChain previous) {
		this.previous = previous;
	}

	public boolean isOldStkLinkLost() {
		return oldStkLinkLost;
	}

	public void setOldStkLinkLost(boolean oldStkLinkLost) {
		this.oldStkLinkLost = oldStkLinkLost;
	}
}
