package edu.osu.cse.pa.dsmodels;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import edu.iitm.cse.common.dsmodels.MutableInt;
import edu.osu.cse.pa.spg.AbstractAllocNode;
import edu.osu.cse.pa.spg.AbstractSPGEdge;
import edu.osu.cse.pa.spg.FieldPTEdge;
import soot.jimple.toolkits.callgraph.Edge;

public class TraverseTupleNew {
	public static int IN = 0;
	public static int OUT = 1; 
	public static int NONE = -1;
	
	private static Set<TraverseTupleNew> quads = new HashSet<TraverseTupleNew>();	
	private AbstractSPGEdge prevEdge; //added by Jyothi
	private int direction;
	private AbstractAllocNode node;
	private CtxStkChain ctxChain;
	private FldStkChain fldChain;
	private HashSet<AbstractSPGEdge> visitedCtxEdges;
	private HashSet<Pair<FldPair, Integer>> visitedFldEdges;	// with context snapshot
	private int ctxHash;
	
	private TraverseTupleNew(AbstractAllocNode n, CtxStkChain cs, FldStkChain fs, HashSet<AbstractSPGEdge> visitedCtxEdges,
		HashSet<Pair<FldPair, Integer>> visitedFldEdges, int ctxHash, AbstractSPGEdge prevEdge, int direction) {
		this.node = n;
		this.ctxChain = cs;
		this.fldChain = fs;
		this.visitedCtxEdges = visitedCtxEdges;
		this.visitedFldEdges = visitedFldEdges;
		this.ctxHash = ctxHash;
		this.prevEdge = prevEdge;
		this.direction = direction;
	}
		
	public static TraverseTupleNew getTuple(AbstractAllocNode n, CtxStkChain cs, FldStkChain fs, HashSet<AbstractSPGEdge> visitedCtxEdges,
		HashSet<Pair<FldPair, Integer>> visitedFldEdges, int ctxHash, AbstractSPGEdge prevEdge, int direction) {
		TraverseTupleNew quad = new TraverseTupleNew(n, cs, fs, visitedCtxEdges, visitedFldEdges, ctxHash, prevEdge, direction);
		quads.add(quad);
		return quad;		
	}
		
	public AbstractAllocNode getNode() {
		return node;
	}
	
	public CtxStkChain getCtxStk() {
		return ctxChain;
	}
	
	public FldStkChain getFldStk() {
		return fldChain;
	}
	
	public HashSet<AbstractSPGEdge> getVisitedCtxEdges() {
		return visitedCtxEdges;
	}
	
	public HashSet<Pair<FldPair, Integer>> getVisitedFldEdges() {
		return visitedFldEdges;
	}
	
	public int getCtxHash() {
		return ctxHash;
	}
			
	public static void clear() {
		quads.clear();
	}

	public AbstractSPGEdge getPrevEdge() {
		return prevEdge;
	}

	public void setPrevEdge(AbstractSPGEdge prevEdge) {
		this.prevEdge = prevEdge;
	}

	public int getDirection() {
		return direction;
	}

	public void setDirection(int direction) {
		this.direction = direction;
	}

}
