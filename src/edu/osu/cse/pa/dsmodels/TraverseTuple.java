package edu.osu.cse.pa.dsmodels;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import edu.osu.cse.pa.spg.AbstractAllocNode;
import edu.osu.cse.pa.spg.AbstractSPGEdge;
import edu.osu.cse.pa.spg.FieldPTEdge;
import soot.jimple.toolkits.callgraph.Edge;

public class TraverseTuple {
	public static int IN = 0;
	public static int OUT = 1; 
	public static int NONE = -1;
	
	private static Set<TraverseTuple> quads = new HashSet<TraverseTuple>();	
	private AbstractSPGEdge prevEdge; //added by Jyothi
	private int direction;
	private AbstractAllocNode node;
	private LinkedList<Edge> ctxStk;
	private LinkedList<FieldPTEdge> fldStk;
	private HashSet<AbstractSPGEdge> visitedCtxEdges;
	private HashSet<Pair<FldPair, Integer>> visitedFldEdges;	// with context snapshot
	private int ctxHash;
	
	private TraverseTuple(AbstractAllocNode n, LinkedList<Edge> cs, LinkedList<FieldPTEdge> fs, HashSet<AbstractSPGEdge> visitedCtxEdges,
		HashSet<Pair<FldPair, Integer>> visitedFldEdges, int ctxHash, AbstractSPGEdge prevEdge, int direction) {
		this.node = n;
		this.ctxStk = cs;
		this.fldStk = fs;
		this.visitedCtxEdges = visitedCtxEdges;
		this.visitedFldEdges = visitedFldEdges;
		this.ctxHash = ctxHash;
		this.prevEdge = prevEdge;
		this.direction = direction;
	}
		
	public static TraverseTuple getTuple(AbstractAllocNode n, LinkedList<Edge> cs, LinkedList<FieldPTEdge> fs, HashSet<AbstractSPGEdge> visitedCtxEdges,
		HashSet<Pair<FldPair, Integer>> visitedFldEdges, int ctxHash, AbstractSPGEdge prevEdge, int direction) {
		TraverseTuple quad = new TraverseTuple(n, cs, fs, visitedCtxEdges, visitedFldEdges, ctxHash, prevEdge, direction);
		quads.add(quad);
		return quad;		
	}
		
	public AbstractAllocNode getNode() {
		return node;
	}
	
	public LinkedList<Edge> getCtxStk() {
		return ctxStk;
	}
	
	public LinkedList<FieldPTEdge> getFldStk() {
		return fldStk;
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
