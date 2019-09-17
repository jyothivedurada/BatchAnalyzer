package edu.osu.cse.pa.dsmodels;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import edu.osu.cse.pa.spg.AbstractAllocNode;
import edu.osu.cse.pa.spg.AbstractSPGEdge;
import edu.osu.cse.pa.spg.FieldPTEdge;
import soot.jimple.toolkits.callgraph.Edge;

public class QuickTraverseTuple {
	private static Set<QuickTraverseTuple> quads = new HashSet<QuickTraverseTuple>();	
	private AbstractAllocNode node;
	private LinkedList<Edge> ctxStk;
	private HashSet<AbstractSPGEdge> visitedCtxEdges;
	private int ctxHash;

	private QuickTraverseTuple(AbstractAllocNode n, LinkedList<Edge> cs,  HashSet<AbstractSPGEdge> visitedCtxEdges,
			int ctxHash) {
		this.node = n;
		this.ctxStk = cs;
		this.visitedCtxEdges = visitedCtxEdges;
		this.ctxHash = ctxHash;
	}

	public static QuickTraverseTuple getTuple(AbstractAllocNode n, LinkedList<Edge> cs, HashSet<AbstractSPGEdge> visitedCtxEdges,
			int ctxHash) {
		QuickTraverseTuple quad = new QuickTraverseTuple(n, cs, visitedCtxEdges, ctxHash);
		quads.add(quad);
		return quad;		
	}

	public AbstractAllocNode getNode() {
		return node;
	}

	public LinkedList<Edge> getCtxStk() {
		return ctxStk;
	}

	public HashSet<AbstractSPGEdge> getVisitedCtxEdges() {
		return visitedCtxEdges;
	}

	public int getCtxHash() {
		return ctxHash;
	}

	public static void clear() {
		quads.clear();
	}
}
