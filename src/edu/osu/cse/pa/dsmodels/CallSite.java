package edu.osu.cse.pa.dsmodels;

import edu.osu.cse.pa.spg.AbstractSPGEdge;
import edu.osu.cse.pa.spg.EntryEdge;
import edu.osu.cse.pa.spg.ExitEdge;
import soot.jimple.toolkits.callgraph.Edge;

public class CallSite {
	
//	private static Set<AbstractSPGEdge> edges = new HashSet<AbstractSPGEdge>();

	public static Edge getCallsite(AbstractSPGEdge e) {	
		if (e instanceof EntryEdge) {
			return ((EntryEdge)e).getCallGraphEdge();
		} else if (e instanceof ExitEdge) {
			return ((ExitEdge)e).getCallGraphEdge();
		}
		
		return null;
	}
//	
//	public static void clear() {
//		edges.clear();
//	}
}
