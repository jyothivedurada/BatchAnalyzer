package edu.osu.cse.pa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.commons.collections4.Trie;
import org.apache.commons.collections4.trie.PatriciaTrie;

import edu.iitm.cse.alias.batch.dsmodels.AliasGlobalVariables;
import edu.osu.cse.pa.dsmodels.AliasCache;
import edu.osu.cse.pa.dsmodels.CallSite;
import edu.osu.cse.pa.dsmodels.CtxPair;
import edu.osu.cse.pa.dsmodels.CtxStkChain;
import edu.osu.cse.pa.dsmodels.FldPair;
import edu.osu.cse.pa.dsmodels.FldStkChain;
import edu.osu.cse.pa.dsmodels.ManuMayAliasAnalysis;
import edu.osu.cse.pa.dsmodels.NumberedObject;
import edu.osu.cse.pa.dsmodels.OutOfBudgetException;
import edu.osu.cse.pa.dsmodels.Pair;
import edu.osu.cse.pa.dsmodels.Summary;
import edu.osu.cse.pa.dsmodels.SummaryRecord;
import edu.osu.cse.pa.dsmodels.TraverseTuple;
import edu.osu.cse.pa.dsmodels.TraverseTupleNew;
import edu.osu.cse.pa.dsmodels.Util;
import edu.osu.cse.pa.dsmodels.WildcardEdge;
import edu.osu.cse.pa.spg.AbstractAllocNode;
import edu.osu.cse.pa.spg.AbstractSPGEdge;
import edu.osu.cse.pa.spg.ClassConstNode;
import edu.osu.cse.pa.spg.EntryEdge;
import edu.osu.cse.pa.spg.ExitEdge;
import edu.osu.cse.pa.spg.FieldPTEdge;
import edu.osu.cse.pa.spg.NodeFactory;
import edu.osu.cse.pa.spg.StringConstNode;
import edu.osu.cse.pa.spg.SymbolicPointerGraph;
import edu.osu.cse.pa.spg.VarNode;
import edu.osu.cse.pa.spg.symbolic.SymbolicObject;
import iohoister.analysis.MayAliasAnalysis;
import soot.AnySubType;
import soot.ArrayType;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.NullType;
import soot.PointsToAnalysis;
import soot.PointsToSet;
import soot.RefLikeType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.util.HashMultiMap;
import soot.util.MultiMap;
import soot.util.queue.QueueReader;

public class PAMain implements MayAliasAnalysis {
	public static int sameCxtCnt  = 0;
	public static int compChks = 0;

	public HashSet<Type> classTypes;

	private boolean pre_jimplifed = false;

	private boolean spgBuilt = false;

	public static boolean ANALYSIS_OPTION = false;

	public static boolean pre_computed_callgraph = true;

	public static int object_cstring = 1;

	public static int recursion_cstring = 0;

	public static boolean callsites = true;

	//added by Jyothi -- start

	public HashSet<String> strings = new HashSet<>();

	public HashMap<String, HashSet<String>> clusters = new HashMap<>();

	public static int ALGO = 1;

	//added by Jyothi -- end

	private static HashMap<SootMethod, Integer> methodProfile =
			new HashMap<SootMethod, Integer>();
	private static int avgNumOfCallers = 0;
	private static int threshold;

	public static boolean VERBOSE = false;
	//---
	HashSet<String> dottyLines = new HashSet<String>();

	public static void countStmts() {
		int count = 0;
		CallGraph cg = Scene.v().getCallGraph();
		SootMethod m = Scene.v().getMainClass().getMethodByName("main");
		List<SootMethod> worklist = new ArrayList<SootMethod>();
		worklist.add(m);
		Set<SootMethod> visited = new HashSet<SootMethod>();
		while (worklist.size() > 0) {
			m = (SootMethod) worklist.get(0);
			worklist.remove(0);
			visited.add(m);
			if (!m.isConcrete())
				continue;
			count += m.getActiveBody().getUnits().size();
			for (Iterator<Edge> it = cg.edgesOutOf(m); it.hasNext();) {

				Edge edge = it.next();
				SootMethod tgt = edge.tgt();
				if (!visited.contains(tgt) && !worklist.contains(tgt)) {
					worklist.add(tgt);
				}
			}
		}

		System.out.println("Total number of statements: " + count);
	}

	/*
	 * Builds the symbolic pointer graph & initialize certain variables
	 */
	public void buildSPG() {
		// moved to mayAlias() since we need to do timing
		if (spgBuilt) {
			return;
		} else {
			spgBuilt = true;
		}
		Util.spgLibMtdsTime = 0;
		ReachableMethods methods = Scene.v().getReachableMethods();
		CallGraph cg = Scene.v().getCallGraph();

		QueueReader<MethodOrMethodContext> r = methods.listener();
		while (r.hasNext()) {
			SootMethod method = (SootMethod) r.next();

			// skip non-concrete methods
			if (!method.isConcrete()) {
				continue;
			}
			//Added by Jyothi -- START
			/*if (!method.isRelevant()) {
				continue;
			}*/
			//Added by Jyothi -- END

			long start = System.currentTimeMillis();
			Util.tweakBody(method);
			SymbolicPointerGraph.v(method).build();
			long end = System.currentTimeMillis();
			long delta = end - start;
			if (method.getDeclaringClass().isLibraryClass()) {
				Util.spgLibMtdsTime += delta;
			}

			if (Util.TEST_SUMMARY) {
				int callers = iterSize(cg.edgesInto(method));
				methodProfile.put(method, callers);
				avgNumOfCallers += callers;
			}		
		}

		if (Util.TEST_SUMMARY) {
			avgNumOfCallers = avgNumOfCallers / methodProfile.size();
			threshold = avgNumOfCallers * Util.SUMM_RATIO;
			System.out.println("THRESHOLD: " + threshold);
			if (Util.DEBUG) {
				System.out.println("[DEBUG] average number of incoming CG edges: " + avgNumOfCallers);
			}
		}


		r = methods.listener();		

		// add entry and exit edges
		while (r.hasNext()) {
			// DO NOT CHANGE
			SootMethod method = (SootMethod) r.next();
			//Added by Jyothi -- START
			/*if (!method.isRelevant()) {
				continue;
			}*/
			//Added by Jyothi -- END

			SymbolicPointerGraph spg = SymbolicPointerGraph.v(method);
			spg.addEntryAndExitEdges();
		}
	}

	/*private boolean processGVN(AbstractAllocNode cur, AbstractAllocNode dest, LinkedList<TraverseTuple> worklist,
			LinkedList<FieldPTEdge> fldStk, HashSet<AbstractSPGEdge> visitedCtxEdges, HashSet<Pair<FldPair, Integer>> visitedFldEdges, int ctxHash) {

		LinkedList<Edge> ctxStk = new LinkedList<Edge>();
		for (Iterator<VarNode> vnIter = cur.getPointBy(); vnIter.hasNext(); ) {
			VarNode vn = vnIter.next();
			if (vn instanceof GlobalVarNode) {
				for (Iterator<PointsToEdge> pteIter = vn.getPointsToEdges(); pteIter.hasNext(); ) {
					PointsToEdge pte = pteIter.next();
					AbstractAllocNode aan = pte.tgt();
					if (aan == dest) {
						return true;
					}

					TraverseTuple tt = TraverseTuple.getTuple(aan, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash);
					worklist.add(tt);
				}
			}			
		}

		return false;
	}
*/
	public boolean isDuplicate(AbstractSPGEdge e, LinkedList<Edge> ctxStk, HashSet<AbstractSPGEdge> visitedCtxEdges,
			HashSet<Pair<FldPair, Integer>> visitedFldEdges, int ctxHash, boolean isBar) {
		if (e instanceof FieldPTEdge) {		
			for (Pair<FldPair, Integer> p : visitedFldEdges) {
				FldPair fp = p.first;
				AbstractSPGEdge fe = fp.getEdge();
				if (e == fe && fp.isBar() == isBar) {
					if (ctxHash == p.second) {
						return true;
					}
				}
			}
			//			visitedFldEdges.add(new Pair<FieldPTEdge, Integer>((FieldPTEdge)e, ctxHash));			
		} else {
			if (visitedCtxEdges.contains(e)) {
				return true;
			}
			//    		visitedCtxEdges.add(e);
		}

		return false;
	}

	public String getNodeName(String string){
		return string.replaceAll("\\s+", "").replaceAll("<", "").replaceAll(">", "").replaceAll("\\.","_").replaceAll("\\(.*\\)", "").replace("@", "0").replace("$", "_");
	}

	public boolean basic(AbstractAllocNode n1, AbstractAllocNode n2) {
		//System.out.println("#n1 : "+n1+" #n2 : "+n2);
		if (n1 == n2) {
			return true;
			//	    	} else if (n1 instanceof AllocNode && n2 instanceof AllocNode) {
		} else if (!(n1 instanceof SymbolicObject || n2 instanceof SymbolicObject)) {
			return false;
		} else if (Util.pointByGVN(n1) || Util.pointByGVN(n2)) {
			return true;
		}

		if (Util.USE_CACHE) {
			Boolean cacheResult = AliasCache.getCache(n1, n2);
			if (null != cacheResult) {
				//System.out.println("Found in cache : actual query or its reverse");
				return cacheResult.booleanValue();        		
			}
		}    	

		Util.traversedNodes = 0;

		LinkedList<TraverseTuple> worklist = new LinkedList<TraverseTuple>();
		TraverseTuple t = TraverseTuple.getTuple(n1, new LinkedList<Edge>(), new LinkedList<FieldPTEdge>(),
				new HashSet<AbstractSPGEdge>(), new HashSet<Pair<FldPair, Integer>>(), 0, null, TraverseTuple.NONE);
		worklist.add(t);
		//	    	}

		SootMethod n2Method = n2.getMethod();
		while (!worklist.isEmpty()) {
			t = worklist.removeFirst();
			AbstractAllocNode n = t.getNode();
			AbstractSPGEdge prevEdge = t.getPrevEdge();

			/*try{
				//System.out.println("Entered inside!! "+type);
				if(n.getType()!=null)
					System.out.println("Processing Type: "+n.getType());
				if(n.getType() == null || !(n.getType() instanceof AnySubType))
					System.out.println("Processing Node: "+n);
			}catch(Exception e){
				System.out.println("Caught Exception !!");
			}
			 */
			//--- incoming edges
			for (Iterator<AbstractSPGEdge> inIter = n.getIncomingEdges(); inIter.hasNext();) {        		
				AbstractSPGEdge e = inIter.next();
				if(e == prevEdge) continue;
				AbstractAllocNode src = e.src();
				SootMethod mtd = src.getMethod();

				// do not clone, but copy on write
				LinkedList<Edge> ctxStk = t.getCtxStk();
				LinkedList<FieldPTEdge> fldStk = t.getFldStk();
				//	System.out.println("fld stk : "+fldStk.size());
				HashSet<AbstractSPGEdge> visitedCtxEdges = t.getVisitedCtxEdges();
				HashSet<Pair<FldPair, Integer>> visitedFldEdges = t.getVisitedFldEdges();
				int ctxHash = t.getCtxHash();        		

				// SRC
				// --- BEGIN COPY-PASTE
				boolean isDup = isDuplicate(e, ctxStk, visitedCtxEdges, visitedFldEdges, ctxHash, true);
				if (isDup) {
					// we should ignore the case when the top of stack is already wildcard
					// and the e is an edge on that cycle
					if ((e instanceof FieldPTEdge) && !(isOnCycle(e, fldStk))) {
						// detect cycles
						ArrayList<FieldPTEdge> cycle = new ArrayList<FieldPTEdge>();    				
						fldStk = (LinkedList<FieldPTEdge>) fldStk.clone();
						int pos = 0;
						while (!fldStk.isEmpty()) {
							FieldPTEdge fldEdge = fldStk.removeFirst();
							// FIXME: assumed to be too expensive, return context-insensitive instead
							if (fldEdge instanceof WildcardEdge) { 
								//System.out.println("Conservative result!!");
								return true;
							}

							cycle.add(fldEdge);   					
							WildcardEdge wildcard = new WildcardEdge(cycle, pos++);
							LinkedList<FieldPTEdge> fldStkClone = (LinkedList<FieldPTEdge>)(fldStk.clone());
							fldStkClone.addFirst(wildcard);
							TraverseTuple tt = TraverseTuple.getTuple(fldEdge.tgt(), ctxStk, fldStkClone, visitedCtxEdges, visitedFldEdges, ctxHash, e, TraverseTuple.NONE);
							worklist.add(tt);
							if (Util.sootFieldEquals(fldEdge.getField(), ((FieldPTEdge)e).getField())) {    					
								break;
							}
						}
					}
					
					if(!((e instanceof EntryEdge) || (e instanceof ExitEdge))){
						continue;
					}
				}
				// --- END COPY-PASTE

				if (src == n1) {
					continue;
				}

				Util.traversedNodes++;
				if (Util.isOutOfBudget()) {
					return true;
				}

				if (e instanceof FieldPTEdge) {
					fldStk = (LinkedList<FieldPTEdge>) fldStk.clone();
					fldStk.addFirst(((FieldPTEdge) e));        			
				} else if (e instanceof EntryEdge) {
					Edge cs1 = CallSite.getCallsite(e);

					if (!ctxStk.isEmpty()) {
						ctxStk = (LinkedList<Edge>) ctxStk.clone();
						Edge cs2 = ctxStk.removeFirst();            			

						if (!cs1.equals(cs2)) {	// matching call site
							// relax the call site constraint for gvn
							// TODO: might be wrong
							/*if ( !(n instanceof SymbolicGlobalObject &&
									cs1.kind().isStatic() &&
									cs2.kind().isStatic() &&
									cs1.getTgt().equals(cs2.getTgt())))*/ {

										continue;
									}
						}
					}
				} else {
					/*if (Util.getEscapableObjects(mtd).size() <= 1 && !Util.getReachables(mtd).contains(n2Method)) {
						continue;
					}*/
					//System.out.println("IN Hello reached!! "+prevEdge + " : "+ e.src()+ " : "+e.tgt() );
					ctxStk = (LinkedList<Edge>) ctxStk.clone();
					// only enter methods that would potentially bring points-to effects
					Edge cs1 = CallSite.getCallsite(e);
					ctxStk.addFirst(cs1);
				}

				//Jyothi : moved the block of code from before edge-checking to after edge-checking.
				//REASON : Otherwise it returns true if it sees a globalvar even if the context do not match -- can lead to imprecision.  
				//Code block : START

				if (Util.pointByGVN(src)) {
					//	        			if (processGVN(src, n2, worklist, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {		        		
					//	    	        		return true;
					//	    	        	} else {
					//AliasGlobalVariables.metGlobalVar = true;
					//System.out.println("Reached global in method :"+src.getMethod());
					return true;
					//	    	         	}
				}


				// jE9pazU8
				if (
						//	        			Util.pointByGVN(src) ||		// TODO: considering gvn might lead to performance hit
						src instanceof StringConstNode ||
						src instanceof ClassConstNode
						) {
					//AliasGlobalVariables.metGlobalVar = true;
					//System.out.println("Reached Stringconst and classconst in method :"+src.getMethod());
					return true;
				}


				// context can be unbalanced, but putField & getField should match
				if (src == n2) {
					if (fldStk.isEmpty()) {	 
						AliasGlobalVariables.nonConservativeAns = true;
						//System.out.println("Actual true src:" + e.src() + " : "+e.tgt() );
						/*if(ctxStk.isEmpty()){
							System.out.println("Added one");
							AliasGlobalVariables.aliasesWthEmptyCallStk.put(n1, n2);
						}*/
						return true;	// alias found
					} else {
						continue;		// invalid path, do NOT add to worklist
					}
				} else if (Util.USE_CACHE) {
					//System.out.println("Caching is on!");
					if (fldStk.isEmpty() && ctxStk.isEmpty()) {
						//System.out.println("Stacks are empty!");
						Boolean cache = AliasCache.getCache(src, n2);
						if (null != cache) {
							if(cache.booleanValue()){
								//System.out.println("Found in cache : sub query");
								//System.out.println("Reusing the cached value!");
								//System.out.println("Query #n1 : "+n1+" #n2 : "+n2+ " #src : "+src);
								return true;	 
							}else{
								continue;	   
							}
						}
					}	        		
				}

				//		        	if (Util.USE_SUMMARY && e instanceof ExitEdge && Summary.ignoreMethod(mtd)) continue;

				if (Util.USE_SUMMARY && e instanceof ExitEdge && worthApply(mtd, n2Method)) {
					if (applySummary(src, n2, worklist, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {	        			
						return true;
					}
				} else {	        		
					if (e instanceof FieldPTEdge) {
						visitedFldEdges = (HashSet<Pair<FldPair, Integer>>) visitedFldEdges.clone();
						visitedFldEdges.add(new Pair<FldPair, Integer>(FldPair.getPair(e, true), ctxHash));
						//System.out.println("In Feild Edge : "+ e.src() + " : "+e.tgt()+ " : "+e);
					} else {
						visitedCtxEdges = (HashSet<AbstractSPGEdge>) visitedCtxEdges.clone();
						visitedCtxEdges.add(e);
						ctxHash = 3 * ctxHash + e.getReverseId();
						/*	if(e instanceof EntryEdge){
							//	System.out.println("In Entry Edge : "+ e.src() + " : "+e.tgt());
						}else{
							//System.out.println("In Exit Edge : "+ e.src() + " : "+e.tgt());
						}*/
					}
					TraverseTuple tt = TraverseTuple.getTuple(src, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash,e, TraverseTuple.IN);
					worklist.add(tt);
				}
			}

			//--- outgoing edges
			for (Iterator<AbstractSPGEdge> outIter = n.getOutgoingEdges(); outIter.hasNext();) {    			
				AbstractSPGEdge e = outIter.next();
				if(e == prevEdge) continue;
				AbstractAllocNode tgt = e.tgt();
				SootMethod mtd = tgt.getMethod();
				Type type = tgt.getType();

				//	    			if (e instanceof EntryEdge && mtd != n2Method && Util.empiricalIgnoreMethod(mtd)) continue;

				// do not clone, but copy on write
				LinkedList<Edge> ctxStk = t.getCtxStk();
				LinkedList<FieldPTEdge> fldStk = t.getFldStk();
				//System.out.println("fld stk : "+fldStk.size());
				HashSet<AbstractSPGEdge> visitedCtxEdges = t.getVisitedCtxEdges();
				HashSet<Pair<FldPair, Integer>> visitedFldEdges = t.getVisitedFldEdges();
				int ctxHash = t.getCtxHash();

				// TGT
				// --- BEGIN COPY-PASTE
				boolean isDup = isDuplicate(e, ctxStk, visitedCtxEdges, visitedFldEdges, ctxHash, false);
				if (isDup) {
					if (!(e instanceof FieldPTEdge))    				
						continue;
				}
				// --- END COPY-PASTE

				//	        		if (addedNodes.contains(tgt)) continue;
				if (tgt == n1) {
					continue;
				}

				try {
					if (tgt.getMethod().toString().equals("<java.lang.Object: void <init>()>")) {
						continue;
					}
				} catch (Exception ex) {
					continue;
				}

				Util.traversedNodes++;
				if (Util.isOutOfBudget()) {
					return true;
				}

				if (e instanceof FieldPTEdge) {
					if (fldStk.isEmpty()) {
						continue;
					} else {
						FieldPTEdge fpt1 = (FieldPTEdge) e;
						FieldPTEdge topEdge = fldStk.peek();        				
						if (topEdge instanceof WildcardEdge) {        					
							WildcardEdge wildcard = (WildcardEdge) topEdge;
							if (!wildcard.match(fpt1.getField())) {
								continue;
							} else {
								wildcard = (WildcardEdge) wildcard.clone();
								wildcard.forward();
								fldStk = (LinkedList<FieldPTEdge>) (fldStk.clone());
								fldStk.removeFirst();
								fldStk.addFirst(wildcard);
							}       					
						} else {
							SootField topFld = topEdge.getField();            				

							if (!Util.sootFieldEquals(fpt1.getField(), topFld)) {
								continue;
							}

							fldStk = (LinkedList<FieldPTEdge>) (fldStk.clone());
							fldStk.removeFirst();
						}        				
					}        			
				} else if (e instanceof EntryEdge) {
					/*if (Util.getEscapableObjects(mtd).size() <= 1 && !Util.getReachables(mtd).contains(n2Method)) {
						continue;
					}
					 */
					//System.out.println(" OUT Hello reached!! "+prevEdge + " : "+ e.src()+ " : "+e.tgt() );
					ctxStk = (LinkedList<Edge>) ctxStk.clone();
					Edge cs1 = CallSite.getCallsite(e);   			
					ctxStk.addFirst(cs1);
				} else {
					Edge cs1 = CallSite.getCallsite(e);        			

					if (!ctxStk.isEmpty()) {
						ctxStk = (LinkedList<Edge>) ctxStk.clone();
						Edge cs2 = ctxStk.removeFirst();

						if (!cs1.equals(cs2)) {	// matching call site
							// relax the call site constraint for gvn
							// TODO: might be wrong
							/*if ( !(n instanceof SymbolicGlobalObject &&
									cs1.kind().isStatic() &&
									cs2.kind().isStatic() &&
									cs1.getTgt().equals(cs2.getTgt()))) */{

										continue;
									}
						}
					}
				}


				if (Util.pointByGVN(tgt)) {
					//	        			if (processGVN(tgt, n2, worklist, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {
					//			        		return true;
					//			        	} else {
					//AliasGlobalVariables.metGlobalVar = true;
					//System.out.println("Met global : "+tgt.getMethod());
					return true;
					//			        	}
				}

				if (
						//	        			Util.pointByGVN(tgt) ||		// TODO: considering gvn might lead to performance hit
						tgt instanceof StringConstNode ||
						tgt instanceof ClassConstNode) {
					//AliasGlobalVariables.metGlobalVar = true;
					//System.out.println("REached String const and class const in method :"+tgt.getMethod());
					return true;
				} 

				// context can be unbalanced, but putField & getField should match
				if (tgt == n2) {
					if (fldStk.isEmpty()) {
						AliasGlobalVariables.nonConservativeAns = true;
						//	System.out.println("Actual true tgt:" + e.src() + " : " + e.tgt() );
						/*if(ctxStk.isEmpty()){
							System.out.println("Added one");
							AliasGlobalVariables.aliasesWthEmptyCallStk.put(n1, n2);
						}*/
						return true;
					} else {
						continue;
					}
				} else if (Util.USE_CACHE) {
					if (fldStk.isEmpty() && ctxStk.isEmpty()) {
						Boolean cache = AliasCache.getCache(tgt, n2);
						if (null != cache) {
							if(cache.booleanValue()){
								//System.out.println("Found in cache : sub query");
								//System.out.println("Reusing the cached value!");
								//System.out.println("Query #n1 : "+n1+" #n2 : "+n2+ " #tgt : "+tgt);
								return true;	 
							}else{
								continue;	   
							}        				
						}
					}
				}

				//	        		if (Util.USE_SUMMARY && e instanceof EntryEdge && Summary.ignoreMethod(mtd)) continue;

				if (Util.USE_SUMMARY && e instanceof EntryEdge && worthApply(mtd, n2Method)) {
					if (applySummary(tgt, n2, worklist, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {	        			
						return true;
					}
				} else {
					if (e instanceof FieldPTEdge) {
						visitedFldEdges = (HashSet<Pair<FldPair, Integer>>) visitedFldEdges.clone();
						visitedFldEdges.add(new Pair<FldPair, Integer>(FldPair.getPair(e, false), ctxHash));
						//System.out.println("Out Field Edge : "+ e.src() + " : "+e.tgt() + " : "+e );
					} else {
						visitedCtxEdges = (HashSet<AbstractSPGEdge>) visitedCtxEdges.clone();
						visitedCtxEdges.add(e);
						ctxHash = 3 * ctxHash + e.getId();
						/*if(e instanceof EntryEdge){
							//	System.out.println("Out Entry Edge : "+ e.src() + " : "+e.tgt());
						}else{
							//System.out.println("Out Exit Edge : "+ e.src() + " : "+e.tgt());
						}*/
					}
					TraverseTuple tt = TraverseTuple.getTuple(tgt, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash, e, TraverseTuple.OUT);
					worklist.add(tt);	
				}    		
			}



			//	    		if (traversedNodes >= Util.SPA_BUDGET_NODES) {
			//	    			return true;
			//	    		}
		}    	

		AliasGlobalVariables.nonConservativeAns = true;
		//System.out.println("Actual false:");
		return false;
	}

	public boolean RT(AbstractAllocNode n1, AbstractAllocNode n2, HashSet<Type> relevantTypes) {


		if (n1 == n2) {
			return true;
			//	    	} else if (n1 instanceof AllocNode && n2 instanceof AllocNode) {
		} else if (!(n1 instanceof SymbolicObject || n2 instanceof SymbolicObject)) {
			return false;
		} else if (Util.pointByGVN(n1) || Util.pointByGVN(n2)) {
			return true;
		}

		if (Util.USE_CACHE) {
			Boolean cacheResult = AliasCache.getCache(n1, n2);
			if (null != cacheResult) {
				return cacheResult.booleanValue();        		
			}
		}    	

		Util.traversedNodes = 0;

		LinkedList<TraverseTuple> worklist = new LinkedList<TraverseTuple>();
		//	    	if (Util.pointByGVN(n1)) {
		//	    		if (processGVN(n1, n2, worklist, new LinkedList<FieldPTEdge>(), new HashSet<AbstractSPGEdge>(),
		//	    	    	new HashSet<Pair<FldPair, Integer>>(), 0)) {    		
		//	    	    		return true;
		//	    	    }
		//	    	} else {
		TraverseTuple t = TraverseTuple.getTuple(n1, new LinkedList<Edge>(), new LinkedList<FieldPTEdge>(),
				new HashSet<AbstractSPGEdge>(), new HashSet<Pair<FldPair, Integer>>(), 0, null, TraverseTuple.NONE);
		worklist.add(t);
		//	    	}

		SootMethod n2Method = n2.getMethod();
		while (!worklist.isEmpty()) {
			t = worklist.removeFirst();
			AbstractAllocNode n = t.getNode();
			AbstractSPGEdge prevEdge = t.getPrevEdge();



			//--- incoming edges
			for (Iterator<AbstractSPGEdge> inIter = n.getIncomingEdges(); inIter.hasNext();) {        		
				AbstractSPGEdge e = inIter.next();
				if(e == prevEdge) continue;
				AbstractAllocNode src = e.src();
				SootMethod mtd = src.getMethod();
				Type type = src.getType();

				if((type != null) && !(type.isRelevant() || (type instanceof ArrayType && ((ArrayType)type).baseType.isRelevant())
						|| (type instanceof AnySubType) || (type instanceof NullType))){
					/*try{
						System.out.println("Entered inside!! "+type);
					}catch(Exception ex){
						System.out.println("Caught Exception !!");
					}*/
					continue;
				}

				//System.out.println(n.getMethod());

				//	    			if (e instanceof ExitEdge && mtd != n2Method && Util.empiricalIgnoreMethod(mtd)) continue;

				// do not clone, but copy on write
				LinkedList<Edge> ctxStk = t.getCtxStk();
				LinkedList<FieldPTEdge> fldStk = t.getFldStk();
				//	System.out.println("fld stk : "+fldStk.size());
				HashSet<AbstractSPGEdge> visitedCtxEdges = t.getVisitedCtxEdges();
				HashSet<Pair<FldPair, Integer>> visitedFldEdges = t.getVisitedFldEdges();
				int ctxHash = t.getCtxHash();        		

				// SRC
				// --- BEGIN COPY-PASTE
				boolean isDup = isDuplicate(e, ctxStk, visitedCtxEdges, visitedFldEdges, ctxHash, true);
				if (isDup) {
					// we should ignore the case when the top of stack is already wildcard
					// and the e is an edge on that cycle
					if ((e instanceof FieldPTEdge) && !(isOnCycle(e, fldStk))) {
						// detect cycles
						ArrayList<FieldPTEdge> cycle = new ArrayList<FieldPTEdge>();    				
						fldStk = (LinkedList<FieldPTEdge>) fldStk.clone();
						int pos = 0;
						while (!fldStk.isEmpty()) {
							FieldPTEdge fldEdge = fldStk.removeFirst();
							// FIXME: assumed to be too expensive, return context-insensitive instead
							if (fldEdge instanceof WildcardEdge) { 
								//System.out.println("Conservative result!!");
								return true;
							}

							cycle.add(fldEdge);   					
							WildcardEdge wildcard = new WildcardEdge(cycle, pos++);
							LinkedList<FieldPTEdge> fldStkClone = (LinkedList<FieldPTEdge>)(fldStk.clone());
							fldStkClone.addFirst(wildcard);
							TraverseTuple tt = TraverseTuple.getTuple(fldEdge.tgt(), ctxStk, fldStkClone, visitedCtxEdges, visitedFldEdges, ctxHash, e, TraverseTuple.NONE);
							worklist.add(tt);
							if (Util.sootFieldEquals(fldEdge.getField(), ((FieldPTEdge)e).getField())) {    					
								break;
							}
						}
					}

					if(!((e instanceof EntryEdge) || (e instanceof ExitEdge))){
						continue;
					}
				}
				// --- END COPY-PASTE

				if (src == n1) {
					continue;
				}

				Util.traversedNodes++;
				if (Util.isOutOfBudget()) {
					return true;
				}

				if (e instanceof FieldPTEdge) {
					fldStk = (LinkedList<FieldPTEdge>) fldStk.clone();
					fldStk.addFirst(((FieldPTEdge) e));        			
				} else if (e instanceof EntryEdge) {
					Edge cs1 = CallSite.getCallsite(e);

					if (!ctxStk.isEmpty()) {
						ctxStk = (LinkedList<Edge>) ctxStk.clone();
						Edge cs2 = ctxStk.removeFirst();            			

						if (!cs1.equals(cs2)) {	// matching call site
							// relax the call site constraint for gvn
							// TODO: might be wrong
							/*if ( !(n instanceof SymbolicGlobalObject &&
									cs1.kind().isStatic() &&
									cs2.kind().isStatic() &&
									cs1.getTgt().equals(cs2.getTgt())))*/ {

										continue;
									}
						}
					}
				} else {
					/*if (Util.getEscapableObjects(mtd).size() <= 1 && !Util.getReachables(mtd).contains(n2Method)) {
						continue;
					}*/
					ctxStk = (LinkedList<Edge>) ctxStk.clone();
					// only enter methods that would potentially bring points-to effects
					Edge cs1 = CallSite.getCallsite(e);
					ctxStk.addFirst(cs1);
				}

				if (Util.pointByGVN(src)) {
					//	        			if (processGVN(src, n2, worklist, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {		        		
					//	    	        		return true;
					//	    	        	} else {
					//AliasGlobalVariables.metGlobalVar = true;
					//System.out.println("Reached global in method :"+src.getMethod());
					return true;
					//	    	         	}
				}


				// jE9pazU8
				if (
						//	        			Util.pointByGVN(src) ||		// TODO: considering gvn might lead to performance hit
						src instanceof StringConstNode ||
						src instanceof ClassConstNode
						) {
					//AliasGlobalVariables.metGlobalVar = true;
					//System.out.println("Reached Stringconst and classconst in method :"+src.getMethod());
					return true;
				}

				// context can be unbalanced, but putField & getField should match
				if (src == n2) {
					if (fldStk.isEmpty()) {	 
						AliasGlobalVariables.nonConservativeAns = true;
						//System.out.println("Actual true src:" + e.src() + " : "+e.tgt() );
						return true;	// alias found
					} else {
						continue;		// invalid path, do NOT add to worklist
					}
				} else if (Util.USE_CACHE) {
					if (fldStk.isEmpty() && ctxStk.isEmpty()) {
						Boolean cache = AliasCache.getCache(src, n2);
						if (null != cache) {
							//System.out.println("Reusing the cached value!");
							if(cache.booleanValue()){
								return true;	 
							}else{
								continue;	   
							}        			
						}
					}	        		
				}

				//		        	if (Util.USE_SUMMARY && e instanceof ExitEdge && Summary.ignoreMethod(mtd)) continue;

				if (Util.USE_SUMMARY && e instanceof ExitEdge && worthApply(mtd, n2Method)) {
					if (applySummary(src, n2, worklist, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {	        			
						return true;
					}
				} else {	        		
					if (e instanceof FieldPTEdge) {
						visitedFldEdges = (HashSet<Pair<FldPair, Integer>>) visitedFldEdges.clone();
						visitedFldEdges.add(new Pair<FldPair, Integer>(FldPair.getPair(e, true), ctxHash));
						//System.out.println("In Feild Edge : "+ e.src() + " : "+e.tgt()+ " : "+e);
					} else {
						visitedCtxEdges = (HashSet<AbstractSPGEdge>) visitedCtxEdges.clone();
						visitedCtxEdges.add(e);
						ctxHash = 3 * ctxHash + e.getReverseId();
						/*if(e instanceof EntryEdge){
							System.out.println("In Entry Edge : "+ e.src() + " : "+e.tgt());
						}else{
							System.out.println("In Exit Edge : "+ e.src() + " : "+e.tgt());
						}*/
					}
					TraverseTuple tt = TraverseTuple.getTuple(src, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash,e, TraverseTuple.IN);
					worklist.add(tt);
				}
			}

			//--- outgoing edges
			for (Iterator<AbstractSPGEdge> outIter = n.getOutgoingEdges(); outIter.hasNext();) {    			
				AbstractSPGEdge e = outIter.next();
				if(e == prevEdge) continue;
				AbstractAllocNode tgt = e.tgt();
				SootMethod mtd = tgt.getMethod();
				Type type = tgt.getType();

				if((type != null) && !(type.isRelevant() || (type instanceof ArrayType && ((ArrayType)type).baseType.isRelevant())
						|| (type instanceof AnySubType) || (type instanceof NullType))){
					/*try{
						System.out.println("Entered inside!! "+type);
					}catch(Exception ex){
						System.out.println("Caught Exception !!");
					}*/
					continue;
				}

				//	    			if (e instanceof EntryEdge && mtd != n2Method && Util.empiricalIgnoreMethod(mtd)) continue;

				// do not clone, but copy on write
				LinkedList<Edge> ctxStk = t.getCtxStk();
				LinkedList<FieldPTEdge> fldStk = t.getFldStk();
				//System.out.println("fld stk : "+fldStk.size());
				HashSet<AbstractSPGEdge> visitedCtxEdges = t.getVisitedCtxEdges();
				HashSet<Pair<FldPair, Integer>> visitedFldEdges = t.getVisitedFldEdges();
				int ctxHash = t.getCtxHash();

				// TGT
				// --- BEGIN COPY-PASTE
				boolean isDup = isDuplicate(e, ctxStk, visitedCtxEdges, visitedFldEdges, ctxHash, false);
				if (isDup) {
					if (!(e instanceof FieldPTEdge))    				
						continue;
				}
				// --- END COPY-PASTE

				//	        		if (addedNodes.contains(tgt)) continue;
				if (tgt == n1) {
					continue;
				}

				try {
					if (tgt.getMethod().toString().equals("<java.lang.Object: void <init>()>")) {
						continue;
					}
				} catch (Exception ex) {
					continue;
				}

				Util.traversedNodes++;
				if (Util.isOutOfBudget()) {
					return true;
				}

				if (e instanceof FieldPTEdge) {
					if (fldStk.isEmpty()) {
						continue;
					} else {
						FieldPTEdge fpt1 = (FieldPTEdge) e;
						FieldPTEdge topEdge = fldStk.peek();        				
						if (topEdge instanceof WildcardEdge) {        					
							WildcardEdge wildcard = (WildcardEdge) topEdge;
							if (!wildcard.match(fpt1.getField())) {
								continue;
							} else {
								wildcard = (WildcardEdge) wildcard.clone();
								wildcard.forward();
								fldStk = (LinkedList<FieldPTEdge>) (fldStk.clone());
								fldStk.removeFirst();
								fldStk.addFirst(wildcard);
							}       					
						} else {
							SootField topFld = topEdge.getField();            				

							if (!Util.sootFieldEquals(fpt1.getField(), topFld)) {
								continue;
							}

							fldStk = (LinkedList<FieldPTEdge>) (fldStk.clone());
							fldStk.removeFirst();
						}        				
					}        			
				} else if (e instanceof EntryEdge) {
					/*if (Util.getEscapableObjects(mtd).size() <= 1 && !Util.getReachables(mtd).contains(n2Method)) {
						continue;
					}
					 */
					ctxStk = (LinkedList<Edge>) ctxStk.clone();
					Edge cs1 = CallSite.getCallsite(e);   			
					ctxStk.addFirst(cs1);
				} else {
					Edge cs1 = CallSite.getCallsite(e);        			

					if (!ctxStk.isEmpty()) {
						ctxStk = (LinkedList<Edge>) ctxStk.clone();
						Edge cs2 = ctxStk.removeFirst();

						if (!cs1.equals(cs2)) {	// matching call site
							// relax the call site constraint for gvn
							// TODO: might be wrong
							/*if ( !(n instanceof SymbolicGlobalObject &&
									cs1.kind().isStatic() &&
									cs2.kind().isStatic() &&
									cs1.getTgt().equals(cs2.getTgt()))) */{

										continue;
									}
						}
					}
				}


				if (Util.pointByGVN(tgt)) {
					//	        			if (processGVN(tgt, n2, worklist, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {
					//			        		return true;
					//			        	} else {
					//AliasGlobalVariables.metGlobalVar = true;
					//System.out.println("Met global : "+tgt.getMethod());
					return true;
					//			        	}
				}

				if (
						//	        			Util.pointByGVN(tgt) ||		// TODO: considering gvn might lead to performance hit
						tgt instanceof StringConstNode ||
						tgt instanceof ClassConstNode) {
					//AliasGlobalVariables.metGlobalVar = true;
					//System.out.println("REached String const and class const in method :"+tgt.getMethod());
					return true;
				} 

				// context can be unbalanced, but putField & getField should match
				if (tgt == n2) {
					if (fldStk.isEmpty()) {
						AliasGlobalVariables.nonConservativeAns = true;
						//System.out.println("Actual true tgt:" + e.src() + " : "+e.tgt() );
						return true;
					} else {
						continue;
					}
				} else if (Util.USE_CACHE) {
					if (fldStk.isEmpty() && ctxStk.isEmpty()) {
						Boolean cache = AliasCache.getCache(tgt, n2);
						if (null != cache) {
							//System.out.println("Reusing the cached value!");
							if(cache.booleanValue()){
								return true;	 
							}else{
								continue;	   
							}        				
						}
					}
				}

				//	        		if (Util.USE_SUMMARY && e instanceof EntryEdge && Summary.ignoreMethod(mtd)) continue;

				if (Util.USE_SUMMARY && e instanceof EntryEdge && worthApply(mtd, n2Method)) {
					if (applySummary(tgt, n2, worklist, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {	        			
						return true;
					}
				} else {
					if (e instanceof FieldPTEdge) {
						visitedFldEdges = (HashSet<Pair<FldPair, Integer>>) visitedFldEdges.clone();
						visitedFldEdges.add(new Pair<FldPair, Integer>(FldPair.getPair(e, false), ctxHash));
						//System.out.println("Out Field Edge : "+ e.src() + " : "+e.tgt() + " : "+e );
					} else {
						visitedCtxEdges = (HashSet<AbstractSPGEdge>) visitedCtxEdges.clone();
						visitedCtxEdges.add(e);
						ctxHash = 3 * ctxHash + e.getId();
						/*if(e instanceof EntryEdge){
							System.out.println("Out Entry Edge : "+ e.src() + " : "+e.tgt());
						}else{
							System.out.println("Out Exit Edge : "+ e.src() + " : "+e.tgt());
						}*/
					}
					TraverseTuple tt = TraverseTuple.getTuple(tgt, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash, e, TraverseTuple.OUT);
					worklist.add(tt);	
				}    		
			}



			//	    		if (traversedNodes >= Util.SPA_BUDGET_NODES) {
			//	    			return true;
			//	    		}
		}    	
		AliasGlobalVariables.nonConservativeAns = true;
		//System.out.println("Actual false:");
		return false;
	}

	public boolean VC(AbstractAllocNode n1, AbstractAllocNode n2) {
		if (n1 == n2) {
			return true;
			//	    	} else if (n1 instanceof AllocNode && n2 instanceof AllocNode) {
		} else if (!(n1 instanceof SymbolicObject || n2 instanceof SymbolicObject)) {
			return false;
		} else if (Util.pointByGVN(n1) || Util.pointByGVN(n2)) {
			return true;
		}

		if (Util.USE_CACHE) {
			Boolean cacheResult = AliasCache.getCache(n1, n2);
			if (null != cacheResult) {
				return cacheResult.booleanValue();        		
			}
		}    	

		Util.traversedNodes = 0;

		LinkedList<TraverseTuple> worklist = new LinkedList<TraverseTuple>();
		//	    	if (Util.pointByGVN(n1)) {
		//	    		if (processGVN(n1, n2, worklist, new LinkedList<FieldPTEdge>(), new HashSet<AbstractSPGEdge>(),
		//	    	    	new HashSet<Pair<FldPair, Integer>>(), 0)) {    		
		//	    	    		return true;
		//	    	    }
		//	    	} else {
		TraverseTuple t = TraverseTuple.getTuple(n1, new LinkedList<Edge>(), new LinkedList<FieldPTEdge>(),
				new HashSet<AbstractSPGEdge>(), new HashSet<Pair<FldPair, Integer>>(), 0, null, TraverseTuple.NONE);
		worklist.add(t);
		//	    	}

		SootMethod n2Method = n2.getMethod();
		while (!worklist.isEmpty()) {
			t = worklist.removeFirst();
			AbstractAllocNode n = t.getNode();
			AbstractSPGEdge prevEdge = t.getPrevEdge();


			//--- incoming edges
			for (Iterator<AbstractSPGEdge> inIter = n.getIncomingEdges(); inIter.hasNext();) {        		
				AbstractSPGEdge e = inIter.next();
				if(e == prevEdge) continue;
				AbstractAllocNode src = e.src();
				SootMethod mtd = src.getMethod();
				Type type = src.getType();

				//System.out.println(n.getMethod());

				//	    			if (e instanceof ExitEdge && mtd != n2Method && Util.empiricalIgnoreMethod(mtd)) continue;

				// do not clone, but copy on write
				LinkedList<Edge> ctxStk = t.getCtxStk();
				LinkedList<FieldPTEdge> fldStk = t.getFldStk();
				//	System.out.println("fld stk : "+fldStk.size());
				HashSet<AbstractSPGEdge> visitedCtxEdges = t.getVisitedCtxEdges();
				HashSet<Pair<FldPair, Integer>> visitedFldEdges = t.getVisitedFldEdges();
				int ctxHash = t.getCtxHash();        		

				// SRC
				// --- BEGIN COPY-PASTE
				boolean isDup = isDuplicate(e, ctxStk, visitedCtxEdges, visitedFldEdges, ctxHash, true);
				if (isDup) {
					// we should ignore the case when the top of stack is already wildcard
					// and the e is an edge on that cycle
					if ((e instanceof FieldPTEdge) && !(isOnCycle(e, fldStk))) {
						// detect cycles
						ArrayList<FieldPTEdge> cycle = new ArrayList<FieldPTEdge>();    				
						fldStk = (LinkedList<FieldPTEdge>) fldStk.clone();
						int pos = 0;
						while (!fldStk.isEmpty()) {
							FieldPTEdge fldEdge = fldStk.removeFirst();
							// FIXME: assumed to be too expensive, return context-insensitive instead
							if (fldEdge instanceof WildcardEdge) { 
								//System.out.println("Conservative result!!");
								return true;
							}

							cycle.add(fldEdge);   					
							WildcardEdge wildcard = new WildcardEdge(cycle, pos++);
							LinkedList<FieldPTEdge> fldStkClone = (LinkedList<FieldPTEdge>)(fldStk.clone());
							fldStkClone.addFirst(wildcard);
							TraverseTuple tt = TraverseTuple.getTuple(fldEdge.tgt(), ctxStk, fldStkClone, visitedCtxEdges, visitedFldEdges, ctxHash, e, TraverseTuple.NONE);
							worklist.add(tt);
							if (Util.sootFieldEquals(fldEdge.getField(), ((FieldPTEdge)e).getField())) {    					
								break;
							}
						}
					}

					if(!((e instanceof EntryEdge) || (e instanceof ExitEdge))){
						continue;
					}
				}
				// --- END COPY-PASTE

				if (src == n1) {
					continue;
				}

				Util.traversedNodes++;
				if (Util.isOutOfBudget()) {
					return true;
				}

				if (e instanceof FieldPTEdge) {
					fldStk = (LinkedList<FieldPTEdge>) fldStk.clone();
					fldStk.addFirst(((FieldPTEdge) e));        			
				} else if (e instanceof EntryEdge) {
					Edge cs1 = CallSite.getCallsite(e);

					if (!ctxStk.isEmpty()) {
						ctxStk = (LinkedList<Edge>) ctxStk.clone();
						Edge cs2 = ctxStk.removeFirst();            			

						if (!cs1.equals(cs2)) {	// matching call site
							// relax the call site constraint for gvn
							// TODO: might be wrong
							/*if ( !(n instanceof SymbolicGlobalObject &&
									cs1.kind().isStatic() &&
									cs2.kind().isStatic() &&
									cs1.getTgt().equals(cs2.getTgt())))*/ {

										continue;
									}
						}
					}
				} else {
					/*if (Util.getEscapableObjects(mtd).size() <= 1 && !Util.getReachables(mtd).contains(n2Method)) {
						continue;
					}*/
					//if(ctxStk.isEmpty()){
					if((prevEdge != null) && (prevEdge instanceof ExitEdge) && (t.getDirection() ==  TraverseTuple.OUT)){
						continue;
					}

					ctxStk = (LinkedList<Edge>) ctxStk.clone();
					// only enter methods that would potentially bring points-to effects
					Edge cs1 = CallSite.getCallsite(e);
					ctxStk.addFirst(cs1);
				}


				if (Util.pointByGVN(src)) {
					//	        			if (processGVN(src, n2, worklist, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {		        		
					//	    	        		return true;
					//	    	        	} else {
					//AliasGlobalVariables.metGlobalVar = true;
					//System.out.println("Reached global in method :"+src.getMethod());
					return true;
					//	    	         	}
				}


				// jE9pazU8
				if (
						//	        			Util.pointByGVN(src) ||		// TODO: considering gvn might lead to performance hit
						src instanceof StringConstNode ||
						src instanceof ClassConstNode
						) {
					//AliasGlobalVariables.metGlobalVar = true;
					//System.out.println("Reached Stringconst and classconst in method :"+src.getMethod());
					return true;
				}


				// context can be unbalanced, but putField & getField should match
				if (src == n2) {
					if (fldStk.isEmpty()) {	   
						AliasGlobalVariables.nonConservativeAns = true;
						//System.out.println("Actual true:");
						return true;	// alias found
					} else {
						continue;		// invalid path, do NOT add to worklist
					}
				} else if (Util.USE_CACHE) {
					if (fldStk.isEmpty() && ctxStk.isEmpty()) {
						Boolean cache = AliasCache.getCache(src, n2);
						if (null != cache) {
							//System.out.println("Reusing the cached value!");
							if(cache.booleanValue()){
								return true;	 
							}else{
								continue;	   
							}        			
						}
					}	        		
				}

				//		        	if (Util.USE_SUMMARY && e instanceof ExitEdge && Summary.ignoreMethod(mtd)) continue;

				if (Util.USE_SUMMARY && e instanceof ExitEdge && worthApply(mtd, n2Method)) {
					if (applySummary(src, n2, worklist, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {	        			
						return true;
					}
				} else {	        		
					if (e instanceof FieldPTEdge) {
						visitedFldEdges = (HashSet<Pair<FldPair, Integer>>) visitedFldEdges.clone();
						visitedFldEdges.add(new Pair<FldPair, Integer>(FldPair.getPair(e, true), ctxHash));

						/*if((e.src().getType() == null || !(e.src().getType() instanceof AnySubType)) && 
								(e.tgt().getType() == null || !(e.tgt().getType() instanceof AnySubType))) {
							System.out.println("In Feild Edge : "+ e.src() + " : "+e.tgt()+ " : "+e);
						}
						else
							System.out.println("Any sub type.. In Field Edge In");*/
					} else {
						visitedCtxEdges = (HashSet<AbstractSPGEdge>) visitedCtxEdges.clone();
						visitedCtxEdges.add(e);
						ctxHash = 3 * ctxHash + e.getReverseId();
						/*if((e.src().getType() == null || !(e.src().getType() instanceof AnySubType)) && 
								(e.tgt().getType() == null || !(e.tgt().getType() instanceof AnySubType))) {
							if(e instanceof EntryEdge){
								System.out.println("In Entry Edge : "+ e.src() + " : "+e.tgt());
							}else{
								System.out.println("In Exit Edge : "+ e.src() + " : "+e.tgt());
							}
						}
						else
							System.out.println("Any sub type.. Exit Entry In");*/

					}
					TraverseTuple tt = TraverseTuple.getTuple(src, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash,e, TraverseTuple.IN);
					worklist.add(tt);
				}
			}

			//--- outgoing edges
			for (Iterator<AbstractSPGEdge> outIter = n.getOutgoingEdges(); outIter.hasNext();) {    			
				AbstractSPGEdge e = outIter.next();
				if(e == prevEdge) continue;
				AbstractAllocNode tgt = e.tgt();
				SootMethod mtd = tgt.getMethod();

				//	    			if (e instanceof EntryEdge && mtd != n2Method && Util.empiricalIgnoreMethod(mtd)) continue;

				// do not clone, but copy on write
				LinkedList<Edge> ctxStk = t.getCtxStk();
				LinkedList<FieldPTEdge> fldStk = t.getFldStk();
				//System.out.println("fld stk : "+fldStk.size());
				HashSet<AbstractSPGEdge> visitedCtxEdges = t.getVisitedCtxEdges();
				HashSet<Pair<FldPair, Integer>> visitedFldEdges = t.getVisitedFldEdges();
				int ctxHash = t.getCtxHash();

				// TGT
				// --- BEGIN COPY-PASTE
				boolean isDup = isDuplicate(e, ctxStk, visitedCtxEdges, visitedFldEdges, ctxHash, false);
				if (isDup) {
					if (!(e instanceof FieldPTEdge))    				
						continue;
				}
				// --- END COPY-PASTE

				//	        		if (addedNodes.contains(tgt)) continue;
				if (tgt == n1) {
					continue;
				}

				try {
					if (tgt.getMethod().toString().equals("<java.lang.Object: void <init>()>")) {
						continue;
					}
				} catch (Exception ex) {
					continue;
				}

				Util.traversedNodes++;
				if (Util.isOutOfBudget()) {
					return true;
				}

				if (e instanceof FieldPTEdge) {
					if (fldStk.isEmpty()) {
						continue;
					} else {
						FieldPTEdge fpt1 = (FieldPTEdge) e;
						FieldPTEdge topEdge = fldStk.peek();        				
						if (topEdge instanceof WildcardEdge) {        					
							WildcardEdge wildcard = (WildcardEdge) topEdge;
							if (!wildcard.match(fpt1.getField())) {
								continue;
							} else {
								wildcard = (WildcardEdge) wildcard.clone();
								wildcard.forward();
								fldStk = (LinkedList<FieldPTEdge>) (fldStk.clone());
								fldStk.removeFirst();
								fldStk.addFirst(wildcard);
							}       					
						} else {
							SootField topFld = topEdge.getField();            				

							if (!Util.sootFieldEquals(fpt1.getField(), topFld)) {
								continue;
							}

							fldStk = (LinkedList<FieldPTEdge>) (fldStk.clone());
							fldStk.removeFirst();
						}        				
					}        			
				} else if (e instanceof EntryEdge) {
					/*if (Util.getEscapableObjects(mtd).size() <= 1 && !Util.getReachables(mtd).contains(n2Method)) {
						continue;
					}
					 */
					//	if(ctxStk.isEmpty()){
					if((prevEdge != null) && (prevEdge instanceof EntryEdge) && (((EntryEdge)prevEdge).getVirtualID() == ((EntryEdge)e).getVirtualID())
							&& (t.getDirection() ==  TraverseTuple.IN)){
						continue;
					}
					//}

					ctxStk = (LinkedList<Edge>) ctxStk.clone();
					Edge cs1 = CallSite.getCallsite(e);   			
					ctxStk.addFirst(cs1);
				} else {
					Edge cs1 = CallSite.getCallsite(e);        			

					if (!ctxStk.isEmpty()) {
						ctxStk = (LinkedList<Edge>) ctxStk.clone();
						Edge cs2 = ctxStk.removeFirst();

						if (!cs1.equals(cs2)) {	// matching call site
							// relax the call site constraint for gvn
							// TODO: might be wrong
							/*if ( !(n instanceof SymbolicGlobalObject &&
									cs1.kind().isStatic() &&
									cs2.kind().isStatic() &&
									cs1.getTgt().equals(cs2.getTgt()))) */{

										continue;
									}
						}
					}
				}

				if (Util.pointByGVN(tgt)) {
					//	        			if (processGVN(tgt, n2, worklist, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {
					//			        		return true;
					//			        	} else {
					//AliasGlobalVariables.metGlobalVar = true;
					//System.out.println("Met global : "+tgt.getMethod());
					return true;
					//			        	}
				}

				if (
						//	        			Util.pointByGVN(tgt) ||		// TODO: considering gvn might lead to performance hit
						tgt instanceof StringConstNode ||
						tgt instanceof ClassConstNode) {
					//AliasGlobalVariables.metGlobalVar = true;
					//	System.out.println("REached String const and class const in method :"+tgt.getMethod());
					return true;
				} 

				// context can be unbalanced, but putField & getField should match
				if (tgt == n2) {
					if (fldStk.isEmpty()) {
						AliasGlobalVariables.nonConservativeAns = true;
						//System.out.println("Actual true:");
						return true;
					} else {
						continue;
					}
				} else if (Util.USE_CACHE) {
					if (fldStk.isEmpty() && ctxStk.isEmpty()) {
						Boolean cache = AliasCache.getCache(tgt, n2);
						if (null != cache) {
							//System.out.println("Reusing the cached value!");
							if(cache.booleanValue()){
								return true;	 
							}else{
								continue;	   
							}        				
						}
					}
				}

				//	        		if (Util.USE_SUMMARY && e instanceof EntryEdge && Summary.ignoreMethod(mtd)) continue;

				if (Util.USE_SUMMARY && e instanceof EntryEdge && worthApply(mtd, n2Method)) {
					if (applySummary(tgt, n2, worklist, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {	        			
						return true;
					}
				} else {
					if (e instanceof FieldPTEdge) {
						visitedFldEdges = (HashSet<Pair<FldPair, Integer>>) visitedFldEdges.clone();
						visitedFldEdges.add(new Pair<FldPair, Integer>(FldPair.getPair(e, false), ctxHash));
						/*if((e.src().getType() == null || !(e.src().getType() instanceof AnySubType)) && 
								(e.tgt().getType() == null || !(e.tgt().getType() instanceof AnySubType))) {
							System.out.println("Out Field Edge : "+ e.src() + " : "+e.tgt() + " : "+e );
						}
						else
							System.out.println("Any sub type.. Out Field");*/
					} else {
						visitedCtxEdges = (HashSet<AbstractSPGEdge>) visitedCtxEdges.clone();
						visitedCtxEdges.add(e);
						ctxHash = 3 * ctxHash + e.getId();
					}
					TraverseTuple tt = TraverseTuple.getTuple(tgt, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash, e, TraverseTuple.OUT);
					worklist.add(tt);	
				}    		
			}



			//	    		if (traversedNodes >= Util.SPA_BUDGET_NODES) {
			//	    			return true;
			//	    		}
		}    	

		AliasGlobalVariables.nonConservativeAns = true;
		//System.out.println("Actual false:");
		return false;
	}

	@SuppressWarnings("unchecked")
	public boolean smart(AbstractAllocNode n1, AbstractAllocNode n2) {

		if (n1 == n2) {
			return true;
			//	    	} else if (n1 instanceof AllocNode && n2 instanceof AllocNode) {
		} else if (!(n1 instanceof SymbolicObject || n2 instanceof SymbolicObject)) {
			return false;
		} else if (Util.pointByGVN(n1) || Util.pointByGVN(n2)) {
			return true;
		}

		if (Util.USE_CACHE) {
			Boolean cacheResult = AliasCache.getCache(n1, n2);
			if (null != cacheResult) {
				return cacheResult.booleanValue();        		
			}
		}    	

		Util.traversedNodes = 0;

		LinkedList<TraverseTuple> worklist = new LinkedList<TraverseTuple>();
		//	    	if (Util.pointByGVN(n1)) {
		//	    		if (processGVN(n1, n2, worklist, new LinkedList<FieldPTEdge>(), new HashSet<AbstractSPGEdge>(),
		//	    	    	new HashSet<Pair<FldPair, Integer>>(), 0)) {    		
		//	    	    		return true;
		//	    	    }
		//	    	} else {
		TraverseTuple t = TraverseTuple.getTuple(n1, new LinkedList<Edge>(), new LinkedList<FieldPTEdge>(),
				new HashSet<AbstractSPGEdge>(), new HashSet<Pair<FldPair, Integer>>(), 0, null, TraverseTuple.NONE);
		worklist.add(t);
		//	    	}

		SootMethod n2Method = n2.getMethod();
		while (!worklist.isEmpty()) {
			t = worklist.removeFirst();
			AbstractAllocNode n = t.getNode();
			AbstractSPGEdge prevEdge = t.getPrevEdge();

			//--- incoming edges
			for (Iterator<AbstractSPGEdge> inIter = n.getIncomingEdges(); inIter.hasNext();) {        		
				AbstractSPGEdge e = inIter.next();
				if(e == prevEdge) continue;
				AbstractAllocNode src = e.src();
				SootMethod mtd = src.getMethod();
				Type type = src.getType();

				if((type != null) && !(type.isRelevant() || (type instanceof ArrayType && ((ArrayType)type).baseType.isRelevant())
						|| (type instanceof AnySubType) || (type instanceof NullType))){
					continue;
				}
				//System.out.println(n.getMethod());

				//	    			if (e instanceof ExitEdge && mtd != n2Method && Util.empiricalIgnoreMethod(mtd)) continue;

				// do not clone, but copy on write
				LinkedList<Edge> ctxStk = t.getCtxStk();
				LinkedList<FieldPTEdge> fldStk = t.getFldStk();
				//	System.out.println("fld stk : "+fldStk.size());
				HashSet<AbstractSPGEdge> visitedCtxEdges = t.getVisitedCtxEdges();
				HashSet<Pair<FldPair, Integer>> visitedFldEdges = t.getVisitedFldEdges();
				int ctxHash = t.getCtxHash();        		

				// SRC
				// --- BEGIN COPY-PASTE
				boolean isDup = isDuplicate(e, ctxStk, visitedCtxEdges, visitedFldEdges, ctxHash, true);
				if (isDup) {
					// we should ignore the case when the top of stack is already wildcard
					// and the e is an edge on that cycle
					if ((e instanceof FieldPTEdge) && !(isOnCycle(e, fldStk))) {
						// detect cycles
						ArrayList<FieldPTEdge> cycle = new ArrayList<FieldPTEdge>();    				
						fldStk = (LinkedList<FieldPTEdge>) fldStk.clone();
						int pos = 0;
						while (!fldStk.isEmpty()) {
							FieldPTEdge fldEdge = fldStk.removeFirst();
							// FIXME: assumed to be too expensive, return context-insensitive instead
							if (fldEdge instanceof WildcardEdge) { 
								//	System.out.println("Conservative result!!");
								return true;
							}

							cycle.add(fldEdge);   					
							WildcardEdge wildcard = new WildcardEdge(cycle, pos++);
							LinkedList<FieldPTEdge> fldStkClone = (LinkedList<FieldPTEdge>)(fldStk.clone());
							fldStkClone.addFirst(wildcard);
							TraverseTuple tt = TraverseTuple.getTuple(fldEdge.tgt(), ctxStk, fldStkClone, visitedCtxEdges, visitedFldEdges, ctxHash, e, TraverseTuple.NONE);
							worklist.add(tt);
							if (Util.sootFieldEquals(fldEdge.getField(), ((FieldPTEdge)e).getField())) {    					
								break;
							}
						}
					}

					if(!((e instanceof EntryEdge) || (e instanceof ExitEdge))){
						continue;
					}
				}
				// --- END COPY-PASTE

				if (src == n1) {
					continue;
				}

				Util.traversedNodes++;
				if (Util.isOutOfBudget()) {
					return true;
				}

				if (e instanceof FieldPTEdge) {
					fldStk = (LinkedList<FieldPTEdge>) fldStk.clone();
					fldStk.addFirst(((FieldPTEdge) e));        			
				} else if (e instanceof EntryEdge) {
					Edge cs1 = CallSite.getCallsite(e);

					if (!ctxStk.isEmpty()) {
						ctxStk = (LinkedList<Edge>) ctxStk.clone();
						Edge cs2 = ctxStk.removeFirst();            			

						if (!cs1.equals(cs2)) {	// matching call site
							// relax the call site constraint for gvn
							// TODO: might be wrong
							/*if ( !(n instanceof SymbolicGlobalObject &&
									cs1.kind().isStatic() &&
									cs2.kind().isStatic() &&
									cs1.getTgt().equals(cs2.getTgt())))*/ {

										continue;
									}
						}
					}
				} else {
					/*if (Util.getEscapableObjects(mtd).size() <= 1 && !Util.getReachables(mtd).contains(n2Method)) {
						continue;
					}*/
					//	if(ctxStk.isEmpty()){
					if((prevEdge != null) && (prevEdge instanceof ExitEdge) && (t.getDirection() ==  TraverseTuple.OUT)){
						continue;
					}
					//	}
					ctxStk = (LinkedList<Edge>) ctxStk.clone();
					// only enter methods that would potentially bring points-to effects
					Edge cs1 = CallSite.getCallsite(e);
					ctxStk.addFirst(cs1);
				}

				if (Util.pointByGVN(src)) {
					//	        			if (processGVN(src, n2, worklist, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {		        		
					//	    	        		return true;
					//	    	        	} else {
					//AliasGlobalVariables.metGlobalVar = true;
					//System.out.println("Reached global in method :"+src.getMethod());
					return true;
					//	    	         	}
				}


				// jE9pazU8
				if (
						//	        			Util.pointByGVN(src) ||		// TODO: considering gvn might lead to performance hit
						src instanceof StringConstNode ||
						src instanceof ClassConstNode
						) {
					//AliasGlobalVariables.metGlobalVar = true;
					//System.out.println("Reached Stringconst and classconst in method :"+src.getMethod());
					return true;
				}

				// context can be unbalanced, but putField & getField should match
				if (src == n2) {
					if (fldStk.isEmpty()) {	
						AliasGlobalVariables.nonConservativeAns = true;
						//System.out.println("Actual true:");
						/*if(ctxStk.isEmpty()){
							System.out.println("Added one");
							AliasGlobalVariables.aliasesWthEmptyCallStk.put(n1, n2);
						}*/
						return true;	// alias found
					} else {
						continue;		// invalid path, do NOT add to worklist
					}
				} else if (Util.USE_CACHE) {
					if (fldStk.isEmpty() && ctxStk.isEmpty()) {
						Boolean cache = AliasCache.getCache(src, n2);
						if (null != cache) {
							//System.out.println("Reusing the cached value!");
							if(cache.booleanValue()){
								return true;	 
							}else{
								continue;	   
							}        			
						}
					}	        		
				}

				//		        	if (Util.USE_SUMMARY && e instanceof ExitEdge && Summary.ignoreMethod(mtd)) continue;

				if (Util.USE_SUMMARY && e instanceof ExitEdge && worthApply(mtd, n2Method)) {
					if (applySummary(src, n2, worklist, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {	        			
						return true;
					}
				} else {	        		
					if (e instanceof FieldPTEdge) {
						visitedFldEdges = (HashSet<Pair<FldPair, Integer>>) visitedFldEdges.clone();
						visitedFldEdges.add(new Pair<FldPair, Integer>(FldPair.getPair(e, true), ctxHash));

					} else {
						visitedCtxEdges = (HashSet<AbstractSPGEdge>) visitedCtxEdges.clone();
						visitedCtxEdges.add(e);
						ctxHash = 3 * ctxHash + e.getReverseId();

					}
					TraverseTuple tt = TraverseTuple.getTuple(src, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash,e, TraverseTuple.IN);
					worklist.add(tt);
				}
			}

			//--- outgoing edges
			for (Iterator<AbstractSPGEdge> outIter = n.getOutgoingEdges(); outIter.hasNext();) {    			
				AbstractSPGEdge e = outIter.next();
				if(e == prevEdge) continue;
				AbstractAllocNode tgt = e.tgt();
				SootMethod mtd = tgt.getMethod();
				Type type = tgt.getType();

				if((type != null) && !(type.isRelevant() || (type instanceof ArrayType && ((ArrayType)type).baseType.isRelevant())
						|| (type instanceof AnySubType) || (type instanceof NullType))){
					continue;
				}

				//	    			if (e instanceof EntryEdge && mtd != n2Method && Util.empiricalIgnoreMethod(mtd)) continue;

				// do not clone, but copy on write
				LinkedList<Edge> ctxStk = t.getCtxStk();
				LinkedList<FieldPTEdge> fldStk = t.getFldStk();
				//System.out.println("fld stk : "+fldStk.size());
				HashSet<AbstractSPGEdge> visitedCtxEdges = t.getVisitedCtxEdges();
				HashSet<Pair<FldPair, Integer>> visitedFldEdges = t.getVisitedFldEdges();
				int ctxHash = t.getCtxHash();

				// TGT
				// --- BEGIN COPY-PASTE
				boolean isDup = isDuplicate(e, ctxStk, visitedCtxEdges, visitedFldEdges, ctxHash, false);
				if (isDup) {
					if (!(e instanceof FieldPTEdge))    				
						continue;
				}
				// --- END COPY-PASTE

				//	        		if (addedNodes.contains(tgt)) continue;
				if (tgt == n1) {
					continue;
				}

				try {
					if (tgt.getMethod().toString().equals("<java.lang.Object: void <init>()>")) {
						continue;
					}
				} catch (Exception ex) {
					continue;
				}

				Util.traversedNodes++;
				if (Util.isOutOfBudget()) {
					return true;
				}

				if (e instanceof FieldPTEdge) {
					if (fldStk.isEmpty()) {
						continue;
					} else {
						FieldPTEdge fpt1 = (FieldPTEdge) e;
						FieldPTEdge topEdge = fldStk.peek();        				
						if (topEdge instanceof WildcardEdge) {        					
							WildcardEdge wildcard = (WildcardEdge) topEdge;
							if (!wildcard.match(fpt1.getField())) {
								continue;
							} else {
								wildcard = (WildcardEdge) wildcard.clone();
								wildcard.forward();
								fldStk = (LinkedList<FieldPTEdge>) (fldStk.clone());
								fldStk.removeFirst();
								fldStk.addFirst(wildcard);
							}       					
						} else {
							SootField topFld = topEdge.getField();            				

							if (!Util.sootFieldEquals(fpt1.getField(), topFld)) {
								continue;
							}

							fldStk = (LinkedList<FieldPTEdge>) (fldStk.clone());
							fldStk.removeFirst();
						}        				
					}        			
				} else if (e instanceof EntryEdge) {
					/*if (Util.getEscapableObjects(mtd).size() <= 1 && !Util.getReachables(mtd).contains(n2Method)) {
						continue;
					}
					 */
					if((prevEdge != null) && (prevEdge instanceof EntryEdge) && (((EntryEdge)prevEdge).getVirtualID() == ((EntryEdge)e).getVirtualID())
							&& (t.getDirection() ==  TraverseTuple.IN)){

						continue;
					}
					ctxStk = (LinkedList<Edge>) ctxStk.clone();
					Edge cs1 = CallSite.getCallsite(e);   			
					ctxStk.addFirst(cs1);
				} else {
					Edge cs1 = CallSite.getCallsite(e);        			

					if (!ctxStk.isEmpty()) {
						ctxStk = (LinkedList<Edge>) ctxStk.clone();
						Edge cs2 = ctxStk.removeFirst();

						if (!cs1.equals(cs2)) {	// matching call site
							// relax the call site constraint for gvn
							// TODO: might be wrong
							/*if ( !(n instanceof SymbolicGlobalObject &&
									cs1.kind().isStatic() &&
									cs2.kind().isStatic() &&
									cs1.getTgt().equals(cs2.getTgt()))) */{

										continue;
									}
						}
					}
				}

				if (Util.pointByGVN(tgt)) {
					//	        			if (processGVN(tgt, n2, worklist, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {
					//			        		return true;
					//			        	} else {
					//AliasGlobalVariables.metGlobalVar = true;
					//	System.out.println("Met global : "+tgt.getMethod());
					return true;
					//			        	}
				}

				if (
						//	        			Util.pointByGVN(tgt) ||		// TODO: considering gvn might lead to performance hit
						tgt instanceof StringConstNode ||
						tgt instanceof ClassConstNode) {
					//AliasGlobalVariables.metGlobalVar = true;
					//	System.out.println("REached String const and class const in method :"+tgt.getMethod());
					return true;
				} 

				// context can be unbalanced, but putField & getField should match
				if (tgt == n2) {
					if (fldStk.isEmpty()) {
						AliasGlobalVariables.nonConservativeAns = true;
						//System.out.println("Actual true:");
						return true;
					} else {
						continue;
					}
				} else if (Util.USE_CACHE) {
					if (fldStk.isEmpty() && ctxStk.isEmpty()) {
						Boolean cache = AliasCache.getCache(tgt, n2);
						if (null != cache) {
							//System.out.println("Reusing the cached value!");
							if(cache.booleanValue()){
								return true;	 
							}else{
								continue;	   
							}        				
						}
					}
				}

				//	        		if (Util.USE_SUMMARY && e instanceof EntryEdge && Summary.ignoreMethod(mtd)) continue;

				if (Util.USE_SUMMARY && e instanceof EntryEdge && worthApply(mtd, n2Method)) {
					if (applySummary(tgt, n2, worklist, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {	        			
						return true;
					}
				} else {
					if (e instanceof FieldPTEdge) {
						visitedFldEdges = (HashSet<Pair<FldPair, Integer>>) visitedFldEdges.clone();
						visitedFldEdges.add(new Pair<FldPair, Integer>(FldPair.getPair(e, false), ctxHash));
					} else {
						visitedCtxEdges = (HashSet<AbstractSPGEdge>) visitedCtxEdges.clone();
						visitedCtxEdges.add(e);
						ctxHash = 3 * ctxHash + e.getId();
					}
					TraverseTuple tt = TraverseTuple.getTuple(tgt, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash, e, TraverseTuple.OUT);
					worklist.add(tt);	
				}    		
			}



			//	    		if (traversedNodes >= Util.SPA_BUDGET_NODES) {
			//	    			return true;
			//	    		}
		}    	
		AliasGlobalVariables.nonConservativeAns = true;
		//System.out.println("Actual false:");
		return false;
	}

	@SuppressWarnings("unchecked")
	public boolean isOnCycle(AbstractSPGEdge e, LinkedList<FieldPTEdge> fldStk) {
		FieldPTEdge top = fldStk.peek();
		if (top instanceof WildcardEdge) {
			WildcardEdge wildcard = (WildcardEdge)top;
			for (AbstractSPGEdge edge : wildcard.getCycleEdges()) {
				if (e == edge) return true;
			}
		}

		return false;
	}

	//   
	//	private boolean worthApplying(AbstractAllocNode n) {
	//    	return iterSize(n.getIncomingEdges()) + iterSize(n.getOutgoingEdges()) > 20;
	//	}
	
	public boolean applySummary_lessclone(AbstractAllocNode head, AbstractAllocNode target, LinkedList<TraverseTupleNew> worklist,
			LinkedList<Edge> ctxStk, LinkedList<FieldPTEdge> fldStk, HashSet<AbstractSPGEdge> visitedCtxEdges,
			HashSet<Pair<FldPair, Integer>> visitedFldEdges, int ctxHash) {
		System.out.println("Summ: "+ctxStk + " : "+fldStk+" : "+worklist);
		//    	AbstractAllocNode cur = head;
		SootMethod mtd = head.getMethod(); 
		//System.out.println("Summary started : "+mtd);
		//Jyothi: head can be a return node of a method, or a parameter node of a method (accessed as a target to an actual parameter at a callsite of a method). 
		//In either case, we are entering into a new method from the current method. Hence we get its summary and apply it.

		// TODO: possible bottleneck
		//    	HashSet<SootMethod> rm = Util.getReachables(mtd);
		//    	if (rm.contains(target.getMethod())) {
		//    		TraverseTuple q = TraverseTuple.getTuple(head, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash);
		//        	worklist.add(q);
		//        	return false;
		//    	}
		// END

		//    	long start = System.currentTimeMillis();
		Summary summ = null;
		try {

			summ = Summary.getSummary(mtd);
			if (Util.DEBUG_SUMMARY) {
				System.out.println("[summary.pass] " + mtd);
			}
		} catch (OutOfBudgetException e) {
			if (Util.DEBUG_SUMMARY) {
				System.out.println("[summary.fail] " + mtd);
			}
			return true;
		}
		//System.out.println("Out of budget exception occ -- Summary : "+mtd);
		/*	Summary.numSumMtdsP++;
		Summary.usage.put(mtd, Summary.usage.get(mtd).intValue()+1);*/

		//		Summary.totalComputeTime += (System.currentTimeMillis() - start);

		// if the summary is empty, nothing is applied.
		// FIXME: this might not be the right thing to do
		if (summ == Summary.emptySummary) return false;

		//System.out.println("Has non-empty Summary : "+mtd);

		Collection<SummaryRecord> records = summ.startsWith(head);
		if (records.isEmpty()) {
			return false;
		}
		// with non-empty summary, let's apply it
		for (SummaryRecord rec : records) {
			// grab the end node
			AbstractAllocNode cur = head;
			AbstractAllocNode end = rec.end();
			if (cur == end) continue;

			// every time a new summary record is about to apply,
			// we need to copy current stack from the same quad!

			// clones the current stacks
			LinkedList<Edge> summCtxStk = (LinkedList<Edge>)(ctxStk.clone());
			LinkedList<FieldPTEdge> summFldStk = (LinkedList<FieldPTEdge>)(fldStk.clone());
			HashSet<AbstractSPGEdge> summVisitedCtxEdges = (HashSet<AbstractSPGEdge>)(visitedCtxEdges.clone());
			HashSet<Pair<FldPair, Integer>> summVisitedFldEdges = (HashSet<Pair<FldPair, Integer>>)(visitedFldEdges.clone());
			int summCtxHash = ctxHash;    		

			//			my_assert(rec.begin() == head, "begin != head");

			//			AbstractSPGEdge edge = null;
			boolean valid = true;
			for (NumberedObject summObj : rec.getSeqSumm()) {
				Util.traversedNodes++;
				if (Util.isOutOfBudget()) {
					return true;
				}

				if (summObj instanceof CtxPair) {
					CtxPair cp = (CtxPair) summObj;
					AbstractSPGEdge edge = cp.getEdge();

					if (summVisitedCtxEdges.contains(edge)) {
						valid = false;
						break;
					}	        	        		

					int action = cp.getAction();
					Edge cs2 = cp.getCallsite();
					if (action == CtxPair.PUSH) {
						summCtxStk.addFirst(cs2);
					} else {	// action == POP
						if (!summCtxStk.isEmpty()) {
							if (cs2 != summCtxStk.removeFirst()) {
								valid = false;
								break;
							}
						} // if empty, ignore the edge
					}				

					if (edge.src() == cur) {
						cur = edge.tgt();
					} else {
						cur = edge.src();
					}
					if (cur == target) {
						if (summFldStk.isEmpty()) {
							return true;
						} else {
							valid = false;
							break;
						}
					}
					// the current edge is valid, so add it
					summVisitedCtxEdges.add(edge);
					if (action == CtxPair.PUSH) {
						if (edge instanceof EntryEdge) {	// entry
							summCtxHash = 3 * summCtxHash + edge.getId();
						} else {	// inverse exit
							summCtxHash = 3 * summCtxHash + edge.getReverseId();
						}
					} else {
						if (edge instanceof EntryEdge) {	// inverse entry
							summCtxHash = 3 * summCtxHash + edge.getReverseId();
						} else {	// exit
							summCtxHash = 3 * summCtxHash + edge.getId();
						}
					}
				} else {
					FldPair fp = (FldPair) summObj;

					AbstractSPGEdge edge = fp.getEdge();

					// check if duplicate
					boolean isDup = false;
					for (Pair<FldPair, Integer> fldPair : summVisitedFldEdges) {
						FldPair visitedFP = fldPair.first;
						if ((edge == visitedFP.getEdge()) && (fp.isBar() == visitedFP.isBar()) && (fldPair.second == summCtxHash)) {
							isDup = true;
							break;							
						}
					}
					if (isDup) {
						valid = false;
						break;
					}

					if (fp.isBar()) {
						summFldStk.addFirst(((FieldPTEdge)edge));
					} else {
						if (summFldStk.isEmpty()) {
							valid = false;
							break;
						} else {
							SootField topFld = summFldStk.removeFirst().getField();

							FieldPTEdge fpt1 = (FieldPTEdge) edge;        								

							if (!Util.sootFieldEquals(fpt1.getField(), topFld)) {
								valid = false;
								break;
							}
						}
					}

					if (edge.src() == cur) {
						cur = edge.tgt();
					} else {
						cur = edge.src();
					}
					if (cur == target) {
						if (summFldStk.isEmpty()) {
							return true;
						} else {
							valid = false;
							break;
						}
					}



					summVisitedFldEdges.add(new Pair<FldPair, Integer>(fp, summCtxHash));					
				} // END of summary application				
			} // END of SummaryRecord

			if (valid) {
				Edge topEdge = summCtxStk.removeFirst();

				for (Iterator<AbstractSPGEdge> inIter = end.getIncomingEdges(); inIter.hasNext();) {
					AbstractSPGEdge e = inIter.next();
					if (e instanceof EntryEdge) {
						Edge cs = ((EntryEdge)e).getCallGraphEdge();
						if (cs == topEdge && !summVisitedCtxEdges.contains(e)) {
							AbstractAllocNode src = e.src();
							if (src == target) {
								return summFldStk.isEmpty();									
							}

							Util.traversedNodes++;
							if (Util.isOutOfBudget()) {
								return true;
							}
							CtxStkChain ctxStkChain = new CtxStkChain(ctxStk, null);
						    FldStkChain fldStkChain = new FldStkChain(fldStk, null);
						    
						    ctxStkChain.setOldStkLinkLost(true);
						    fldStkChain.setOldStkLinkLost(true);
							HashSet<AbstractSPGEdge> theContexts = (HashSet<AbstractSPGEdge>)(summVisitedCtxEdges.clone());
							int theCtxHash = 3 * summCtxHash + e.getReverseId();
							
							TraverseTupleNew q = TraverseTupleNew.getTuple(src, ctxStkChain, fldStkChain, theContexts, summVisitedFldEdges, theCtxHash,e, 
									TraverseTuple.IN);
							worklist.add(q);
						}
					}
				}

				for (Iterator<AbstractSPGEdge> outIter = end.getOutgoingEdges(); outIter.hasNext();) {
					AbstractSPGEdge e = outIter.next();
					if (e instanceof ExitEdge) {
						Edge cs = ((ExitEdge)e).getCallGraphEdge();
						if (cs == topEdge && !summVisitedCtxEdges.contains(e)) {
							AbstractAllocNode tgt = e.tgt();
							if (tgt == target) {
								return summFldStk.isEmpty();
							}							

							Util.traversedNodes++;
							if (Util.isOutOfBudget()) {
								return true;
							}

							CtxStkChain ctxStkChain = new CtxStkChain(ctxStk, null);
						    FldStkChain fldStkChain = new FldStkChain(fldStk, null);
						    
						    ctxStkChain.setOldStkLinkLost(true);
						    fldStkChain.setOldStkLinkLost(true);
						    
							HashSet<AbstractSPGEdge> theContexts = (HashSet<AbstractSPGEdge>)(summVisitedCtxEdges.clone());
							int theCtxHash = 3 * summCtxHash + e.getId();
							
							TraverseTupleNew q = TraverseTupleNew.getTuple(tgt, ctxStkChain, fldStkChain, theContexts, summVisitedFldEdges, theCtxHash,e, 
									TraverseTuple.OUT);
							worklist.add(q);
						}
					}
				}
			}			
		}

		return false;
	}

	public boolean applySummary(AbstractAllocNode head, AbstractAllocNode target, LinkedList<TraverseTuple> worklist,
			LinkedList<Edge> ctxStk, LinkedList<FieldPTEdge> fldStk, HashSet<AbstractSPGEdge> visitedCtxEdges,
			HashSet<Pair<FldPair, Integer>> visitedFldEdges, int ctxHash) {

		//    	AbstractAllocNode cur = head;
		SootMethod mtd = head.getMethod(); 
		//System.out.println("Summary started : "+mtd);
		//Jyothi: head can be a return node of a method, or a parameter node of a method (accessed as a target to an actual parameter at a callsite of a method). 
		//In either case, we are entering into a new method from the current method. Hence we get its summary and apply it.

		// TODO: possible bottleneck
		//    	HashSet<SootMethod> rm = Util.getReachables(mtd);
		//    	if (rm.contains(target.getMethod())) {
		//    		TraverseTuple q = TraverseTuple.getTuple(head, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash);
		//        	worklist.add(q);
		//        	return false;
		//    	}
		// END

		//    	long start = System.currentTimeMillis();
		Summary summ = null;
		try {

			summ = Summary.getSummary(mtd);
			if (Util.DEBUG_SUMMARY) {
				System.out.println("[summary.pass] " + mtd);
			}
		} catch (OutOfBudgetException e) {
			if (Util.DEBUG_SUMMARY) {
				System.out.println("[summary.fail] " + mtd);
			}
			return true;
		}
		//System.out.println("Out of budget exception occ -- Summary : "+mtd);
		/*	Summary.numSumMtdsP++;
		Summary.usage.put(mtd, Summary.usage.get(mtd).intValue()+1);*/

		//		Summary.totalComputeTime += (System.currentTimeMillis() - start);

		// if the summary is empty, nothing is applied.
		// FIXME: this might not be the right thing to do
		if (summ == Summary.emptySummary) return false;

		//System.out.println("Has non-empty Summary : "+mtd);

		Collection<SummaryRecord> records = summ.startsWith(head);
		if (records.isEmpty()) {
			return false;
		}
		// with non-empty summary, let's apply it
		for (SummaryRecord rec : records) {
			// grab the end node
			AbstractAllocNode cur = head;
			AbstractAllocNode end = rec.end();
			if (cur == end) continue;

			// every time a new summary record is about to apply,
			// we need to copy current stack from the same quad!

			// clones the current stacks
			LinkedList<Edge> summCtxStk = (LinkedList<Edge>)(ctxStk.clone());
			LinkedList<FieldPTEdge> summFldStk = (LinkedList<FieldPTEdge>)(fldStk.clone());
			HashSet<AbstractSPGEdge> summVisitedCtxEdges = (HashSet<AbstractSPGEdge>)(visitedCtxEdges.clone());
			HashSet<Pair<FldPair, Integer>> summVisitedFldEdges = (HashSet<Pair<FldPair, Integer>>)(visitedFldEdges.clone());
			int summCtxHash = ctxHash;    		

			//			my_assert(rec.begin() == head, "begin != head");

			//			AbstractSPGEdge edge = null;
			boolean valid = true;
			for (NumberedObject summObj : rec.getSeqSumm()) {
				Util.traversedNodes++;
				if (Util.isOutOfBudget()) {
					return true;
				}

				if (summObj instanceof CtxPair) {
					CtxPair cp = (CtxPair) summObj;
					AbstractSPGEdge edge = cp.getEdge();

					if (summVisitedCtxEdges.contains(edge)) {
						valid = false;
						break;
					}	        	        		

					int action = cp.getAction();
					Edge cs2 = cp.getCallsite();
					if (action == CtxPair.PUSH) {
						summCtxStk.addFirst(cs2);
					} else {	// action == POP
						if (!summCtxStk.isEmpty()) {
							if (cs2 != summCtxStk.removeFirst()) {
								valid = false;
								break;
							}
						} // if empty, ignore the edge
					}				

					if (edge.src() == cur) {
						cur = edge.tgt();
					} else {
						cur = edge.src();
					}
					if (cur == target) {
						if (summFldStk.isEmpty()) {
							return true;
						} else {
							valid = false;
							break;
						}
					}
					// the current edge is valid, so add it
					summVisitedCtxEdges.add(edge);
					if (action == CtxPair.PUSH) {
						if (edge instanceof EntryEdge) {	// entry
							summCtxHash = 3 * summCtxHash + edge.getId();
						} else {	// inverse exit
							summCtxHash = 3 * summCtxHash + edge.getReverseId();
						}
					} else {
						if (edge instanceof EntryEdge) {	// inverse entry
							summCtxHash = 3 * summCtxHash + edge.getReverseId();
						} else {	// exit
							summCtxHash = 3 * summCtxHash + edge.getId();
						}
					}
				} else {
					FldPair fp = (FldPair) summObj;

					AbstractSPGEdge edge = fp.getEdge();

					// check if duplicate
					boolean isDup = false;
					for (Pair<FldPair, Integer> fldPair : summVisitedFldEdges) {
						FldPair visitedFP = fldPair.first;
						if ((edge == visitedFP.getEdge()) && (fp.isBar() == visitedFP.isBar()) && (fldPair.second == summCtxHash)) {
							isDup = true;
							break;							
						}
					}
					if (isDup) {
						valid = false;
						break;
					}

					if (fp.isBar()) {
						summFldStk.addFirst(((FieldPTEdge)edge));
					} else {
						if (summFldStk.isEmpty()) {
							valid = false;
							break;
						} else {
							SootField topFld = summFldStk.removeFirst().getField();

							FieldPTEdge fpt1 = (FieldPTEdge) edge;        								

							if (!Util.sootFieldEquals(fpt1.getField(), topFld)) {
								valid = false;
								break;
							}
						}
					}

					if (edge.src() == cur) {
						cur = edge.tgt();
					} else {
						cur = edge.src();
					}
					if (cur == target) {
						if (summFldStk.isEmpty()) {
							return true;
						} else {
							valid = false;
							break;
						}
					}



					summVisitedFldEdges.add(new Pair<FldPair, Integer>(fp, summCtxHash));					
				} // END of summary application				
			} // END of SummaryRecord

			if (valid) {
				Edge topEdge = summCtxStk.removeFirst();

				for (Iterator<AbstractSPGEdge> inIter = end.getIncomingEdges(); inIter.hasNext();) {
					AbstractSPGEdge e = inIter.next();
					if (e instanceof EntryEdge) {
						Edge cs = ((EntryEdge)e).getCallGraphEdge();
						if (cs == topEdge && !summVisitedCtxEdges.contains(e)) {
							AbstractAllocNode src = e.src();
							if (src == target) {
								return summFldStk.isEmpty();									
							}

							Util.traversedNodes++;
							if (Util.isOutOfBudget()) {
								return true;
							}

							HashSet<AbstractSPGEdge> theContexts = (HashSet<AbstractSPGEdge>)(summVisitedCtxEdges.clone());
							int theCtxHash = 3 * summCtxHash + e.getReverseId();
							TraverseTuple q = TraverseTuple.getTuple(src, summCtxStk, summFldStk, theContexts, summVisitedFldEdges, theCtxHash,e, TraverseTuple.IN);
							worklist.add(q);
						}
					}
				}

				for (Iterator<AbstractSPGEdge> outIter = end.getOutgoingEdges(); outIter.hasNext();) {
					AbstractSPGEdge e = outIter.next();
					if (e instanceof ExitEdge) {
						Edge cs = ((ExitEdge)e).getCallGraphEdge();
						if (cs == topEdge && !summVisitedCtxEdges.contains(e)) {
							AbstractAllocNode tgt = e.tgt();
							if (tgt == target) {
								return summFldStk.isEmpty();
							}							

							Util.traversedNodes++;
							if (Util.isOutOfBudget()) {
								return true;
							}

							HashSet<AbstractSPGEdge> theContexts = (HashSet<AbstractSPGEdge>)(summVisitedCtxEdges.clone());
							int theCtxHash = 3 * summCtxHash + e.getId();
							TraverseTuple q = TraverseTuple.getTuple(tgt, summCtxStk, summFldStk, theContexts, summVisitedFldEdges, theCtxHash,e, TraverseTuple.OUT);
							worklist.add(q);
						}
					}
				}
			}			
		}

		return false;
	}

	/*
	 * Intuitively, a method is worth computing summary for if
	 * 		! it is `frequently' called, i.e. used in quite a large number of places
	 * 
	 * Factors affecting the running time of the CFL-reachability computing
	 * while traversing a particular method:
	 * 		! number of incoming/outgoing edges for the nodes on the traverse paths. this
	 * 		  number should be large, meaning that it has large traversal complexity without
	 * 		  summary; it should not be too large, meaning that it is not too complicated
	 * 		  for the summary computing to finish.
	 * 
	 * Metric parameters:
	 * 	#pred - number of parent nodes in the call graph
	 *  #succ - number of children nodes in the call graph     *  
	 * 
	 */
	public static boolean worthApply(SootMethod mtd, SootMethod tgtMtd) {
		//comment -start
		/*if (!worthApply(mtd)) return false;
		ReachableMethods rm = Util.getReachables(mtd);
		if (rm.contains(tgtMtd)) {        		
			return false;
		}

		return true;*/

		// comment -end

		return false;
	}

	public static boolean worthApply(SootMethod mtd) {
		if (Summary.doNotCompute.contains(mtd)) return false;
		// number of incoming call graph edges
		//--- OLD
		/*	Integer tmp = methodProfile.get(mtd);
		if (tmp == null) return false;
		int callers = tmp.intValue();
		boolean res = (callers >= threshold);    	*/
		//--- NEW
		//    	boolean res = true;	// all
		boolean res = mtd.getDeclaringClass().isLibraryClass();	// lib only
		//--- END    	
		//    	if (res) {
		//    		Util.numLibMtds++;
		//    	} else {
		//    		Util.numAppMtds++;
		//    	}

		return res;
		// ---
	}

	private int iterSize(Iterator iter) {
		int res = 0;
		while (iter.hasNext()) {
			iter.next();
			res++;
		}
		return res;
	}

	@SuppressWarnings("unchecked")
	public boolean mayAlias_bfs(VarNode vn1, VarNode vn2) {
		if (!compatibleRefLikeType(vn1.getType(), vn2.getType())) {
			return false;
		}
		SootMethod mtd1 = vn1.getMethod();
		SootMethod mtd2 = vn2.getMethod();

		SymbolicPointerGraph spg1 = SymbolicPointerGraph.v(mtd1);
		Set<AbstractAllocNode> nodes1 = (Set<AbstractAllocNode>) spg1.getVarPtSet().get(vn1);

		SymbolicPointerGraph spg2 = SymbolicPointerGraph.v(mtd2);
		Set<AbstractAllocNode> nodes2 = (Set<AbstractAllocNode>) spg2.getVarPtSet().get(vn2);

		// somehow it points to nothing
		if (nodes1 == null || nodes2 == null) {			
			return false;
		}

		for (AbstractAllocNode n1 : nodes1) {
			for (AbstractAllocNode n2 : nodes2) {				
				TraverseTuple.clear();			
				HashSet<Type> types;// = new HashSet<>();
				types = AliasGlobalVariables.relevantTypesMap.get(vn1.getType());
				for(Type typ : types){
					typ.setRelevant(true);
				}
				//types.addAll(AliasGlobalVariables.relevantTypesMap.get(vn1.getType()));
				if(vn2.getType() != vn1.getType()){
					//types.addAll(AliasGlobalVariables.relevantTypesMap.get(vn2.getType()));
					types = AliasGlobalVariables.relevantTypesMap.get(vn2.getType());
					for(Type typ : types){
						typ.setRelevant(true);
					}
				}

				//System.out.println("type: " +vn1.getType()+"Chosen types : "+types.size());

				boolean res = false;
				switch(PAMain.ALGO){
				case 1:
					res = basic(n1, n2);
					break;
				case 2:
					res = RT(n1, n2, types);
					break;
				case 3:
					res = VC(n1, n2);
					break;
				case 5:
					res = smart(n1, n2);
					break;
				}
				//	System.out.println("Result : "+res);
				//				
				//				if (Util.isOutOfBudget()) {
				//					System.out.println("[traversal.OutOfBudget] " + vn1 + ", " + vn2);
				//				}
				//		
				types = AliasGlobalVariables.relevantTypesMap.get(vn1.getType());
				for(Type typ : types){
					typ.setRelevant(false);
				}
				//types.addAll(AliasGlobalVariables.relevantTypesMap.get(vn1.getType()));
				if(vn2.getType() != vn1.getType()){
					//types.addAll(AliasGlobalVariables.relevantTypesMap.get(vn2.getType()));
					types = AliasGlobalVariables.relevantTypesMap.get(vn2.getType());
					for(Type typ : types){
						typ.setRelevant(false);
					}
				}

				//Added by Jyothi
				if(VERBOSE){
					System.out.println("Result of the analysis : "+ res);
					System.out.println("digraph G {");
					int i=0;
					System.out.println("node[margin=0, width=0.3, height=0.3]");
					System.out.println("edge[arrowsize=0.5, concentrate=false, overlap=false]");
					for(Entry<String, HashSet<String>> entry: clusters.entrySet()){
						System.out.println("	subgraph cluster"+i+++" {");
						System.out.println("		color=blue;");
						System.out.println("		label=\""+entry.getKey()+"\";");
						for (String str: entry.getValue()){
							System.out.println("		"+str+";");
						}
						System.out.println("	}");
					}
					for(String str : strings){ 
						System.out.println("	"+str+";");
					}
					System.out.println("");
					System.out.println("}");
				}

				if (Util.USE_CACHE) AliasCache.addAliasInfo(n1, n2, res);
				if (res) return true;				
			}
		}

		return false;
	}   

	private boolean compatibleRefLikeType(Type t1, Type t2) {
		if (!(t1 instanceof RefLikeType && t2 instanceof RefLikeType)) {
			return false;
		}

		if (t1 instanceof RefType && t2 instanceof RefType) {
			RefType rt1 = (RefType) t1;
			RefType rt2 = (RefType) t2;
			SootClass sc1 = rt1.getSootClass();
			SootClass sc2 = rt2.getSootClass();
			return Util.compatibleClass(sc1, sc2);
		}

		if (t1 instanceof ArrayType && t2 instanceof ArrayType) {
			ArrayType at1 = (ArrayType) t1;
			ArrayType at2 = (ArrayType) t2;
			Type et1 = at1.getArrayElementType();
			Type et2 = at2.getArrayElementType();
			// TODO: the algorithm is oversimplified here
			if (et1.equals(et2)) {
				return true;
			} else {
				return compatibleRefLikeType(et1, et2);
			}
		}

		// FIXME: simply returns true here considering that this method is used for pruning
		return true;
	}

	/**
	 * Demand-driven alias query.
	 * @param var1
	 * @param m1
	 * @param var2
	 * @param m2
	 * @return
	 * 
	 * pre-condition: var1.type == var2.type -> this condition is not checked in the method
	 * 	because it's usually the case; the types would differ only when we are doing an
	 *  exhaustive test
	 */	
	public boolean mayAlias(Local var1, SootMethod m1, Local var2, SootMethod m2) {
		if (var1.getName().equals(var2.getName()) && m1.getSignature().equals(m2.getSignature())) {
			return true;
		}	

		//		if (!spgBuilt) {
		//			buildSPG();
		//			spgBuilt = true;
		//		}
		NodeFactory nf1 = NodeFactory.v(m1);
		NodeFactory nf2 = NodeFactory.v(m2);
		VarNode vn1 = nf1.makeLocalVarNode(m1, var1);
		VarNode vn2 = nf2.makeLocalVarNode(m2, var2);
		boolean res = true; //sparkMayAlias(var1, m1, var2, m2); 
		if (res) {
			//			if (m1.getDeclaringClass().getShortName().contains("Iterator")) {
			//				if (!m2.getDeclaringClass().getShortName().contains("Iterator")) {
			//					res = mayAlias_bfs(vn2, vn1);
			//				}
			//			}
			//		System.out.println("inside bfs");
			/*HashSet<Type> types = new HashSet<>();
			types.addAll(AliasGlobalVariables.relevantTypesMap.get(var1.getType()));
			types.addAll(AliasGlobalVariables.relevantTypesMap.get(var2.getType()));*/
			res = mayAlias_bfs(vn1, vn2);//TODO: commented by Jyothi
		} else {
			Util.sparkFalsePairs++;
		}

		return res;
	}

	public boolean baselineHelper(Local var1, SootMethod m1, Local var2, SootMethod m2, PointsToAnalysis pta) {
		if (var1.getName().equals(var2.getName()) && m1.getSignature().equals(m2.getSignature())) {
			return true;
		}

		PointsToSet pts1 = pta.reachingObjects(var1);
		PointsToSet pts2 = pta.reachingObjects(var2);
		// when both empty, var1 & var2 should be the same object
		// to be aliased, which has been covered at the beginning
		if (pts1.isEmpty() || pts2.isEmpty()) {
			return false;
		}

		return pts1.hasNonEmptyIntersection(pts2);
	}
	/*
	 * Uses the context-insensitive points-to analysis provided by spark
	 * to perform the may alias.
	 */
	public boolean sparkMayAlias(Local var1, SootMethod m1, Local var2, SootMethod m2) {		
		return baselineHelper(var1, m1, var2, m2, Scene.v().getPointsToAnalysis());
	}

	public boolean manuBaseline(Local var1, SootMethod m1, Local var2, SootMethod m2) {		
		return ManuMayAliasAnalysis.v().mayAlias(var1, m1, var2, m2);
	}

	private static PAMain ins;	

	public static PAMain v() {
		if (ins == null) {
			ins = new PAMain();
		}
		return ins;
	}

	private PAMain() {
	}
}
