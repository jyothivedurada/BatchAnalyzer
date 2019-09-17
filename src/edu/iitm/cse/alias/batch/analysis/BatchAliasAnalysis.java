package edu.iitm.cse.alias.batch.analysis;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

import edu.iitm.cse.alias.batch.dsmodels.AliasGlobalVariables;
import edu.iitm.cse.alias.batch.dsmodels.AliasQuery;
import edu.osu.cse.pa.PAMain;
import edu.osu.cse.pa.dsmodels.AliasCache;
import edu.osu.cse.pa.dsmodels.CallSite;
import edu.osu.cse.pa.dsmodels.CtxPair;
import edu.osu.cse.pa.dsmodels.FldPair;
import edu.osu.cse.pa.dsmodels.NumberedObject;
import edu.osu.cse.pa.dsmodels.OutOfBudgetException;
import edu.osu.cse.pa.dsmodels.Pair;
import edu.osu.cse.pa.dsmodels.Summary;
import edu.osu.cse.pa.dsmodels.SummaryRecord;
import edu.osu.cse.pa.dsmodels.TraverseTuple;
import edu.osu.cse.pa.dsmodels.Util;
import edu.osu.cse.pa.dsmodels.WildcardEdge;
import edu.osu.cse.pa.spg.AbstractAllocNode;
import edu.osu.cse.pa.spg.AbstractSPGEdge;
import edu.osu.cse.pa.spg.ClassConstNode;
import edu.osu.cse.pa.spg.EntryEdge;
import edu.osu.cse.pa.spg.ExitEdge;
import edu.osu.cse.pa.spg.FieldPTEdge;
import edu.osu.cse.pa.spg.StringConstNode;
import edu.osu.cse.pa.spg.symbolic.SymbolicObject;
import soot.AnySubType;
import soot.ArrayType;
import soot.NullType;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.jimple.toolkits.callgraph.Edge;

/**
 * @author Jyothi Vedurada
 * @since Dec 21, 2018
 */
public class BatchAliasAnalysis {
	public void processAliasQueriesInGroup(AbstractAllocNode n1, Set<AbstractAllocNode> destinationNodes, Set<AliasQuery> aliasqueries, HashMap<AbstractAllocNode, Set<AliasQuery>> nodesToQueryMap){

		PAMain maa = PAMain.v();

		//	System.out.println("Analysis started :from : "+ n1 +"\n : to : "+destinationNodes);
		long beginning = System.currentTimeMillis();
		boolean change = false;
		Set<AbstractAllocNode> nodesToDelete = new HashSet<>();
		for(AbstractAllocNode n2 : destinationNodes){
			Boolean answer = null;
			if (n1 == n2) {
				answer = true;
				//    	} else if (n1 instanceof AllocNode && n2 instanceof AllocNode) {
			} else if (!(n1 instanceof SymbolicObject || n2 instanceof SymbolicObject)) {
				answer = false;
			} else if (Util.pointByGVN(n1) || Util.pointByGVN(n2)) {
				answer = true;
			}

			if (Util.USE_CACHE) {
				Boolean cacheResult = AliasCache.getCache(n1, n2);
				if (null != cacheResult) {
					answer = cacheResult.booleanValue();
				}
			}   

			if(answer != null){
				for(AliasQuery query: nodesToQueryMap.get(n2)){
					if(!query.isAnswered()){
						change =true;
						if(answer){
							AliasGlobalVariables.results.put(query, answer);
							query.setAnswered(true);
						}else{
							nodesToDelete.add(n2);
						}
					}
				}
			}
		}

		if(change){ 
			destinationNodes.removeAll(nodesToDelete);
			adjustDestinationNodes(destinationNodes, nodesToQueryMap);
		}

		if(destinationNodes.size() == 0)
			return;

		Util.traversedNodes = 0;

		LinkedList<TraverseTuple> worklist = new LinkedList<TraverseTuple>();
		//    	if (Util.pointByGVN(n1)) {
		//    		if (processGVN(n1, n2, worklist, new LinkedList<FieldPTEdge>(), new HashSet<AbstractSPGEdge>(),
		//    	    	new HashSet<Pair<FldPair, Integer>>(), 0)) {    		
		//    	    		return true;
		//    	    }
		//    	} else {
		TraverseTuple t = TraverseTuple.getTuple(n1, new LinkedList<Edge>(), new LinkedList<FieldPTEdge>(),
				new HashSet<AbstractSPGEdge>(), new HashSet<edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>>(), 0, null, TraverseTuple.NONE);
		worklist.add(t);
		//    	}

		while (!worklist.isEmpty()) {
			t = worklist.removeFirst();
			AbstractAllocNode n = t.getNode();
			AbstractSPGEdge prevEdge = t.getPrevEdge();

			//--- incoming edges
			outerloop:for (Iterator<AbstractSPGEdge> inIter = n.getIncomingEdges(); inIter.hasNext();) {        		
				AbstractSPGEdge e = inIter.next();
				if(e == prevEdge) continue;
				AbstractAllocNode src = e.src();
				SootMethod mtd = src.getMethod();


				//    			if (e instanceof ExitEdge && mtd != n2Method && Util.empiricalIgnoreMethod(mtd)) continue;

				// do not clone, but copy on write
				LinkedList<Edge> ctxStk = t.getCtxStk();
				LinkedList<FieldPTEdge> fldStk = t.getFldStk();
				HashSet<AbstractSPGEdge> visitedCtxEdges = t.getVisitedCtxEdges();
				HashSet<edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>> visitedFldEdges = t.getVisitedFldEdges();
				int ctxHash = t.getCtxHash();        		

				// SRC
				// --- BEGIN COPY-PASTE
				boolean isDup = maa.isDuplicate(e, ctxStk, visitedCtxEdges, visitedFldEdges, ctxHash, true);
				if (isDup) {
					// we should ignore the case when the top of stack is already wildcard
					// and the e is an edge on that cycle
					if ((e instanceof FieldPTEdge) && !(maa.isOnCycle(e, fldStk))) {
						// detect cycles
						ArrayList<FieldPTEdge> cycle = new ArrayList<FieldPTEdge>();    				
						fldStk = (LinkedList<FieldPTEdge>) fldStk.clone();
						int pos = 0;
						while (!fldStk.isEmpty()) {
							FieldPTEdge fldEdge = fldStk.removeFirst();
							// FIXME: assumed to be too expensive, return context-insensitive instead
							if (fldEdge instanceof WildcardEdge){ 
								for(AbstractAllocNode n2 : destinationNodes){
									for(AliasQuery query: nodesToQueryMap.get(n2)){
										if(!query.isAnswered()){
											AliasGlobalVariables.results.put(query, true);
											query.setAnswered(true);
										}
									}
								}
								return;
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
				//long current = System.currentTimeMillis();
				//	System.out.println("Time Stamp at "+Util.traversedNodes+ " is : "+ (current-beginning));

				if (Util.isOutOfBudget()) {
					for(AbstractAllocNode n2 : destinationNodes){
						for(AliasQuery query: nodesToQueryMap.get(n2)){
							if(!query.isAnswered()){
								AliasGlobalVariables.results.put(query, true);
								query.setAnswered(true);
							}
						}
					}
					return;
				}

				if (e instanceof FieldPTEdge) {
					fldStk = (LinkedList<FieldPTEdge>) fldStk.clone();
					fldStk.addFirst(((FieldPTEdge) e));        			
				} else if (e instanceof EntryEdge) {
					Edge cs1 = CallSite.getCallsite(e);
					//	System.out.println("Incoming: Entry: src :"+ e.src() +"dest : " +e.tgt());
					/*	System.out.println("Entry edge : incoming edge" + cs1);
					System.out.println("stack"+ctxStk);*/
					if (!ctxStk.isEmpty()) {
						ctxStk = (LinkedList<Edge>) ctxStk.clone();
						Edge cs2 = ctxStk.removeFirst();            			

						if (!cs1.equals(cs2)) {	// matching call site
							// relax the call site constraint for gvn
							// TODO: might be wrong
							/*		if ( !(n instanceof SymbolicGlobalObject &&
									cs1.kind().isStatic() &&
									cs2.kind().isStatic() &&
									cs1.getTgt().equals(cs2.getTgt()))) */{

										continue;
									}
						}
					}
				} else {
					ctxStk = (LinkedList<Edge>) ctxStk.clone();
					// only enter methods that would potentially bring points-to effects
					Edge cs1 = CallSite.getCallsite(e);

					//	System.out.println("Incoming: Exit: src :"+ e.src() +"dest : " +e.tgt());
					/*System.out.println("Exit edge : incoming edge" + cs1);
					System.out.println("stack"+ctxStk);*/
					ctxStk.addFirst(cs1);
				}

				if (Util.pointByGVN(src)) {
					//        			if (processGVN(src, n2, worklist, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {		        		
					//    	        		return true;
					//    	        	} else {
					for(AbstractAllocNode n2 : destinationNodes){
						for(AliasQuery query: nodesToQueryMap.get(n2)){
							if(!query.isAnswered()){
								AliasGlobalVariables.results.put(query, true);
								query.setAnswered(true);
							}
						}
					}
					return;

					//    	        	}
				}


				// jE9pazU8
				if (
						//        			Util.pointByGVN(src) ||		// TODO: considering gvn might lead to performance hit
						src instanceof StringConstNode ||
						src instanceof ClassConstNode
						) {
					for(AbstractAllocNode n2 : destinationNodes){
						for(AliasQuery query: nodesToQueryMap.get(n2)){
							if(!query.isAnswered()){
								AliasGlobalVariables.results.put(query, true);
								query.setAnswered(true);
							}
						}
					}
					return;
				}

				// context can be unbalanced, but putField & getField should match
				change = false;
				nodesToDelete = new HashSet<>();
				//	long start = System.currentTimeMillis();
				loop: for (AbstractAllocNode n2 : destinationNodes){
					if (src == n2) {
						if (fldStk.isEmpty()) {	        			
							// alias found
							//System.out.println("Alias found");
							for(AliasQuery query: nodesToQueryMap.get(n2)){
								if(!query.isAnswered()){
									change = true;
									AliasGlobalVariables.results.put(query, true);
									query.setAnswered(true);
								}
							}
						} else {
							if(destinationNodes.size() == 1)
								continue outerloop;		// invalid path, do NOT add to worklist
						}
						break loop;
					} else if (Util.USE_CACHE) {
						if (fldStk.isEmpty() && ctxStk.isEmpty()) {
							Boolean cache = AliasCache.getCache(src, n2);
							if (null != cache) {
								for(AliasQuery query: nodesToQueryMap.get(n2)){
									if(!query.isAnswered()){
										change =true;
										//System.out.println("Reusing the cached value!");
										if(cache.booleanValue()){
											AliasGlobalVariables.results.put(query, true);
											query.setAnswered(true);
										}else{
											nodesToDelete.add(n2);
										}
									}
								}
							}
						}	        		
					}
				}

				if(change){ 
					if(nodesToDelete.size() == destinationNodes.size())
						continue outerloop;
					adjustDestinationNodes(destinationNodes, nodesToQueryMap);
				}

				if(destinationNodes.size() == 0)
					return;
				//	long end = System.currentTimeMillis();
				//	totalAdjust += (end - start);

				//	        	if (Util.USE_SUMMARY && e instanceof ExitEdge && Summary.ignoreMethod(mtd)) continue;

				// && maa.worthApply(mtd, n2Method)
				boolean applySummary = false;
				if (Util.USE_SUMMARY && e instanceof ExitEdge) {
					for (AbstractAllocNode n2 : destinationNodes){
						if(maa.worthApply(mtd, n2.getMethod())){
							applySummary  = true;
							break;
						}
					}

					if (applySummary){
						applySummary(src, destinationNodes, worklist, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash, nodesToQueryMap);       			

						if(destinationNodes.size() == 0)
							return;
					}
				} 


				if(!applySummary) {	        		
					if (e instanceof FieldPTEdge) {
						visitedFldEdges = (HashSet<edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>>) visitedFldEdges.clone();
						visitedFldEdges.add(new edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>(FldPair.getPair(e, true), ctxHash));
					} else {
						visitedCtxEdges = (HashSet<AbstractSPGEdge>) visitedCtxEdges.clone();
						visitedCtxEdges.add(e);
						ctxHash = 3 * ctxHash + e.getReverseId();
					}
					TraverseTuple tt = TraverseTuple.getTuple(src, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash, e, TraverseTuple.IN);
					worklist.add(tt);		        			        	
				}
			}

			//--- outgoing edges
			outerloop:for (Iterator<AbstractSPGEdge> outIter = n.getOutgoingEdges(); outIter.hasNext();) {    			
				AbstractSPGEdge e = outIter.next();
				if(e == prevEdge) continue;
				AbstractAllocNode tgt = e.tgt();
				SootMethod mtd = tgt.getMethod();

				//    			if (e instanceof EntryEdge && mtd != n2Method && Util.empiricalIgnoreMethod(mtd)) continue;

				// do not clone, but copy on write
				LinkedList<Edge> ctxStk = t.getCtxStk();
				LinkedList<FieldPTEdge> fldStk = t.getFldStk();
				HashSet<AbstractSPGEdge> visitedCtxEdges = t.getVisitedCtxEdges();
				HashSet<edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>> visitedFldEdges = t.getVisitedFldEdges();
				int ctxHash = t.getCtxHash();

				// TGT
				// --- BEGIN COPY-PASTE
				boolean isDup = maa.isDuplicate(e, ctxStk, visitedCtxEdges, visitedFldEdges, ctxHash, false);
				if (isDup) {
					if (!(e instanceof FieldPTEdge))    				
						continue;
				}
				// --- END COPY-PASTE

				//        		if (addedNodes.contains(tgt)) continue;
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
				//	long current = System.currentTimeMillis();
				//	System.out.println("Time Stamp at "+Util.traversedNodes+ " is : "+ (current-beginning));
				if (Util.isOutOfBudget()) {
					for(AbstractAllocNode n2 : destinationNodes){
						for(AliasQuery query: nodesToQueryMap.get(n2)){
							if(!query.isAnswered()){
								AliasGlobalVariables.results.put(query, true);
								query.setAnswered(true);
							}
						}
					}
					return;
				}

				if (e instanceof FieldPTEdge) {
					if (fldStk.isEmpty()) {
						//System.out.println("Entered in continue");
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

					ctxStk = (LinkedList<Edge>) ctxStk.clone();
					Edge cs1 = CallSite.getCallsite(e);   	
					//	System.out.println("Outgoing: Entry: src :"+ e.src() +"dest : " +e.tgt());
					/*System.out.println("Entry edge : outgoing edge" + cs1);
					System.out.println("stack"+ctxStk);*/
					ctxStk.addFirst(cs1);
				} else {
					Edge cs1 = CallSite.getCallsite(e);  
					//	System.out.println("Outgoing: Exit: src :"+ e.src() +"dest : " +e.tgt());
					/*System.out.println("Exit edge : outgoing edge" + cs1);
					System.out.println("stack"+ctxStk);*/

					if (!ctxStk.isEmpty()) {
						ctxStk = (LinkedList<Edge>) ctxStk.clone();
						Edge cs2 = ctxStk.removeFirst();

						if (!cs1.equals(cs2)) {	// matching call site
							// relax the call site constraint for gvn
							// TODO: might be wrong
							/*	if ( !(n instanceof SymbolicGlobalObject &&
									cs1.kind().isStatic() &&
									cs2.kind().isStatic() &&
									cs1.getTgt().equals(cs2.getTgt())))*/ {

										continue;
									}
						}
					}

				}

				if (Util.pointByGVN(tgt)) {
					//        			if (processGVN(tgt, n2, worklist, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {
					//		        		return true;
					//		        	} else {
					for(AbstractAllocNode n2 : destinationNodes){
						for(AliasQuery query: nodesToQueryMap.get(n2)){
							if(!query.isAnswered()){
								AliasGlobalVariables.results.put(query, true);
								query.setAnswered(true);
							}
						}
					}
					return;
					//		        	}
				}

				if (
						//        			Util.pointByGVN(tgt) ||		// TODO: considering gvn might lead to performance hit
						tgt instanceof StringConstNode ||
						tgt instanceof ClassConstNode) {
					for(AbstractAllocNode n2 : destinationNodes){
						for(AliasQuery query: nodesToQueryMap.get(n2)){
							if(!query.isAnswered()){
								AliasGlobalVariables.results.put(query, true);
								query.setAnswered(true);
							}
						}
					}
					return;
				}    



				// context can be unbalanced, but putField & getField should match
				change = false;
				nodesToDelete = new HashSet<>();
				//long start = System.currentTimeMillis();
				loop: for (AbstractAllocNode n2 : destinationNodes){
					if (tgt == n2) {
						if (fldStk.isEmpty()) {        				
							// alias found
							//System.out.println("Alias found");
							for(AliasQuery query: nodesToQueryMap.get(n2)){
								if(!query.isAnswered()){
									change = true;
									AliasGlobalVariables.results.put(query, true);
									query.setAnswered(true);
								}
							}
						} else {
							if(destinationNodes.size() == 1)
								continue outerloop; // invalid path, do NOT add to worklist
						}
						break loop;
					} else if (Util.USE_CACHE) {
						if (fldStk.isEmpty() && ctxStk.isEmpty()) {
							Boolean cache = AliasCache.getCache(tgt, n2);
							if (null != cache) {
								for(AliasQuery query: nodesToQueryMap.get(n2)){
									if(!query.isAnswered()){
										change =true;
										//System.out.println("Reusing the cached value!");
										if(cache.booleanValue()){
											AliasGlobalVariables.results.put(query, true);
											query.setAnswered(true);
										}else{
											nodesToDelete.add(n2);
										}
									}
								}
							}
						}
					}
				}

				if(change){ 
					if(nodesToDelete.size() == destinationNodes.size())
						continue outerloop;
					adjustDestinationNodes(destinationNodes, nodesToQueryMap);
				}

				if(destinationNodes.size() == 0)
					return;
				//long end = System.currentTimeMillis();
				//	totalAdjust += (end - start);

				//        		if (Util.USE_SUMMARY && e instanceof EntryEdge && Summary.ignoreMethod(mtd)) continue;

				boolean applySummary = false;
				if (Util.USE_SUMMARY && e instanceof EntryEdge) {
					for (AbstractAllocNode n2 : destinationNodes){
						if(maa.worthApply(mtd, n2.getMethod())){
							applySummary  = true;
							break;
						}
					}

					if (applySummary){
						applySummary(tgt, destinationNodes, worklist, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash, nodesToQueryMap);      			

						if(destinationNodes.size() == 0)
							return;
					}
				} 

				if(!applySummary) {
					if (e instanceof FieldPTEdge) {
						visitedFldEdges = (HashSet<edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>>) visitedFldEdges.clone();
						visitedFldEdges.add(new edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>(FldPair.getPair(e, false), ctxHash));
					} else {
						visitedCtxEdges = (HashSet<AbstractSPGEdge>) visitedCtxEdges.clone();
						visitedCtxEdges.add(e);
						ctxHash = 3 * ctxHash + e.getId();
					}
					TraverseTuple tt = TraverseTuple.getTuple(tgt, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash, e, TraverseTuple.OUT);
					worklist.add(tt);		        	
				}    		
			}

			//    		if (traversedNodes >= Util.SPA_BUDGET_NODES) {
			//    			return true;
			//    		}
		}    	

		for (AbstractAllocNode n2 : destinationNodes){
			for(AliasQuery query: nodesToQueryMap.get(n2)){
				if(!query.isAnswered()){
					Set<AbstractAllocNode> nodes = query.getNonAliasGroupIds();
					if(nodes == null){
						nodes = new HashSet<>();
						query.setNonAliasGroupIds(nodes);
					}
					nodes.add(n1);
					if(nodes.containsAll(query.getNodes1()) || nodes.containsAll(query.getNodes2())){
						AliasGlobalVariables.results.put(query, false);
						query.setAnswered(true);
					}
				}
			}
		}

		return;
	}


	public void processAliasQueriesInGroupWithOPT(AbstractAllocNode n1, Set<AbstractAllocNode> destinationNodes, Set<AliasQuery> aliasqueries, HashMap<AbstractAllocNode, Set<AliasQuery>> nodesToQueryMap){
		PAMain maa = PAMain.v();

		//System.out.println("Analysis started2 :from : "+ n1 +"\n : to : "+destinationNodes);
		long beginning = System.currentTimeMillis();
		boolean change = false;
		Set<AbstractAllocNode> nodesToDelete = new HashSet<>();
		for(AbstractAllocNode n2 : destinationNodes){
			Boolean answer = null;
			if (n1 == n2) {
				answer = true;
				//    	} else if (n1 instanceof AllocNode && n2 instanceof AllocNode) {
			} else if (!(n1 instanceof SymbolicObject || n2 instanceof SymbolicObject)) {
				answer = false;
			} else if (Util.pointByGVN(n1) || Util.pointByGVN(n2)) {
				answer = true;
			}

			if (Util.USE_CACHE) {
				Boolean cacheResult = AliasCache.getCache(n1, n2);
				if (null != cacheResult) {
					answer = cacheResult.booleanValue();
				}
			}   

			if(answer != null){
				for(AliasQuery query: nodesToQueryMap.get(n2)){
					if(!query.isAnswered()){
						change =true;
						if(answer){
							AliasGlobalVariables.results_original.put(query, answer);
							query.setAnswered(true);
						}else{
							nodesToDelete.add(n2);
						}
					}
				}
			}
		}

		if(change){ 
			destinationNodes.removeAll(nodesToDelete);
			adjustDestinationNodes(destinationNodes, nodesToQueryMap);
		}

		if(destinationNodes.size() == 0)
			return;

		Util.traversedNodes = 0;

		LinkedList<TraverseTuple> worklist = new LinkedList<TraverseTuple>();
		//    	if (Util.pointByGVN(n1)) {
		//    		if (processGVN(n1, n2, worklist, new LinkedList<FieldPTEdge>(), new HashSet<AbstractSPGEdge>(),
		//    	    	new HashSet<Pair<FldPair, Integer>>(), 0)) {    		
		//    	    		return true;
		//    	    }
		//    	} else {
		TraverseTuple t = TraverseTuple.getTuple(n1, new LinkedList<Edge>(), new LinkedList<FieldPTEdge>(),
				new HashSet<AbstractSPGEdge>(), new HashSet<edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>>(), 0, null, TraverseTuple.NONE);
		worklist.add(t);
		//    	}
		//final LinkedList<FieldPTEdge> EMPTY_FIELD_STACK = new LinkedList<FieldPTEdge>();
		/*	MultiMap<AbstractSPGEdge, LinkedList<FieldPTEdge>> summEntry = new HashMultiMap<>();
		MultiMap<AbstractSPGEdge, LinkedList<FieldPTEdge>> summExit = new HashMultiMap<>();*/

		while (!worklist.isEmpty()) {
			t = worklist.removeFirst();
			AbstractAllocNode n = t.getNode();
			AbstractSPGEdge prevEdge = t.getPrevEdge();

			//--- incoming edges
			outerloop:for (Iterator<AbstractSPGEdge> inIter = n.getIncomingEdges(); inIter.hasNext();) {        		
				AbstractSPGEdge e = inIter.next();
				if(e == prevEdge) continue;
				AbstractAllocNode src = e.src();
				SootMethod mtd = src.getMethod();
				Type type = src.getType();

				if((type != null) && !(type.isRelevant() || (type instanceof ArrayType && ((ArrayType)type).baseType.isRelevant())
						|| (type instanceof AnySubType) || (type instanceof NullType))){
					/*try{
					System.out.println("Entered inside!! "+type);
					}catch(Exception e){
						System.out.println("Caught Exception !!");
					}*/
					continue;
				}


				//    			if (e instanceof ExitEdge && mtd != n2Method && Util.empiricalIgnoreMethod(mtd)) continue;

				// do not clone, but copy on write
				LinkedList<Edge> ctxStk = t.getCtxStk();
				LinkedList<FieldPTEdge> fldStk = t.getFldStk();
				HashSet<AbstractSPGEdge> visitedCtxEdges = t.getVisitedCtxEdges();
				HashSet<edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>> visitedFldEdges = t.getVisitedFldEdges();
				int ctxHash = t.getCtxHash();        		

				// SRC
				// --- BEGIN COPY-PASTE
				boolean isDup = maa.isDuplicate(e, ctxStk, visitedCtxEdges, visitedFldEdges, ctxHash, true);
				if (isDup) {
					// we should ignore the case when the top of stack is already wildcard
					// and the e is an edge on that cycle
					if ((e instanceof FieldPTEdge) && !(maa.isOnCycle(e, fldStk))) {
						// detect cycles
						ArrayList<FieldPTEdge> cycle = new ArrayList<FieldPTEdge>();    				
						fldStk = (LinkedList<FieldPTEdge>) fldStk.clone();
						int pos = 0;
						while (!fldStk.isEmpty()) {
							FieldPTEdge fldEdge = fldStk.removeFirst();
							// FIXME: assumed to be too expensive, return context-insensitive instead
							if (fldEdge instanceof WildcardEdge){ 
								for(AbstractAllocNode n2 : destinationNodes){
									for(AliasQuery query: nodesToQueryMap.get(n2)){
										if(!query.isAnswered()){
											AliasGlobalVariables.results_original.put(query, true);
											query.setAnswered(true);
										}
									}
								}
								return;
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
				//long current = System.currentTimeMillis();
				//	System.out.println("Time Stamp at "+Util.traversedNodes+ " is : "+ (current-beginning));

				if (Util.isOutOfBudget()) {
					for(AbstractAllocNode n2 : destinationNodes){
						for(AliasQuery query: nodesToQueryMap.get(n2)){
							if(!query.isAnswered()){
								AliasGlobalVariables.results_original.put(query, true);
								query.setAnswered(true);
							}
						}
					}
					return;
				}

				if (e instanceof FieldPTEdge) {
					fldStk = (LinkedList<FieldPTEdge>) fldStk.clone();
					fldStk.addFirst(((FieldPTEdge) e));        			
				} else if (e instanceof EntryEdge) {
					Edge cs1 = CallSite.getCallsite(e);
					//	System.out.println("Incoming: Entry: src :"+ e.src() +"dest : " +e.tgt());
					/*	System.out.println("Entry edge : incoming edge" + cs1);
				System.out.println("stack"+ctxStk);*/
					if (!ctxStk.isEmpty()) {
						ctxStk = (LinkedList<Edge>) ctxStk.clone();
						Edge cs2 = ctxStk.removeFirst();            			

						if (!cs1.equals(cs2)) {	// matching call site
							// relax the call site constraint for gvn
							// TODO: might be wrong
							/*		if ( !(n instanceof SymbolicGlobalObject &&
								cs1.kind().isStatic() &&
								cs2.kind().isStatic() &&
								cs1.getTgt().equals(cs2.getTgt()))) */{

									continue;
								}
						}
					}
				} else {
					//if(ctxStk.isEmpty()){
					if((prevEdge != null) && (prevEdge instanceof ExitEdge) && (t.getDirection() ==  TraverseTuple.OUT)){
						//System.out.println("Hello reached!! "+prevEdge + " : "+ e.src()+ " : "+e.tgt() );
						continue;
					}

					ctxStk = (LinkedList<Edge>) ctxStk.clone();
					// only enter methods that would potentially bring points-to effects
					Edge cs1 = CallSite.getCallsite(e);

					//	System.out.println("Incoming: Exit: src :"+ e.src() +"dest : " +e.tgt());
					/*System.out.println("Exit edge : incoming edge" + cs1);
				System.out.println("stack"+ctxStk);*/
					ctxStk.addFirst(cs1);
				}

				if (Util.pointByGVN(src)) {
					//        			if (processGVN(src, n2, worklist, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {		        		
					//    	        		return true;
					//    	        	} else {
					for(AbstractAllocNode n2 : destinationNodes){
						for(AliasQuery query: nodesToQueryMap.get(n2)){
							if(!query.isAnswered()){
								AliasGlobalVariables.results_original.put(query, true);
								query.setAnswered(true);
							}
						}
					}
					return;

					//    	        	}
				}

				// jE9pazU8
				if (
						//        			Util.pointByGVN(src) ||		// TODO: considering gvn might lead to performance hit
						src instanceof StringConstNode ||
						src instanceof ClassConstNode
						) {
					for(AbstractAllocNode n2 : destinationNodes){
						for(AliasQuery query: nodesToQueryMap.get(n2)){
							if(!query.isAnswered()){
								AliasGlobalVariables.results_original.put(query, true);
								query.setAnswered(true);
							}
						}
					}
					return;
				}

				// context can be unbalanced, but putField & getField should match
				change = false;
				nodesToDelete = new HashSet<>();
				//	long start = System.currentTimeMillis();
				loop: for (AbstractAllocNode n2 : destinationNodes){
					if (src == n2) {
						if (fldStk.isEmpty()) {	        			
							// alias found
							//System.out.println("Alias found");
							for(AliasQuery query: nodesToQueryMap.get(n2)){
								if(!query.isAnswered()){
									change = true;
									AliasGlobalVariables.results_original.put(query, true);
									query.setAnswered(true);
								}
							}
						} else {
							if(destinationNodes.size() == 1)
								continue outerloop;		// invalid path, do NOT add to worklist
						}
						break loop;
					} else if (Util.USE_CACHE) {
						if (fldStk.isEmpty() && ctxStk.isEmpty()) {
							Boolean cache = AliasCache.getCache(src, n2);
							if (null != cache) {
								for(AliasQuery query: nodesToQueryMap.get(n2)){
									if(!query.isAnswered()){
										change =true;
										//System.out.println("Reusing the cached value!");
										if(cache.booleanValue()){
											AliasGlobalVariables.results_original.put(query, true);
											query.setAnswered(true);
										}else{
											nodesToDelete.add(n2);
										}
									}
								}
							}
						}	        		
					}
				}

				if(change){ 
					if(nodesToDelete.size() == destinationNodes.size())
						continue outerloop;
					adjustDestinationNodes(destinationNodes, nodesToQueryMap);
				}

				if(destinationNodes.size() == 0)
					return;
				//	long end = System.currentTimeMillis();
				//	totalAdjust += (end - start);

				//	        	if (Util.USE_SUMMARY && e instanceof ExitEdge && Summary.ignoreMethod(mtd)) continue;

				// && maa.worthApply(mtd, n2Method)
				boolean applySummary = false;
				if (Util.USE_SUMMARY && e instanceof ExitEdge) {
					for (AbstractAllocNode n2 : destinationNodes){
						if(maa.worthApply(mtd, n2.getMethod())){
							applySummary  = true;
							break;
						}
					}

					if (applySummary){
						applySummarywithOPT(src, destinationNodes, worklist, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash, nodesToQueryMap);       			

						if(destinationNodes.size() == 0)
							return;
					}
				} 


				if(!applySummary) {	        		
					if (e instanceof FieldPTEdge) {
						visitedFldEdges = (HashSet<edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>>) visitedFldEdges.clone();
						visitedFldEdges.add(new edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>(FldPair.getPair(e, true), ctxHash));
					} else {
						visitedCtxEdges = (HashSet<AbstractSPGEdge>) visitedCtxEdges.clone();
						visitedCtxEdges.add(e);
						ctxHash = 3 * ctxHash + e.getReverseId();
					}
					TraverseTuple tt = TraverseTuple.getTuple(src, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash, e, TraverseTuple.IN);
					worklist.add(tt);		        			        	
				}
			}

			//--- outgoing edges
			outerloop:for (Iterator<AbstractSPGEdge> outIter = n.getOutgoingEdges(); outIter.hasNext();) {    			
				AbstractSPGEdge e = outIter.next();
				if(e == prevEdge) continue;
				AbstractAllocNode tgt = e.tgt();
				SootMethod mtd = tgt.getMethod();
				Type type = tgt.getType();

				if((type != null) && !(type.isRelevant() || (type instanceof ArrayType && ((ArrayType)type).baseType.isRelevant())
						|| (type instanceof AnySubType) || (type instanceof NullType))){
					/*try{
					System.out.println("Entered inside!! "+type);
					}catch(Exception e){
						System.out.println("Caught Exception !!");
					}*/
					continue;
				}

				//    			if (e instanceof EntryEdge && mtd != n2Method && Util.empiricalIgnoreMethod(mtd)) continue;

				// do not clone, but copy on write
				LinkedList<Edge> ctxStk = t.getCtxStk();
				LinkedList<FieldPTEdge> fldStk = t.getFldStk();
				HashSet<AbstractSPGEdge> visitedCtxEdges = t.getVisitedCtxEdges();
				HashSet<edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>> visitedFldEdges = t.getVisitedFldEdges();
				int ctxHash = t.getCtxHash();

				// TGT
				// --- BEGIN COPY-PASTE
				boolean isDup = maa.isDuplicate(e, ctxStk, visitedCtxEdges, visitedFldEdges, ctxHash, false);
				if (isDup) {
					if (!(e instanceof FieldPTEdge))    				
						continue;
				}
				// --- END COPY-PASTE

				//        		if (addedNodes.contains(tgt)) continue;
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
				//	long current = System.currentTimeMillis();
				//	System.out.println("Time Stamp at "+Util.traversedNodes+ " is : "+ (current-beginning));
				if (Util.isOutOfBudget()) {
					for(AbstractAllocNode n2 : destinationNodes){
						for(AliasQuery query: nodesToQueryMap.get(n2)){
							if(!query.isAnswered()){
								AliasGlobalVariables.results_original.put(query, true);
								query.setAnswered(true);
							}
						}
					}
					return;
				}

				if (e instanceof FieldPTEdge) {
					if (fldStk.isEmpty()) {
						//System.out.println("Entered in continue");
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
					if((prevEdge != null) && (prevEdge instanceof EntryEdge) && (((EntryEdge)prevEdge).getVirtualID() == ((EntryEdge)e).getVirtualID())
							&& (t.getDirection() ==  TraverseTuple.IN)){
						//	System.out.println("Hello reached!! "+prevEdge + " : "+ e.src()+ " : "+e.tgt() );
						continue;
					}


					ctxStk = (LinkedList<Edge>) ctxStk.clone();
					Edge cs1 = CallSite.getCallsite(e);   	
					//	System.out.println("Outgoing: Entry: src :"+ e.src() +"dest : " +e.tgt());
					/*System.out.println("Entry edge : outgoing edge" + cs1);
				System.out.println("stack"+ctxStk);*/
					ctxStk.addFirst(cs1);
				} else {
					Edge cs1 = CallSite.getCallsite(e);  
					//	System.out.println("Outgoing: Exit: src :"+ e.src() +"dest : " +e.tgt());
					/*System.out.println("Exit edge : outgoing edge" + cs1);
				System.out.println("stack"+ctxStk);*/

					if (!ctxStk.isEmpty()) {
						ctxStk = (LinkedList<Edge>) ctxStk.clone();
						Edge cs2 = ctxStk.removeFirst();

						if (!cs1.equals(cs2)) {	// matching call site
							// relax the call site constraint for gvn
							// TODO: might be wrong
							/*	if ( !(n instanceof SymbolicGlobalObject &&
								cs1.kind().isStatic() &&
								cs2.kind().isStatic() &&
								cs1.getTgt().equals(cs2.getTgt())))*/ {

									continue;
								}
						}
					}

					//Doubt : jyothi Will this part of the code ever reached? I don't think so because these are the exit edges without return value
					//Clarification: Need not be, these can also be exit edges mapped to return vals and entry edges mapped to parameters at the same time.
				}

				if (Util.pointByGVN(tgt)) {
					//        			if (processGVN(tgt, n2, worklist, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash)) {
					//		        		return true;
					//		        	} else {
					for(AbstractAllocNode n2 : destinationNodes){
						for(AliasQuery query: nodesToQueryMap.get(n2)){
							if(!query.isAnswered()){
								AliasGlobalVariables.results_original.put(query, true);
								query.setAnswered(true);
							}
						}
					}
					return;
					//		        	}
				}

				if (
						//        			Util.pointByGVN(tgt) ||		// TODO: considering gvn might lead to performance hit
						tgt instanceof StringConstNode ||
						tgt instanceof ClassConstNode) {
					for(AbstractAllocNode n2 : destinationNodes){
						for(AliasQuery query: nodesToQueryMap.get(n2)){
							if(!query.isAnswered()){
								AliasGlobalVariables.results_original.put(query, true);
								query.setAnswered(true);
							}
						}
					}
					return;
				}    



				// context can be unbalanced, but putField & getField should match
				change = false;
				nodesToDelete = new HashSet<>();
				//long start = System.currentTimeMillis();
				loop: for (AbstractAllocNode n2 : destinationNodes){
					if (tgt == n2) {
						if (fldStk.isEmpty()) {        				
							// alias found
							//System.out.println("Alias found");
							for(AliasQuery query: nodesToQueryMap.get(n2)){
								if(!query.isAnswered()){
									change = true;
									AliasGlobalVariables.results_original.put(query, true);
									query.setAnswered(true);
								}
							}
						} else {
							if(destinationNodes.size() == 1)
								continue outerloop; // invalid path, do NOT add to worklist
						}
						break loop;
					} else if (Util.USE_CACHE) {
						if (fldStk.isEmpty() && ctxStk.isEmpty()) {
							Boolean cache = AliasCache.getCache(tgt, n2);
							if (null != cache) {
								for(AliasQuery query: nodesToQueryMap.get(n2)){
									if(!query.isAnswered()){
										change =true;
										//System.out.println("Reusing the cached value!");
										if(cache.booleanValue()){
											AliasGlobalVariables.results_original.put(query, true);
											query.setAnswered(true);
										}else{
											nodesToDelete.add(n2);
										}
									}
								}
							}
						}
					}
				}

				if(change){ 
					if(nodesToDelete.size() == destinationNodes.size())
						continue outerloop;
					adjustDestinationNodes(destinationNodes, nodesToQueryMap);
				}

				if(destinationNodes.size() == 0)
					return;
				//long end = System.currentTimeMillis();
				//	totalAdjust += (end - start);

				//        		if (Util.USE_SUMMARY && e instanceof EntryEdge && Summary.ignoreMethod(mtd)) continue;

				boolean applySummary = false;
				if (Util.USE_SUMMARY && e instanceof EntryEdge) {
					for (AbstractAllocNode n2 : destinationNodes){
						if(maa.worthApply(mtd, n2.getMethod())){
							applySummary  = true;
							break;
						}
					}

					if (applySummary){
						applySummarywithOPT(tgt, destinationNodes, worklist, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash, nodesToQueryMap);      			

						if(destinationNodes.size() == 0)
							return;
					}
				} 

				if(!applySummary) {
					if (e instanceof FieldPTEdge) {
						visitedFldEdges = (HashSet<edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>>) visitedFldEdges.clone();
						visitedFldEdges.add(new edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>(FldPair.getPair(e, false), ctxHash));
					} else {
						visitedCtxEdges = (HashSet<AbstractSPGEdge>) visitedCtxEdges.clone();
						visitedCtxEdges.add(e);
						ctxHash = 3 * ctxHash + e.getId();
					}
					TraverseTuple tt = TraverseTuple.getTuple(tgt, ctxStk, fldStk, visitedCtxEdges, visitedFldEdges, ctxHash, e, TraverseTuple.OUT);
					worklist.add(tt);		        	
				}    		
			}

			//    		if (traversedNodes >= Util.SPA_BUDGET_NODES) {
			//    			return true;
			//    		}
		}    	

		for (AbstractAllocNode n2 : destinationNodes){
			for(AliasQuery query: nodesToQueryMap.get(n2)){
				if(!query.isAnswered()){
					Set<AbstractAllocNode> nodes = query.getNonAliasGroupIds();
					if(nodes == null){
						nodes = new HashSet<>();
						query.setNonAliasGroupIds(nodes);
					}
					nodes.add(n1);
					if(nodes.containsAll(query.getNodes1()) || nodes.containsAll(query.getNodes2())){
						AliasGlobalVariables.results_original.put(query, false);
						query.setAnswered(true);
					}
				}
			}
		}

		return;

	}

	//	public static long totalAdjust = (long) 1.0;
	private void adjustDestinationNodes(Set<AbstractAllocNode> destinationNodes, HashMap<AbstractAllocNode, Set<AliasQuery>> nodesToQueryMap){
		//long start = System.currentTimeMillis();
		Iterator<AbstractAllocNode> destItr = destinationNodes.iterator();
		while(destItr.hasNext()){
			AbstractAllocNode n2 = destItr.next();
			boolean notAnswered = false;
			for(AliasQuery query: nodesToQueryMap.get(n2)){
				if(!query.isAnswered())
					notAnswered = true;
			}
			if(!notAnswered)
				destItr.remove();
		}
		//long end = System.currentTimeMillis();
		//totalAdjust += (end - start);
	}

	public void applySummary(AbstractAllocNode head, Set<AbstractAllocNode> destinationNodes, LinkedList<TraverseTuple> worklist,
			LinkedList<Edge> ctxStk, LinkedList<FieldPTEdge> fldStk, HashSet<AbstractSPGEdge> visitedCtxEdges,
			HashSet<edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>> visitedFldEdges, int ctxHash, HashMap<AbstractAllocNode, Set<AliasQuery>> nodesToQueryMap) {

		//    	AbstractAllocNode cur = head;
		SootMethod mtd = head.getMethod(); 

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
			for (AbstractAllocNode target : destinationNodes){
				for(AliasQuery query: nodesToQueryMap.get(target)){
					if(!query.isAnswered()){
						AliasGlobalVariables.results.put(query, true);
						query.setAnswered(true);
					}
				}
			}
			adjustDestinationNodes(destinationNodes, nodesToQueryMap);
			return;
		}
		//		Summary.totalComputeTime += (System.currentTimeMillis() - start);

		// if the summary is empty, nothing is applied.
		// FIXME: this might not be the right thing to do
		if (summ == Summary.emptySummary) return;

		Collection<SummaryRecord> records = summ.startsWith(head);
		if (records.isEmpty()) {
			return;
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
			HashSet<edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>> summVisitedFldEdges = (HashSet<edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>>)(visitedFldEdges.clone());
			int summCtxHash = ctxHash;    		

			//			my_assert(rec.begin() == head, "begin != head");

			//			AbstractSPGEdge edge = null;
			boolean valid = true;
			loop:	for (NumberedObject summObj : rec.getSeqSumm()) {
				Util.traversedNodes++;
				if (Util.isOutOfBudget()) {
					for (AbstractAllocNode target : destinationNodes){
						for(AliasQuery query: nodesToQueryMap.get(target)){
							if(!query.isAnswered()){
								AliasGlobalVariables.results.put(query, true);
								query.setAnswered(true);
							}
						}
					}
					adjustDestinationNodes(destinationNodes, nodesToQueryMap);
					return;
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

					boolean change = false;
					innerloop: for (AbstractAllocNode target : destinationNodes){
						if (cur == target) {
							if (summFldStk.isEmpty()) {
								for(AliasQuery query: nodesToQueryMap.get(target)){
									if(!query.isAnswered()){
										change = true;
										AliasGlobalVariables.results.put(query, true);
										query.setAnswered(true);
									}
								}
								break innerloop;
							} else {
								valid = false;
								break loop;
							}
						}
					}
					if(change){ 
						adjustDestinationNodes(destinationNodes, nodesToQueryMap);
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
					for (edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer> fldPair : summVisitedFldEdges) {
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

					boolean change = false;
					innerloop: for (AbstractAllocNode target : destinationNodes){
						if (cur == target) {
							if (summFldStk.isEmpty()) {
								for(AliasQuery query: nodesToQueryMap.get(target)){
									if(!query.isAnswered()){
										change = true;
										AliasGlobalVariables.results.put(query, true);
										query.setAnswered(true);
									}
								}
								break innerloop;
							} else {
								valid = false;
								break loop;
							}
						}
					}
					if(change){ 
						adjustDestinationNodes(destinationNodes, nodesToQueryMap);
					}

					summVisitedFldEdges.add(new edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>(fp, summCtxHash));					
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

							boolean change = false;
							innerloop: for (AbstractAllocNode target : destinationNodes){
								if (src == target) {
									if (summFldStk.isEmpty()) {
										for(AliasQuery query: nodesToQueryMap.get(target)){
											if(!query.isAnswered()){
												change = true;
												AliasGlobalVariables.results.put(query, true);
												query.setAnswered(true);
											}
										}
										break innerloop;
									} else {
										return; //through this method's entry or exit edge, valid path cannot be reached. ~Jyothi 
									}
								}
							}
							if(change){ 
								adjustDestinationNodes(destinationNodes, nodesToQueryMap);
							}


							Util.traversedNodes++;
							if (Util.isOutOfBudget()) {
								for (AbstractAllocNode target : destinationNodes){
									for(AliasQuery query: nodesToQueryMap.get(target)){
										if(!query.isAnswered()){
											AliasGlobalVariables.results.put(query, true);
											query.setAnswered(true);
										}
									}
								}
								adjustDestinationNodes(destinationNodes, nodesToQueryMap);
								return;
							}

							HashSet<AbstractSPGEdge> theContexts = (HashSet<AbstractSPGEdge>)(summVisitedCtxEdges.clone());
							int theCtxHash = 3 * summCtxHash + e.getReverseId();
							TraverseTuple q = TraverseTuple.getTuple(src, summCtxStk, summFldStk, theContexts, summVisitedFldEdges, theCtxHash, e, TraverseTuple.IN);
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

							boolean change = false;
							innerloop: for (AbstractAllocNode target : destinationNodes){
								if (tgt == target) {
									if (summFldStk.isEmpty()) {
										for(AliasQuery query: nodesToQueryMap.get(target)){
											if(!query.isAnswered()){
												change = true;
												AliasGlobalVariables.results.put(query, true);
												query.setAnswered(true);
											}
										}
										break innerloop;
									} else {
										return; //through this method's entry or exit edge, valid path cannot be reached. ~Jyothi 
									}
								}
							}
							if(change){ 
								adjustDestinationNodes(destinationNodes, nodesToQueryMap);
							}						

							Util.traversedNodes++;
							if (Util.isOutOfBudget()) {
								for (AbstractAllocNode target : destinationNodes){
									for(AliasQuery query: nodesToQueryMap.get(target)){
										if(!query.isAnswered()){
											AliasGlobalVariables.results.put(query, true);
											query.setAnswered(true);
										}
									}
								}
								adjustDestinationNodes(destinationNodes, nodesToQueryMap);
								return;
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

	}



	public void applySummarywithOPT(AbstractAllocNode head, Set<AbstractAllocNode> destinationNodes, LinkedList<TraverseTuple> worklist,
			LinkedList<Edge> ctxStk, LinkedList<FieldPTEdge> fldStk, HashSet<AbstractSPGEdge> visitedCtxEdges,
			HashSet<edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>> visitedFldEdges, int ctxHash, HashMap<AbstractAllocNode, Set<AliasQuery>> nodesToQueryMap) {

		//    	AbstractAllocNode cur = head;
		SootMethod mtd = head.getMethod(); 

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
			for (AbstractAllocNode target : destinationNodes){
				for(AliasQuery query: nodesToQueryMap.get(target)){
					if(!query.isAnswered()){
						AliasGlobalVariables.results_original.put(query, true);
						query.setAnswered(true);
					}
				}
			}
			adjustDestinationNodes(destinationNodes, nodesToQueryMap);
			return;
		}
		//		Summary.totalComputeTime += (System.currentTimeMillis() - start);

		// if the summary is empty, nothing is applied.
		// FIXME: this might not be the right thing to do
		if (summ == Summary.emptySummary) return;

		Collection<SummaryRecord> records = summ.startsWith(head);
		if (records.isEmpty()) {
			return;
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
			HashSet<edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>> summVisitedFldEdges = (HashSet<edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>>)(visitedFldEdges.clone());
			int summCtxHash = ctxHash;    		

			//			my_assert(rec.begin() == head, "begin != head");

			//			AbstractSPGEdge edge = null;
			boolean valid = true;
			loop:	for (NumberedObject summObj : rec.getSeqSumm()) {
				Util.traversedNodes++;
				if (Util.isOutOfBudget()) {
					for (AbstractAllocNode target : destinationNodes){
						for(AliasQuery query: nodesToQueryMap.get(target)){
							if(!query.isAnswered()){
								AliasGlobalVariables.results_original.put(query, true);
								query.setAnswered(true);
							}
						}
					}
					adjustDestinationNodes(destinationNodes, nodesToQueryMap);
					return;
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

					boolean change = false;
					innerloop: for (AbstractAllocNode target : destinationNodes){
						if (cur == target) {
							if (summFldStk.isEmpty()) {
								for(AliasQuery query: nodesToQueryMap.get(target)){
									if(!query.isAnswered()){
										change = true;
										AliasGlobalVariables.results_original.put(query, true);
										query.setAnswered(true);
									}
								}
								break innerloop;
							} else {
								valid = false;
								break loop;
							}
						}
					}
					if(change){ 
						adjustDestinationNodes(destinationNodes, nodesToQueryMap);
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
					for (edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer> fldPair : summVisitedFldEdges) {
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

					boolean change = false;
					innerloop: for (AbstractAllocNode target : destinationNodes){
						if (cur == target) {
							if (summFldStk.isEmpty()) {
								for(AliasQuery query: nodesToQueryMap.get(target)){
									if(!query.isAnswered()){
										change = true;
										AliasGlobalVariables.results_original.put(query, true);
										query.setAnswered(true);
									}
								}
								break innerloop;
							} else {
								valid = false;
								break loop;
							}
						}
					}
					if(change){ 
						adjustDestinationNodes(destinationNodes, nodesToQueryMap);
					}

					summVisitedFldEdges.add(new edu.osu.cse.pa.dsmodels.Pair<FldPair, Integer>(fp, summCtxHash));					
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

							boolean change = false;
							innerloop: for (AbstractAllocNode target : destinationNodes){
								if (src == target) {
									if (summFldStk.isEmpty()) {
										for(AliasQuery query: nodesToQueryMap.get(target)){
											if(!query.isAnswered()){
												change = true;
												AliasGlobalVariables.results_original.put(query, true);
												query.setAnswered(true);
											}
										}
										break innerloop;
									} else {
										return; //through this method's entry or exit edge, valid path cannot be reached. ~Jyothi 
									}
								}
							}
							if(change){ 
								adjustDestinationNodes(destinationNodes, nodesToQueryMap);
							}


							Util.traversedNodes++;
							if (Util.isOutOfBudget()) {
								for (AbstractAllocNode target : destinationNodes){
									for(AliasQuery query: nodesToQueryMap.get(target)){
										if(!query.isAnswered()){
											AliasGlobalVariables.results_original.put(query, true);
											query.setAnswered(true);
										}
									}
								}
								adjustDestinationNodes(destinationNodes, nodesToQueryMap);
								return;
							}

							HashSet<AbstractSPGEdge> theContexts = (HashSet<AbstractSPGEdge>)(summVisitedCtxEdges.clone());
							int theCtxHash = 3 * summCtxHash + e.getReverseId();
							TraverseTuple q = TraverseTuple.getTuple(src, summCtxStk, summFldStk, theContexts, summVisitedFldEdges, theCtxHash, e, TraverseTuple.IN);
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

							boolean change = false;
							innerloop: for (AbstractAllocNode target : destinationNodes){
								if (tgt == target) {
									if (summFldStk.isEmpty()) {
										for(AliasQuery query: nodesToQueryMap.get(target)){
											if(!query.isAnswered()){
												change = true;
												AliasGlobalVariables.results_original.put(query, true);
												query.setAnswered(true);
											}
										}
										break innerloop;
									} else {
										return; //through this method's entry or exit edge, valid path cannot be reached. ~Jyothi 
									}
								}
							}
							if(change){ 
								adjustDestinationNodes(destinationNodes, nodesToQueryMap);
							}						

							Util.traversedNodes++;
							if (Util.isOutOfBudget()) {
								for (AbstractAllocNode target : destinationNodes){
									for(AliasQuery query: nodesToQueryMap.get(target)){
										if(!query.isAnswered()){
											AliasGlobalVariables.results_original.put(query, true);
											query.setAnswered(true);
										}
									}
								}
								adjustDestinationNodes(destinationNodes, nodesToQueryMap);
								return;
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


	}


	public void processOrderedAliasQueriesWithOPT(Set<edu.iitm.cse.common.dsmodels.Pair<AbstractAllocNode, AbstractAllocNode>> effectiveQueries, Set<AliasQuery> aliasqueries){
		HashMap<edu.iitm.cse.common.dsmodels.Pair<AbstractAllocNode, AbstractAllocNode>, Set<AliasQuery>> nodesToQueryMap = new HashMap<>();

		for(edu.iitm.cse.common.dsmodels.Pair<AbstractAllocNode,AbstractAllocNode> pair: effectiveQueries){
			AbstractAllocNode n1 = pair.getFirst();
			AbstractAllocNode n2 = pair.getSecond();

			for(AliasQuery query : aliasqueries){
				if(query.isAnswered())
					continue;
				if((query.getNodes1().contains(n1) && query.getNodes2().contains(n2)) ||
						(query.getNodes1().contains(n2) && query.getNodes2().contains(n1))){
					Set<AliasQuery> queries = nodesToQueryMap.get(pair);
					if(queries == null){
						queries = new HashSet<>();
						nodesToQueryMap.put(pair, queries);
					}
					queries.add(query);
				}
			}
		}

		for(edu.iitm.cse.common.dsmodels.Pair<AbstractAllocNode,AbstractAllocNode> pair: effectiveQueries){
			/*boolean res = BatchAnalysisInitiator.v().autoAnswer(pair.getFirst(), pair.getSecond());
			if(!res){
			*/
			HashSet<Type> srcDestTypes = new HashSet<>();

			for(AliasQuery query: nodesToQueryMap.get(pair)){
				srcDestTypes.add(query.getL1().getType());
				srcDestTypes.add(query.getL2().getType());
			}
			//	System.out.println("srcDest Types : "+srcDestTypes);

			HashSet<Type> types = new HashSet<>();
			for(Type typ : srcDestTypes)
				types.addAll(AliasGlobalVariables.relevantTypesMap.get(typ));

			for(Type typ : types){
				typ.setRelevant(true);
			}

			boolean res = PAMain.v().smart(pair.getFirst(), pair.getSecond());

			for(Type typ : types){
				typ.setRelevant(false);
			}
			if(res){
				for(AliasQuery query: nodesToQueryMap.get(pair)){
					if(!query.isAnswered()){
						AliasGlobalVariables.results_original.put(query, res);
						query.setAnswered(true);
					}
				}
			}
			// else: In case of negative result, it will be taken care in the next loop.
		}

		//At the end, take care of "no" answered queries. : decide whether this should be here or in its caller.
		for(AliasQuery query : aliasqueries){
			if(!query.isAnswered()){
				/*for(AbstractAllocNode n1: query.getNodes1()){
					for(AbstractAllocNode n2: query.getNodes2()){
						Pair pair =new Pair<AbstractAllocNode, AbstractAllocNode>(n1, n2));
						if(effectiveQueries.contains(pair){
							if()
							continue loop;

						}
					}
				}*/
				AliasGlobalVariables.results_original.put(query, false);
				query.setAnswered(true);
			}
		}
	}


	public void processOrderedAliasQueries(Set<edu.iitm.cse.common.dsmodels.Pair<AbstractAllocNode, AbstractAllocNode>> effectiveQueries, Set<AliasQuery> aliasqueries){
		HashMap<edu.iitm.cse.common.dsmodels.Pair<AbstractAllocNode, AbstractAllocNode>, Set<AliasQuery>> nodesToQueryMap = new HashMap<>();

		for(edu.iitm.cse.common.dsmodels.Pair<AbstractAllocNode,AbstractAllocNode> pair: effectiveQueries){
			AbstractAllocNode n1 = pair.getFirst();
			AbstractAllocNode n2 = pair.getSecond();

			for(AliasQuery query : aliasqueries){
				if(query.isAnswered())
					continue;
				if((query.getNodes1().contains(n1) && query.getNodes2().contains(n2)) ||
						(query.getNodes1().contains(n2) && query.getNodes2().contains(n1))){
					Set<AliasQuery> queries = nodesToQueryMap.get(pair);
					if(queries == null){
						queries = new HashSet<>();
						nodesToQueryMap.put(pair, queries);
					}
					queries.add(query);
				}
			}
		}

		for(edu.iitm.cse.common.dsmodels.Pair<AbstractAllocNode,AbstractAllocNode> pair: effectiveQueries){
			/*boolean res = BatchAnalysisInitiator.v().autoAnswer(pair.getFirst(), pair.getSecond());
			if(!res){
			*/
			boolean res = PAMain.v().smart(pair.getFirst(), pair.getSecond());
			if(res){
				for(AliasQuery query: nodesToQueryMap.get(pair)){
					if(!query.isAnswered()){
						AliasGlobalVariables.results.put(query, res);
						query.setAnswered(true);
					}
				}
			}
			// else: In case of negative result, it will be taken care in the next loop.
		}

		//At the end, take care of "no" answered queries. : decide whether this should be here or in its caller.
		for(AliasQuery query : aliasqueries){
			if(!query.isAnswered()){
				/*for(AbstractAllocNode n1: query.getNodes1()){
					for(AbstractAllocNode n2: query.getNodes2()){
						Pair pair =new Pair<AbstractAllocNode, AbstractAllocNode>(n1, n2));
						if(effectiveQueries.contains(pair){
							if()
							continue loop;

						}
					}
				}*/
				AliasGlobalVariables.results.put(query, false);
				query.setAnswered(true);
			}
		}
	}
}
