
package edu.iitm.cse.alias.batch.analysis;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map.Entry;
import java.util.Set;

import edu.iitm.cse.alias.batch.dsmodels.AliasGlobalVariables;
import edu.iitm.cse.alias.batch.dsmodels.AliasQuery;
import edu.iitm.cse.common.dsmodels.MutableInt;
import edu.iitm.cse.common.dsmodels.Pair;
import edu.osu.cse.pa.dsmodels.Util;
import edu.osu.cse.pa.spg.AbstractAllocNode;
import edu.osu.cse.pa.spg.NodeFactory;
import edu.osu.cse.pa.spg.SymbolicPointerGraph;
import edu.osu.cse.pa.spg.VarNode;
import soot.ArrayType;
import soot.Local;
import soot.RefLikeType;
import soot.RefType;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;


/**
 * @author Jyothi Vedurada
 * @since Dec 20, 2018
 */
public class BatchAnalysisInitiator {
	private static BatchAnalysisInitiator theInst;

	public static BatchAnalysisInitiator v() {
		if (theInst == null) {
			theInst = new BatchAnalysisInitiator();		
		}
		return theInst;
	}
	/*function splitIntoGroups(I )// I = {(ni , mi )}N ′
	foreach (nx, mx) ∈ I do cnt(nx) ← cnt(nx) + 1; cnt(mx) ← cnt(mx) + 1;
	max←argmaxcnt(n1,n2,...,nN′,m1,m2,...,mN′); // argmaxcnt(arg1,arg2,..) returns an argi for which cnt(argi) is the largest.
	foreach (nx, mx) ∈ I do
	if nx =maxormx =maxthen
	G ← G ∪ {(nx, mx)};
	I = I − G;
	S = {G} ∪ splitIntoGroups(I ); return S;*/
	public void processQueriesInBatch(Set<AliasQuery> aliasqueries){
		ArrayList<Pair<AbstractAllocNode,AbstractAllocNode>> effectiveQueriesV = new ArrayList<Pair<AbstractAllocNode,AbstractAllocNode>>();
		//Set<Pair<AbstractAllocNode,AbstractAllocNode>> effectiveQueriesSet = new HashSet<Pair<AbstractAllocNode,AbstractAllocNode>>();
		for(AliasQuery query: aliasqueries){
			Local var1 = query.getL1();
			Local var2 = query.getL2();
			SootMethod mtd1 = query.getM1();
			SootMethod mtd2 = query.getM2();

			if (var1.getName().equals(var2.getName()) && mtd1.getSignature().equals(mtd2.getSignature())) {
				query.setAnswered(true);
				AliasGlobalVariables.results.put(query, true);
				//	System.out.println("Answered in the beginning!!");
				continue;
			}	

			/*boolean res = PAMain.v().sparkMayAlias(var1, mtd1, var2, mtd2);
			if (!res) {
				query.setAnswered(true);
				AliasGlobalVariables.results.put(query, false);
				//	System.out.println("Answered in the beginning by Spark Analysis!!");
				continue;
			}*/

			NodeFactory nf1 = NodeFactory.v(mtd1);
			NodeFactory nf2 = NodeFactory.v(mtd2);
			VarNode vn1 = nf1.makeLocalVarNode(mtd1, query.getL1());
			VarNode vn2 = nf2.makeLocalVarNode(mtd2, query.getL2());
			if (!compatibleRefLikeType(vn1.getType(), vn2.getType())) {
				query.setAnswered(true);
				AliasGlobalVariables.results.put(query, false);
				//	System.out.println("Answered in the beginning!!");
				continue;
			}

			SymbolicPointerGraph spg1 = SymbolicPointerGraph.v(mtd1);
			Set<AbstractAllocNode> nodes1 = (Set<AbstractAllocNode>) spg1.getVarPtSet().get(vn1);

			SymbolicPointerGraph spg2 = SymbolicPointerGraph.v(mtd2);
			Set<AbstractAllocNode> nodes2 = (Set<AbstractAllocNode>) spg2.getVarPtSet().get(vn2);

			query.setNodes1(nodes1);
			query.setNodes2(nodes2);

			// somehow it points to nothing
			if (nodes1 == null || nodes2 == null) {
				query.setAnswered(true);
				AliasGlobalVariables.results.put(query, false);
				//System.out.println("Answered in the beginning!!");
				continue;
			}


		}

		//Pair<AbstractAllocNode,Set<AbstractAllocNode>> sourceAndDestinationNodes; 
		BatchAliasAnalysis batchAliasAnalysis = new BatchAliasAnalysis();

		//effectiveQueriesV = new ArrayList<Pair<AbstractAllocNode,AbstractAllocNode>>();

		//start solving effective queries

		//	long start = System.currentTimeMillis();
		//sourceAndDestinationNodes = getMaxGroup(aliasqueries);
		LinkedHashMap<AbstractAllocNode,Set<AbstractAllocNode>> groups = getGroupsInOrder(aliasqueries);


		ArrayList<AbstractAllocNode> sources = new ArrayList<AbstractAllocNode>(groups.keySet());
		//	long end = System.currentTimeMillis();

		//	long elapsedTime = (end - start);

		int iter=0;
		int count = 0;
		boolean done = false;
		//int numQueries = 0;
		//		elapsedTime =0;
		loop1: do{
			AbstractAllocNode maxAllocNode = null;
			Set<AbstractAllocNode> destinationNodes = new HashSet<>();
			HashMap<AbstractAllocNode, Set<AliasQuery>> nodesToQueryMap = new HashMap<>();
			while(true){
				if(!(iter < sources.size())){
					done = true;
					continue loop1;
				}
				maxAllocNode = sources.get(iter);
				iter++;

				//start = System.currentTimeMillis();
				for(AliasQuery query : aliasqueries){
					if(query.isAnswered())
						continue;
					if(!(query.getNodes1().contains(maxAllocNode) || query.getNodes2().contains(maxAllocNode)))
						continue;

					for (AbstractAllocNode n1 : query.getNodes1()) {
						if(query.getNonAliasGroupIds() != null && query.getNonAliasGroupIds().contains(n1))
							continue;
						for (AbstractAllocNode n2 : query.getNodes2()) {
							if(query.getNonAliasGroupIds() != null && query.getNonAliasGroupIds().contains(n2))
								continue;

							if(n1 == maxAllocNode){
								destinationNodes.add(n2);
								Set<AliasQuery> queries = nodesToQueryMap.get(n2);
								if(queries == null){
									queries = new HashSet<>();
									nodesToQueryMap.put(n2, queries);
								}
								queries.add(query);
							}else if(n2 == maxAllocNode){
								destinationNodes.add(n1);
								Set<AliasQuery> queries = nodesToQueryMap.get(n1);
								if(queries == null){
									queries = new HashSet<>();
									nodesToQueryMap.put(n1, queries);
								}
								queries.add(query);
							}
						}
					}
				}

				if((destinationNodes.size() != 0 )  || (AliasGlobalVariables.results.size() == aliasqueries.size()) ){
					break;
				}
			}

			//	end = System.currentTimeMillis();
			//	elapsedTime += (end - start);

			//System.out.println("Source and destination: "+maxAllocNode+ " : " +destinationNodes.size()+" : "+destinationNodes);

			if(destinationNodes.size() > 1){
				//trigger algorithm for solving alias queries in batch with same start node.
				done = false;
				Set<AbstractAllocNode> destinationNodesCopy = new HashSet<AbstractAllocNode>(destinationNodes);

				//invoke auto answerer
				/*Iterator<AbstractAllocNode> iterator = destinationNodes.iterator();

				while(iterator.hasNext()){
					AbstractAllocNode dest = iterator.next();
					boolean answered = autoAnswer(maxAllocNode, dest);
					if(answered){
						for(AliasQuery query : nodesToQueryMap.get(dest)){
							AliasGlobalVariables.results.put(query, true);
							query.setAnswered(true);
						}
						iterator.remove();
					}
				}*/
				
				batchAliasAnalysis.processAliasQueriesInGroup(maxAllocNode, destinationNodes, aliasqueries, nodesToQueryMap);

				for(AbstractAllocNode n2 : destinationNodesCopy){
					//System.out.println(destinationNodesCopy);
					for(AliasQuery query: nodesToQueryMap.get(n2)){
						if(!query.isAnswered()){
							Set<AbstractAllocNode> nodes = query.getNonAliasGroupIds();
							if(nodes == null){
								nodes = new HashSet<>();
								query.setNonAliasGroupIds(nodes);
							}

							if(!nodes.contains(maxAllocNode)){
								nodes.add(maxAllocNode);
								if(nodes.containsAll(query.getNodes1()) || nodes.containsAll(query.getNodes2())){
									AliasGlobalVariables.results.put(query, false);
									query.setAnswered(true);
								}
							}
						}
					}
				}

			}else if(destinationNodes.size() == 1){

				//trigger algorithm for solving many independent alias queries.
				done = true;
				Set<Pair<AbstractAllocNode,AbstractAllocNode>> effectiveQueries = new HashSet<Pair<AbstractAllocNode,AbstractAllocNode>>();
				//--start--
				for(AliasQuery query: aliasqueries){
					if(!query.isAnswered()){
						for (AbstractAllocNode n1 : query.getNodes1()) {
							if(query.getNonAliasGroupIds() != null && query.getNonAliasGroupIds().contains(n1))
								continue;
							for (AbstractAllocNode n2 : query.getNodes2()) {
								if(query.getNonAliasGroupIds() != null && query.getNonAliasGroupIds().contains(n2))
									continue;
								//check for whether the query can be answered from previous queries
								//the whole part from start to end may not be required based on getMaxGroup implementation.

								/*if(effectiveQueriesPerOneActualQuery.contains(new Pair<AbstractAllocNode, AbstractAllocNode>(n2, n1))){
									System.out.println("Contains the reverse query!!");
								} */
								if(!effectiveQueries.contains(new Pair<AbstractAllocNode, AbstractAllocNode>(n2, n1))){
									//System.out.println("Contains the reverse query2!!");
									effectiveQueries.add(new Pair<AbstractAllocNode, AbstractAllocNode>(n1, n2));
								} 
							}
						}
					}
				}
				//--end--

				batchAliasAnalysis.processOrderedAliasQueries(effectiveQueries, aliasqueries);
			}else{
				// no queries to solve
				done = true;
			}
		}while(!done);

	}

	
	public void processQueriesInBatchWithOPT(Set<AliasQuery> aliasqueries){
		ArrayList<Pair<AbstractAllocNode,AbstractAllocNode>> effectiveQueriesV = new ArrayList<Pair<AbstractAllocNode,AbstractAllocNode>>();
		//Set<Pair<AbstractAllocNode,AbstractAllocNode>> effectiveQueriesSet = new HashSet<Pair<AbstractAllocNode,AbstractAllocNode>>();
		for(AliasQuery query: aliasqueries){
			Local var1 = query.getL1();
			Local var2 = query.getL2();
			SootMethod mtd1 = query.getM1();
			SootMethod mtd2 = query.getM2();

			if (var1.getName().equals(var2.getName()) && mtd1.getSignature().equals(mtd2.getSignature())) {
				query.setAnswered(true);
				AliasGlobalVariables.results_original.put(query, true);
				//	System.out.println("Answered in the beginning!!");
				continue;
			}	

			/*boolean res = PAMain.v().sparkMayAlias(var1, mtd1, var2, mtd2);
		if (!res) {
			query.setAnswered(true);
			AliasGlobalVariables.results.put(query, false);
			//	System.out.println("Answered in the beginning by Spark Analysis!!");
			continue;
		}*/

			NodeFactory nf1 = NodeFactory.v(mtd1);
			NodeFactory nf2 = NodeFactory.v(mtd2);
			VarNode vn1 = nf1.makeLocalVarNode(mtd1, query.getL1());
			VarNode vn2 = nf2.makeLocalVarNode(mtd2, query.getL2());
			if (!compatibleRefLikeType(vn1.getType(), vn2.getType())) {
				query.setAnswered(true);
				AliasGlobalVariables.results_original.put(query, false);
				//	System.out.println("Answered in the beginning!!");
				continue;
			}

			SymbolicPointerGraph spg1 = SymbolicPointerGraph.v(mtd1);
			Set<AbstractAllocNode> nodes1 = (Set<AbstractAllocNode>) spg1.getVarPtSet().get(vn1);

			SymbolicPointerGraph spg2 = SymbolicPointerGraph.v(mtd2);
			Set<AbstractAllocNode> nodes2 = (Set<AbstractAllocNode>) spg2.getVarPtSet().get(vn2);

			query.setNodes1(nodes1);
			query.setNodes2(nodes2);

			// somehow it points to nothing
			if (nodes1 == null || nodes2 == null) {
				query.setAnswered(true);
				AliasGlobalVariables.results_original.put(query, false);
				//System.out.println("Answered in the beginning!!");
				continue;
			}


		}

		//Pair<AbstractAllocNode,Set<AbstractAllocNode>> sourceAndDestinationNodes; 
		BatchAliasAnalysis batchAliasAnalysis = new BatchAliasAnalysis();

		//effectiveQueriesV = new ArrayList<Pair<AbstractAllocNode,AbstractAllocNode>>();

		//start solving effective queries

		//	long start = System.currentTimeMillis();
		//sourceAndDestinationNodes = getMaxGroup(aliasqueries);
		LinkedHashMap<AbstractAllocNode,Set<AbstractAllocNode>> groups = getGroupsInOrder(aliasqueries);


		ArrayList<AbstractAllocNode> sources = new ArrayList<AbstractAllocNode>(groups.keySet());

		int iter=0;
		//int count = 0;
		boolean done = false;
		//int numQueries = 0;
		//elapsedTime =0;
		loop1: do{
			AbstractAllocNode maxAllocNode = null;
			Set<AbstractAllocNode> destinationNodes = new HashSet<>();
			HashMap<AbstractAllocNode, Set<AliasQuery>> nodesToQueryMap = new HashMap<>();
			while(true){
				if(!(iter < sources.size())){
					done = true;
					continue loop1;
				}
				maxAllocNode = sources.get(iter);
				iter++;


				for(AliasQuery query : aliasqueries){
					if(query.isAnswered())
						continue;
					if(!(query.getNodes1().contains(maxAllocNode) || query.getNodes2().contains(maxAllocNode)))
						continue;

					for (AbstractAllocNode n1 : query.getNodes1()) {
						if(query.getNonAliasGroupIds() != null && query.getNonAliasGroupIds().contains(n1))
							continue;
						for (AbstractAllocNode n2 : query.getNodes2()) {
							if(query.getNonAliasGroupIds() != null && query.getNonAliasGroupIds().contains(n2))
								continue;

							if(n1 == maxAllocNode){
								destinationNodes.add(n2);
								Set<AliasQuery> queries = nodesToQueryMap.get(n2);
								if(queries == null){
									queries = new HashSet<>();
									nodesToQueryMap.put(n2, queries);
								}
								queries.add(query);
							}else if(n2 == maxAllocNode){
								destinationNodes.add(n1);
								Set<AliasQuery> queries = nodesToQueryMap.get(n1);
								if(queries == null){
									queries = new HashSet<>();
									nodesToQueryMap.put(n1, queries);
								}
								queries.add(query);
							}
						}
					}
				}

				if((destinationNodes.size() != 0 )  || (AliasGlobalVariables.results_original.size() == aliasqueries.size()) ){
					break;
				}
			}

			//	end = System.currentTimeMillis();
			//	elapsedTime += (end - start);

			//System.out.println("Source and destination: "+maxAllocNode+ " : " +destinationNodes.size()+" : "+destinationNodes);

			if(destinationNodes.size() > 1){
				//trigger algorithm for solving alias queries in batch with same start node.
				done = false;

				Set<AbstractAllocNode> destinationNodesCopy = new HashSet<AbstractAllocNode>(destinationNodes);

				//invoke auto answerer
				/*Iterator<AbstractAllocNode> iterator = destinationNodes.iterator();

				while(iterator.hasNext()){
					AbstractAllocNode dest = iterator.next();
					boolean answered = autoAnswer(maxAllocNode, dest);
					if(answered){
						for(AliasQuery query : nodesToQueryMap.get(dest)){
							AliasGlobalVariables.results_original.put(query, true);
							query.setAnswered(true);
						}
						iterator.remove();
					}
				}*/
				
				HashSet<Type> srcDestTypes = new HashSet<>();

				for (AbstractAllocNode target : destinationNodes){
					for(AliasQuery query: nodesToQueryMap.get(target)){
						srcDestTypes.add(query.getL1().getType());
						srcDestTypes.add(query.getL2().getType());
					}
				}
				//	System.out.println("srcDest Types : "+srcDestTypes);

				HashSet<Type> types = new HashSet<>();
				for(Type typ : srcDestTypes)
					types.addAll(AliasGlobalVariables.relevantTypesMap.get(typ));

				for(Type typ : types){
					typ.setRelevant(true);
				}

				//numQueries++;
				batchAliasAnalysis.processAliasQueriesInGroupWithOPT(maxAllocNode, destinationNodes, aliasqueries, nodesToQueryMap);

				for(Type typ : types){
					typ.setRelevant(false);
				}

				for(AbstractAllocNode n2 : destinationNodesCopy){
					//System.out.println(destinationNodesCopy);
					for(AliasQuery query: nodesToQueryMap.get(n2)){
						if(!query.isAnswered()){
							Set<AbstractAllocNode> nodes = query.getNonAliasGroupIds();
							if(nodes == null){
								nodes = new HashSet<>();
								query.setNonAliasGroupIds(nodes);
							}

							if(!nodes.contains(maxAllocNode)){
								nodes.add(maxAllocNode);
								if(nodes.containsAll(query.getNodes1()) || nodes.containsAll(query.getNodes2())){
									AliasGlobalVariables.results_original.put(query, false);
									query.setAnswered(true);
								}
							}
						}
					}
				}

			}else if(destinationNodes.size() == 1){

				//trigger algorithm for solving many independent alias queries.
				done = true;
				Set<Pair<AbstractAllocNode,AbstractAllocNode>> effectiveQueries = new HashSet<Pair<AbstractAllocNode,AbstractAllocNode>>();
				//--start--
				for(AliasQuery query: aliasqueries){
					if(!query.isAnswered()){
						for (AbstractAllocNode n1 : query.getNodes1()) {
							if(query.getNonAliasGroupIds() != null && query.getNonAliasGroupIds().contains(n1))
								continue;
							for (AbstractAllocNode n2 : query.getNodes2()) {
								if(query.getNonAliasGroupIds() != null && query.getNonAliasGroupIds().contains(n2))
									continue;
								//check for whether the query can be answered from previous queries
								//the whole part from start to end may not be required based on getMaxGroup implementation.

								/*if(effectiveQueriesPerOneActualQuery.contains(new Pair<AbstractAllocNode, AbstractAllocNode>(n2, n1))){
								System.out.println("Contains the reverse query!!");
							} */
								if(!effectiveQueries.contains(new Pair<AbstractAllocNode, AbstractAllocNode>(n2, n1))){
									//System.out.println("Contains the reverse query2!!");
									effectiveQueries.add(new Pair<AbstractAllocNode, AbstractAllocNode>(n1, n2));
								} 
							}
						}
					}
				}
				//--end--

				batchAliasAnalysis.processOrderedAliasQueriesWithOPT(effectiveQueries, aliasqueries);
			}else{
				// no queries to solve
				done = true;
			}
		}while(!done);

		//System.out.println("Num batch queries: "+numQueries);
	}

	private LinkedHashMap<AbstractAllocNode,Set<AbstractAllocNode>> getGroupsInOrder(Set<AliasQuery> aliasqueries){
		LinkedHashMap<AbstractAllocNode,Set<AbstractAllocNode>> groups = new LinkedHashMap<AbstractAllocNode,Set<AbstractAllocNode>>();
		HashMap<AbstractAllocNode,Set<AbstractAllocNode>> ranks = new HashMap<AbstractAllocNode,Set<AbstractAllocNode>>();

		for(AliasQuery query : aliasqueries){
			if(!query.isAnswered()){
				for (AbstractAllocNode n1 : query.getNodes1()) {
					for (AbstractAllocNode n2 : query.getNodes2()) {	
						Set<AbstractAllocNode> set1 = ranks.get(n1);
						Set<AbstractAllocNode> set2 = ranks.get(n2);

						if(set1 == null){
							set1 = new HashSet<AbstractAllocNode>();
							ranks.put(n1, set1);
						}
						set1.add(n2);

						if(set2 == null){
							set2 = new HashSet<AbstractAllocNode>();
							ranks.put(n2, set2);
						}
						set2.add(n1);
					}
				}
			}
		}

		int max = -999;
		AbstractAllocNode maxAllocNode = null;

		for(Entry<AbstractAllocNode,Set<AbstractAllocNode>> entry : ranks.entrySet()){
			int size =entry.getValue().size();
			if(size > max){
				max = size;
				maxAllocNode = entry.getKey();
			}
		}

		while(!ranks.isEmpty()){
			max = -999;
			groups.put(maxAllocNode, ranks.get(maxAllocNode));
			//System.out.println("Source and destination: "+maxAllocNode+ " : " +ranks.get(maxAllocNode).size()+" : "+ranks.get(maxAllocNode));
			ranks.remove(maxAllocNode);

			//check	(n1n2 n2n1)
			AbstractAllocNode previousAllocNode = maxAllocNode;
			maxAllocNode = null;
			for(Entry<AbstractAllocNode,Set<AbstractAllocNode>> entry : ranks.entrySet()){
				entry.getValue().remove(previousAllocNode);
				int size = entry.getValue().size();
				if(size>max){
					max = size;
					maxAllocNode = entry.getKey();
				} 
			}
			if(max == 0)
				break;
		}
		//System.out.println("******************");

		return groups;
	}

	private Pair<AbstractAllocNode, Set<AbstractAllocNode>> getMaxGroup(Set<AliasQuery> aliasqueries){
		HashMap<AbstractAllocNode,MutableInt> ranks = new HashMap<AbstractAllocNode,MutableInt>();
		int max = -999; 
		AbstractAllocNode maxAllocNode = null;

		int cnt=0;

		Set<Pair<AbstractAllocNode,AbstractAllocNode>> effectiveQueries = new HashSet<Pair<AbstractAllocNode,AbstractAllocNode>>();

		for(AliasQuery query: aliasqueries){
			if(!query.isAnswered()){
				cnt++;
				for (AbstractAllocNode n1 : query.getNodes1()) {
					if(query.getNonAliasGroupIds() != null && query.getNonAliasGroupIds().contains(n1))
						continue;

					for (AbstractAllocNode n2 : query.getNodes2()) {	
						if(query.getNonAliasGroupIds() != null && query.getNonAliasGroupIds().contains(n2))
							continue;

						if(!effectiveQueries.contains(new Pair<AbstractAllocNode, AbstractAllocNode>(n2, n1)))
							effectiveQueries.add(new Pair<AbstractAllocNode, AbstractAllocNode>(n1, n2));
					}
				}
			}
		}

		for(Pair<AbstractAllocNode, AbstractAllocNode> pair : effectiveQueries){
			AbstractAllocNode n1 = pair.getFirst();
			AbstractAllocNode n2 = pair.getSecond();
			MutableInt cnt1 = ranks.get(n1);
			if(cnt1 == null){
				cnt1 = new MutableInt(1);
				ranks.put(n1, cnt1);
			}else
				cnt1.increment();

			int n1cnt = cnt1.getValue();

			if(n1cnt > max){
				max = n1cnt;
				maxAllocNode = n1;
			}

			if(n1 != n2){
				MutableInt cnt2 = ranks.get(n2);
				if(cnt2 == null){
					cnt2 = new MutableInt(1);
					ranks.put(n2, cnt2);
				}else 
					cnt2.increment();

				int n2cnt = cnt2.getValue();

				if((n2cnt > max)){
					max = n2cnt;
					maxAllocNode = n2;
				}
			}
		}

		Set<AbstractAllocNode> destinationNodes = new HashSet<AbstractAllocNode>();

		for(AliasQuery query: aliasqueries){
			if(!query.isAnswered()){
				for (AbstractAllocNode n1 : query.getNodes1()) {
					if(query.getNonAliasGroupIds() != null && query.getNonAliasGroupIds().contains(n1))
						continue;
					for (AbstractAllocNode n2 : query.getNodes2()) {
						if(query.getNonAliasGroupIds() != null && query.getNonAliasGroupIds().contains(n2))
							continue;

						if(n1 == maxAllocNode){
							destinationNodes.add(n2);
						}else if(n2 == maxAllocNode){
							destinationNodes.add(n1);
						}
					}
				}
			}
		}

		return new Pair<AbstractAllocNode, Set<AbstractAllocNode>>(maxAllocNode, destinationNodes);
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
	
	public boolean autoAnswer(AbstractAllocNode start, AbstractAllocNode end) {
		Set<AbstractAllocNode> destNodesofStart = null;
		Set<AbstractAllocNode> srcNodesofEnd = new HashSet<AbstractAllocNode>();

		//if(AliasGlobalVariables.aliasesWthEmptyCallStk.keySet().contains(start))
		destNodesofStart = AliasGlobalVariables.aliasesWthEmptyCallStk.get(start);
		if(destNodesofStart.size() == 0)
			return false;
		
		for(Entry<AliasQuery,Boolean> entry : AliasGlobalVariables.results_original.entrySet()){
			AliasQuery query = entry.getKey();
			if(query.isAnswered() && entry.getValue() && (query.getNodes1()  != null) && (query.getNodes2() != null)){
				if(query.getNodes2().contains(end))
					srcNodesofEnd.addAll(query.getNodes1());
			}
		}
		
		if(srcNodesofEnd.size() == 0)
			return false;

		for(AbstractAllocNode subSrc : destNodesofStart){
			for(AbstractAllocNode subDest : srcNodesofEnd){
				if(subSrc.equals(subDest)){
					return true;
				}else if(AliasGlobalVariables.aliasesWthEmptyCallStk.get(subSrc).contains(subDest)){
						return true;
				}else{
					 if(autoAnswer2(subSrc, subDest)){ 
						 return true;}
				}
			}
		}
		return false;
	}
	/**
	 * @param maxAllocNode
	 * @param set
	 * @return
	 */
	public boolean autoAnswer2(AbstractAllocNode start, AbstractAllocNode end) {
		Set<AbstractAllocNode> destNodesofStart = null;
		Set<AbstractAllocNode> srcNodesofEnd =  new HashSet<AbstractAllocNode>();

		//if(AliasGlobalVariables.aliasesWthEmptyCallStk.keySet().contains(start))
		destNodesofStart = AliasGlobalVariables.aliasesWthEmptyCallStk.get(start);
		if(destNodesofStart.size() == 0)
			return false;
		
		if(!AliasGlobalVariables.aliasesWthEmptyCallStk.containsValue(end))
			return false;
		Iterator<heros.solver.Pair<AbstractAllocNode, AbstractAllocNode>> iter = AliasGlobalVariables.aliasesWthEmptyCallStk.iterator();
		while(iter.hasNext()){
			heros.solver.Pair<AbstractAllocNode, AbstractAllocNode> pair = iter.next();
			if(pair.getO2().equals(end)){
				srcNodesofEnd.add(pair.getO1());
			}
		}
		
		if(srcNodesofEnd.size() == 0)
			return false;
		

		for(AbstractAllocNode subSrc : destNodesofStart){
			for(AbstractAllocNode subDest : srcNodesofEnd){
				if(subSrc.equals(subDest)){
					return true;
				}else if(AliasGlobalVariables.aliasesWthEmptyCallStk.get(subSrc).contains(subDest)){
						return true;
				}else{
					 if(autoAnswer2(subSrc, subDest)){ 
						 return true;}
				}
			}
		}
		return false;
	}


}
