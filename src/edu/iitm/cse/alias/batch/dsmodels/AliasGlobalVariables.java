package edu.iitm.cse.alias.batch.dsmodels;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import edu.osu.cse.pa.spg.AbstractAllocNode;
import edu.osu.cse.pa.spg.AbstractSPGEdge;
import soot.SootMethod;
import soot.Type;
import soot.util.HashMultiMap;
import soot.util.MultiMap;

public class AliasGlobalVariables {
	
	public static HashMap<AliasQuery,Boolean> results = new HashMap<>();
	public static HashMap<AliasQuery,Boolean> results_original = new HashMap<>();
	public static int numClassesThreshold = 99999;
	//public static HashSet<Type> enclosureTypes;
	public static Set<AliasQuery> aliasqueries;
	public static boolean metGlobalVar = false;
	public static Boolean nonConservativeAns = false;
	public static HashSet<Type> defEnclTypes;
	//test
	//public static HashSet<Type> declaredTypes;
	public static HashMap<Type,HashSet<Type>> relevantTypesMap = new HashMap<>();
	//Added this for auto answerer
	public static MultiMap<AbstractAllocNode, AbstractAllocNode> aliasesWthEmptyCallStk = new HashMultiMap<>();
	
	public static int entryID = 1;
}
