package edu.iitm.cse.alias.dacapo;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Random;
import java.util.Set;

import edu.iitm.cse.alias.batch.dsmodels.AliasGlobalVariables;
import edu.iitm.cse.alias.batch.dsmodels.AliasQuery;
import edu.osu.cse.pa.dsmodels.Util;
import iohoister.analysis.ArrayFieldRef;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Value;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.InstanceFieldRef;
import soot.jimple.Stmt;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.ReachableMethods;
import soot.toolkits.scalar.Pair;
import soot.util.queue.QueueReader;

/**
 * @author Jyothi Vedurada
 * @since Nov 25, 2018
 */
public class QueriesCollectorDacapo {

	private Map<SootField, HashSet<Pair<DefinitionStmt, SootMethod>>> instanceFieldWrites =
			new HashMap<SootField, HashSet<Pair<DefinitionStmt, SootMethod>>>();
	private Map<SootField, HashSet<Pair<DefinitionStmt, SootMethod>>> instanceFieldReads =
			new HashMap<SootField, HashSet<Pair<DefinitionStmt, SootMethod>>>();

	private Map<SootField, HashSet<Pair<DefinitionStmt, SootMethod>>> arrayElementWrites =
			new HashMap<SootField, HashSet<Pair<DefinitionStmt, SootMethod>>>();
	private Map<SootField, HashSet<Pair<DefinitionStmt, SootMethod>>> arrayElementReads =
			new HashMap<SootField, HashSet<Pair<DefinitionStmt, SootMethod>>>();

	Set<SootClass> interestedTypes = new HashSet<SootClass>();

	public Set<AliasQuery> collectQueries(String application_includes){
		processApp(application_includes);
		System.out.println("Number of types of interest : "+interestedTypes.size());
		System.out.println(interestedTypes);
		Set<AliasQuery> queries =  new HashSet<>();
		populateQueries(instanceFieldWrites, instanceFieldReads, queries);
		populateQueries(arrayElementWrites, arrayElementReads, queries);
		System.out.println("Number of Alias Queries : "+queries.size());
		return queries;
	}

	private void populateQueries(Map<SootField, HashSet<Pair<DefinitionStmt, SootMethod>>> writes,
			Map<SootField, HashSet<Pair<DefinitionStmt, SootMethod>>> reads, Set<AliasQuery> queries) {		
		for (Map.Entry<SootField, HashSet<Pair<DefinitionStmt, SootMethod>>> entry : writes.entrySet()) {
			SootField writeFld = entry.getKey();
			HashSet<Pair<DefinitionStmt, SootMethod>> readSet = reads.get(writeFld); 
			HashSet<Pair<DefinitionStmt, SootMethod>> writeSet = entry.getValue();

			for (Pair<DefinitionStmt, SootMethod> p1 : writeSet) {
				DefinitionStmt s1 = p1.getO1();
				SootMethod m1 = p1.getO2();

				InstanceFieldRef f1 = (InstanceFieldRef) s1.getLeftOp();
				Local l1 = (Local) f1.getBase();
				for (Pair<DefinitionStmt, SootMethod> p2 : writeSet) {
					DefinitionStmt s2 = p2.getO1();
					SootMethod m2 = p2.getO2();
					if (s1 == s2) {
						continue;
					}

					InstanceFieldRef f2 = (InstanceFieldRef) s2.getLeftOp();					
					Local l2 = (Local) f2.getBase();
					/*if(queries.contains(query)){
						for(AliasQuery query2 : queries){
							if(query.equals(query2)){
								System.out.println(" Already contains!!");
								System.out.println("Query : "+query);
								System.out.println("Query2 : "+query2);
							}
						}
					}*/
					queries.add(new AliasQuery(l1, l2, m1, m2));
				}

				if (readSet == null) continue;
				for (Pair<DefinitionStmt, SootMethod> p2 : readSet) {
					DefinitionStmt s2 = p2.getO1();
					SootMethod m2 = p2.getO2();

					InstanceFieldRef f2 = (InstanceFieldRef) s2.getRightOp();
					Local l2 = (Local) f2.getBase();
					//	System.out.println("Query: "+l1+" : "+l2+" : "+m1+" : "+m2);
				
					/*if(queries.contains(query)){
						for(AliasQuery query2 : queries){
							if(query.equals(query2)){
								System.out.println(" Already contains!!");
								System.out.println("Query : "+query);
								System.out.println("Query2 : "+query2);
							}
						}
					}*/
					queries.add(new AliasQuery(l1, l2, m1, m2));
				}
			}
		}
	}

	private boolean hasExceptionBase(InstanceFieldRef r, SootClass throwable) {
		Type type = r.getBase().getType();
		if (type instanceof RefType) {
			RefType rt = (RefType) type;
			SootClass baseClass = Scene.v().getSootClass(rt.getClassName());
			return (Util.subclassOf(baseClass, throwable));				
		}
		return false;
	}

	@SuppressWarnings("unchecked")
	private void processMethod(SootMethod mtd) {
		if (!mtd.hasActiveBody()) {
			mtd.retrieveActiveBody();
		}

		SootClass throwable = Scene.v().getSootClass("java.lang.Throwable");

		for (Iterator stmts = mtd.getActiveBody().getUnits().iterator(); stmts.hasNext();) {
			Stmt st = (Stmt) stmts.next();
			if (!(st.containsFieldRef() && st instanceof DefinitionStmt)) {
				continue;
			}

			DefinitionStmt ds = (DefinitionStmt) st;
			Value lhs = ds.getLeftOp();
			Value rhs = ds.getRightOp();

			if (lhs instanceof FieldRef) {	// write				
				SootField fld = ((FieldRef) lhs).getField();				
				if(interestedTypes.contains(fld.getDeclaringClass())){
					if (lhs instanceof InstanceFieldRef) {
						if (hasExceptionBase((InstanceFieldRef)lhs, throwable)) {
							continue;
						}

						if (lhs instanceof ArrayFieldRef) {
							addElement(arrayElementWrites, fld, ds, mtd);						
						} else {
							addElement(instanceFieldWrites, fld, ds, mtd);						
						}					
					} else {  // StaticFieldRef
						//					addElement(staticFieldWrites, fld, ds, mtd);
					}
				}
			} else {	// rhs instanceof FieldRef
				SootField fld = ((FieldRef) rhs).getField();
				if(interestedTypes.contains(fld.getDeclaringClass())){
					if (rhs instanceof InstanceFieldRef) {
						if (hasExceptionBase((InstanceFieldRef)rhs, throwable)) {
							continue;
						}					
						if (rhs instanceof ArrayFieldRef) {
							addElement(arrayElementReads, fld, ds, mtd);
						} else {
							addElement(instanceFieldReads, fld, ds, mtd);						
						}										
					} else {  // StaticFieldRef
						//					addElement(staticFieldReads, fld, ds, mtd);
					}
				}
			}
		}
	}

	private void addElement(Map<SootField, HashSet<Pair<DefinitionStmt, SootMethod>>> map, SootField fld,
			DefinitionStmt ds, SootMethod mtd) {

		HashSet<Pair<DefinitionStmt, SootMethod>> set = map.get(fld);
		if (set == null) {
			set = new HashSet<Pair<DefinitionStmt, SootMethod>>();
			map.put(fld, set);
		}

		set.add(new Pair<DefinitionStmt, SootMethod>(ds, mtd));
	}

	public void processApp(String application_includes)
	{
		String[] applicationClassNames = application_includes.split(":");
		ArrayList<SootClass> applicationClasses  = new ArrayList<SootClass>();
		for (SootClass c : Scene.v().getClasses()) {
			for (String app : applicationClassNames) {
				if (c.toString().startsWith(app.replace("<", ""))) {
					if (!c.isApplicationClass() && !c.isPhantom())
						c.setApplicationClass();
					applicationClasses.add(c);
				}
			}
		}

		System.out.println("Number of application classes : "+ applicationClasses.size());
		if(AliasGlobalVariables.numClassesThreshold != 99999){
			Random random = new Random(1234567);
			for (SootClass sc : applicationClasses) {
				if(random.nextBoolean()){
					interestedTypes.add(sc);
				}

				if(interestedTypes.size() >= AliasGlobalVariables.numClassesThreshold){
					break;
				}
			}
		}else{
			for (SootClass sc : Scene.v().getApplicationClasses()) {
				interestedTypes.add(sc);
			}
		}

		ReachableMethods methods = Scene.v().getReachableMethods();
		CallGraph cg = Scene.v().getCallGraph();

		QueueReader<MethodOrMethodContext> r = methods.listener();
		while (r.hasNext()) {
			SootMethod mtd = (SootMethod) r.next();
			//for (SootClass sc : Scene.v().getApplicationClasses()) {
			//System.out.println("class  Name: "+sc.getName());
			//		for (SootClass sc : Scene.v().getClasses()) {
			//			boolean isApp = sc.isApplicationClass();
			if(!mtd.getDeclaringClass().isApplicationClass()) {
				continue;
			}
			if (!mtd.isConcrete()) {
				continue;
			}
			//	 System.out.println(mtd.getSignature());
			//				Util.tweakBody(mtd);

			processMethod(mtd);
		}
	}
}