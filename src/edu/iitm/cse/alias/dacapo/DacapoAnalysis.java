package edu.iitm.cse.alias.dacapo;

import java.io.File;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.iitm.cse.alias.batch.TypeCollector;
import edu.iitm.cse.alias.batch.analysis.BatchAnalysisInitiator;
import edu.iitm.cse.alias.batch.dsmodels.AliasGlobalVariables;
import edu.iitm.cse.alias.batch.dsmodels.AliasQuery;
import edu.iitm.cse.alias.batch.dsmodels.AnalysisVariant;
import edu.iitm.cse.alias.batch.evaluation.PrecisionCompare;
import edu.iitm.cse.common.dsmodels.GlobalVariables;
import edu.osu.cse.pa.PAMain;
import edu.osu.cse.pa.dsmodels.Util;
import iohoister.analysis.MayAliasAnalysis;
import soot.G;
import soot.Local;
import soot.PackManager;
import soot.Scene;
import soot.SceneTransformer;
import soot.SootClass;
import soot.SootMethod;
import soot.Transform;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.options.Options;
import soot.toolkits.scalar.Pair;

/**
 * @author Jyothi Vedurada
 * @since Jan 4, 2019
 */
public class DacapoAnalysis extends SceneTransformer {
	HashSet<Pair<Pair<Local,SootMethod>, Pair<Local, SootMethod>>> aliases = new HashSet<>();
	Set<SootMethod> visited = new HashSet<SootMethod>();
	private static DacapoAnalysis theInst;
	static CallGraph cg;
	MayAliasAnalysis maa;

	public static DacapoAnalysis v() {
		if (theInst == null) {
			theInst = new DacapoAnalysis();		
		}
		return theInst;
	}

	public static void main(String arg[]){
		GlobalVariables.projectName = arg[0];
		AliasGlobalVariables.numClassesThreshold = Integer.parseInt(arg[1]); //used to collect a set of queries
		initializesoot(arg[2]);
		Scene.v().loadNecessaryClasses();
		SootClass c = Scene.v().forceResolve(GlobalVariables.mainclass, SootClass.BODIES);
		if (c != null) {
			c.setApplicationClass();
		}
		SootMethod methodByName = c.getMethodByName("main");
		List<SootMethod> ePoints = new LinkedList<>();
		ePoints.add(methodByName);
		Scene.v().setEntryPoints(ePoints);

		/*long startTime = System.currentTimeMillis();
		Options.v().setPhaseOption("cg.spark", "on");
		Options.v().setPhaseOption("cg.spark", "vta:true");
		Options.v().setPhaseOption("cg.spark", "verbose:true");
		Options.v().setPhaseOption("cg", "all-reachable:true");
		//	Options.v().setPhaseOption("cg.spark", "on-fly-cg:false");
		PackManager.v().getPack("cg").apply();
		long stopTime = System.currentTimeMillis();
		long elapsedTime = stopTime - startTime;
		System.out.println("Time taken for CHA  graph construction : "+elapsedTime);
		 */	
		//test();

		/*for (SootClass sc : Scene.v().getClasses()) {
				sc.getFields();
			}*/

		/*int count=0;
			for (SootClass sc : Scene.v().getClasses()) {
				for (SootMethod mtd : sc.getMethods()) {
					count++;
				}
		    }
			System.out.println("Num methods before: " +count);*/

		//CallGraphPruner.v().apply();
		//test();

		long startTime = System.currentTimeMillis();
		//Scene.v().releaseCallGraph();
		//G.v().MethodPAG_methodToPag = new HashMap<SootMethod, MethodPAG>();
		//Options.v().force_overwrite();
		Options.v().setPhaseOption("cg.spark", "pre-jimplify");
		Options.v().setPhaseOption("cg.spark", "vta:false");
		Options.v().setPhaseOption("cg", "all-reachable:true");
		Options.v().setPhaseOption("cg.spark", "verbose:true");
		Options.v().setPhaseOption("cg.spark", "on");
		//Options.v().setPhaseOption("cg.spark", "geom-pta:true");
		//Options.v().setPhaseOption("cg.spark", "geom-runs:2");
		PackManager.v().getPack("cg").apply();
		long stopTime = System.currentTimeMillis();
		long elapsedTime = stopTime - startTime;
		System.out.println("Time taken for call graph construction : "+elapsedTime);

		String phaseName = "wjtp.racer";
		DacapoAnalysis pa = DacapoAnalysis.v();
		Transform t = new Transform(phaseName, pa);
		PackManager.v().getPack("wjtp").add(t);
		PackManager.v().getPack("wjtp").apply();
		stopTime = System.currentTimeMillis();
	}

	static String application_includes = null;

	public static void initializesoot(String classpath){
		G.v().reset();
		//classpath should also contain paths to rt.jar and jce.jar, required for Soot
		//"/Users/vjyothi/Downloads/jdk1.7.0_80/jre/lib/jce.jar"+":"
		//+ "/Users/vjyothi/Downloads/jdk1.7.0_80/jre/lib/rt.jar";
		
		String mainclass = "";
		String processdir = "";

		if(GlobalVariables.mainclass == null){
			switch(GlobalVariables.projectName){
			case "antlr": 
				application_includes="<dacapo.antlr.:<antlr.";
				classpath += ":"+"antlr-deps.jar";
				mainclass = "dacapo.antlr.Main";
				processdir = "antlr.jar";
				break;
			case "bloat":
				application_includes = "<dacapo.bloat.:<EDU.";			
				classpath += ":"+"bloat-deps.jar";
				mainclass = "dacapo.bloat.Main2";
				processdir = "bloat.jar";
				break;
			case  "chart":
				application_includes = "<dacapo.chart.:<org.jfree.chart.:<org.jfree.data.";
				classpath += ":"+"chart-deps.jar";
				mainclass = "dacapo.chart.Main2";
				processdir = "chart.jar";
				break;
			case "eclipse":
				application_includes = "<dacapo.eclipse.:<org.eclipse.:<org.osgi.";
				classpath += ":"+"eclipse-deps.jar";
				mainclass = "dacapo.eclipse.Main2";
				processdir = "eclipse.jar";
				break;
			case "fop":
				application_includes = "<dacapo.fop.:<org.apache.fop.";
				classpath += ":"+"fop-deps.jar";
				mainclass = "dacapo.fop.Main2";
				processdir = "fop.jar";
				break;
			case "hsqldb":
				application_includes = "<dacapo.hsqldb.:<org.hsqldb.";
				classpath += ":"+"hsqldb-deps.jar";
				mainclass = "org.hsqldb.hsqldbDoopDriver";
				processdir = "hsqldb.jar";
				break;
			case "jython":
				application_includes = "<dacapo.jython.:<com.ziclix.:<javatests.:<jxxload_help.:<org.python.:<org.apache.oro.";
				classpath += ":"+"jython-deps.jar";
				mainclass = "dacapo.jython.Main2";
				processdir = "jython.jar";
				break;
			case "luindex":
				application_includes = "<dacapo.luindex.:<dacapo.lusearch.:<org.apache.lucene.";
				//				dynamic_classes_file = luindex.dyn
				//			tamiflex_facts_file = luindex.tfx
				//			jre = jre/rt-1.4.2_11.jar
				classpath += ":"+"luindex-deps.jar";
				mainclass = "dacapo.luindex.Main2";
				processdir = "luindex.jar";
				break;
			case "lusearch":
				application_includes = "<dacapo.luindex.:<dacapo.lusearch.:<org.apache.lucene.";
				/*dynamic_classes_file = lusearch.dyn
				tamiflex_facts_file = lusearch.tfx
				jre = jre/rt-1.4.2_11.jar*/
				classpath += ":"+"lusearch-deps.jar";
				mainclass = "dacapo.lusearch.Main2";
				processdir = "lusearch.jar";
				break;
			case "pmd":
				application_includes = "<dacapo.pmd.:<net.sourceforge.pmd.";
				/*dynamic_classes_file = pmd.dyn
				tamiflex_facts_file = pmd.tfx
				jre = jre/rt-1.4.2_11.jar*/
				classpath += ":"+"pmd-deps.jar";
				mainclass = "dacapo.pmd.Main2";
				processdir = "pmd.jar";
				break;
			case "xalan":
				application_includes = "<dacapo.xalan.:<org.apache.xalan.:<org.apache.xml.dtm.:<org.apache.xml.utils.:<org.apache.xpath.:<org.w3c.dom.xpath.";
				/*dynamic_classes_file = xalan.dyn
				tamiflex_facts_file = xalan.tfx
				jre = jre/rt-1.4.2_11.jar*/
				classpath += ":"+"xalan-deps.jar";
				mainclass = "dacapo.xalan.Main2";
				processdir = "xalan.jar";
				break;
			}
			GlobalVariables.mainclass = mainclass;
		}else {
			classpath = GlobalVariables.classpath;
			mainclass = GlobalVariables.mainclass;
			processdir = GlobalVariables.processdir;
		} 

		Options.v().set_soot_classpath(classpath);
		Options.v().set_main_class(mainclass);
		Options.v().set_whole_program(true);
		Options.v().set_output_format(Options.output_format_none);
		//Options.v().set_prepend_classpath(true);
		//Options.v().set_no_bodies_for_excluded(true);
		Options.v().set_include_all(true);
		Options.v().set_allow_phantom_refs(true);
		List<String> processDirs = new LinkedList<String>();


		for (String ap : processdir.split(File.pathSeparator))
			processDirs.add(ap);
		Options.v().set_process_dir(processDirs);
		/*Options.v().setPhaseOption("cg", "all-reachable:true");
		Options.v().setPhaseOption("cg.spark", "verbose:true");
		Options.v().setPhaseOption("cg.spark", "on");
		Options.v().setPhaseOption("cg.spark", "geom-pta:true");
		Options.v().setPhaseOption("cg.spark", "geom-runs:1");*/

		//Options.v().setPhaseOption("cg.spark", "pre-jimplify");

		Scene.v().addBasicClass(mainclass, SootClass.BODIES);
	}

	/*
	 * Traverse reachable methods, and for each method:
	 *   * build read/write sets for each allocation site
	 *   * query pairs of elements (one from read, one from write OR
	 *     both from write) to see whether they may alias. if they do
	 *     then there may be data races between them.
	 *   * prune: must alias analysis on locks (optional)
	 * 
	 */
	@SuppressWarnings("unchecked")
	@Override
	protected void internalTransform(String phaseName, Map options) {
		if (Util.SOAP12) {
			if (Util.USE_CACHE) {
				throw new RuntimeException("SOAP12 should not use caching!!!");
			}
		}

		Util.mayAliasTime = 0;
		Util.sparkFalsePairs = 0;
		//		Util.numAppMtds = 0;
		//		Util.numLibMtds = 0;
		Set<AliasQuery> aliasqueries = (new QueriesCollectorDacapo()).collectQueries(application_includes);
		TypeCollector.v().apply(aliasqueries);
		AliasGlobalVariables.aliasqueries = aliasqueries;

		/*--BASIC, SMART and BATCH--*/
		/*DRIVER HERE: pass one of the constants of AnalysisVariant. Run only one implementation variant at a time.*/
		runAliasAnalysisImpl(AnalysisVariant.BATCH);
		//runAliasAnalysisImpl(AnalysisVariant.SBATCH);
		//runAliasAnalysisImpl(AnalysisVariant.RT);
		//runAliasAnalysisImpl(AnalysisVariant.VC);
		//runAliasAnalysisImpl(AnalysisVariant.SMART);
		//runAliasAnalysisImpl(AnalysisVariant.BASIC);

		/*--SPARK--*/
		//raceDetectionUsingSPARK(aliasqueries);
		//PrecisionCompare.v().printResults(8, false, false);

		/*--Manu--*/
		//Util.MAY_ALIAS  = "manu";
		//maa = Util.getMayAliasAnalysis();
		//raceDetectionUsingManusPT(aliasqueries, maa);

		//System.out.println("Results size : Batch : "+ AliasGlobalVariables.results.size());
		//System.out.println("Results size : Related Work : "+ AliasGlobalVariables.results_original.size());
		/*--Comparison of results--*/
		/*int numTrue=0, numFalse=0;
		for(Entry<AliasQuery,Boolean> entry: AliasGlobalVariables.results_original.entrySet()){
			if(entry.getValue().booleanValue() == true){
				numTrue++;
			}else{
				numFalse++;
			}
		}
		System.out.println("Precision Related : Num of trues : "+numTrue+"Num of falsess : "+numFalse);

		int matches=0, nonmatches=0;
		for(Entry<AliasQuery,Boolean> entry: AliasGlobalVariables.results.entrySet()){
			AliasQuery aliasQuery = entry.getKey();
			if(AliasGlobalVariables.results_original.get(aliasQuery).booleanValue() == entry.getValue().booleanValue()){
				matches++;
			}else{
				nonmatches++;
				System.out.println("Answer is different for the query: "+aliasQuery);
				System.out.println("Batch : "+entry.getValue()+" Related work : "+AliasGlobalVariables.results_original.get(aliasQuery).booleanValue());
			}
		}

		System.out.println("Number of alias queries :"+aliasqueries.size());
		System.out.println("Precision: Num of matches : "+matches+"Num of non-matches : "+nonmatches);
		 */

		/*PrecisionCompare.v().dumpTrace(1);
		PrecisionCompare.v().dumpTrace(2);
		PrecisionCompare.v().dumpTrace(3);
		PrecisionCompare.v().dumpTrace(4);
		PrecisionCompare.v().dumpTrace(5);
		PrecisionCompare.v().dumpTrace(7);*/

		Util.totalAnalysisTime = System.currentTimeMillis() - Util.totalAnalysisTime;
		//	int queries = instanceFieldWrites.size() * (instanceFieldReads.size());
		//+
		//	arrayElementWrites.size() * (arrayElementWrites.size() + arrayElementReads.size());
		String prefix = "[6e9waprU." + Util.BENCH_NAME + "." + Util.MAY_ALIAS + (Util.USE_SUMMARY ? ".summ" : ".nosumm") + "] ";
		//	System.out.println(prefix + "Total Time: " + (end - start) + ", Time: " + (Util.mayAliasTime / 1000000) + " ms, #SparkFalse: " + Util.sparkFalsePairs + ", #Aliases: " + numRaces + ", #Queries: " + queries);

		//		System.out.printf("[END] numAppMtds: %d, numLibMtds: %d\n", Util.numAppMtds, Util.numLibMtds);
		//	System.exit(-1);

	}

	private void runAliasAnalysisImpl(AnalysisVariant variant){
		Set<AliasQuery> aliasqueries = AliasGlobalVariables.aliasqueries;
		BatchAnalysisInitiator aliasPathReuser = new BatchAnalysisInitiator();
		MayAliasAnalysis maa = Util.getMayAliasAnalysis();
		long start,end, elapsedTime;
		switch(variant){
		case BATCH:
			System.out.println("Running BATCH version!!");
			Util.budgetExceptionCount = 0;
			start = System.currentTimeMillis();
			aliasPathReuser.processQueriesInBatch(aliasqueries);
			end = System.currentTimeMillis();
			elapsedTime = end - start;
			System.out.println("Time taken by batch analysis : "+ ((float)elapsedTime/(float)1000));
			System.out.println("Out of budget exceptions in batch analysis: "+Util.budgetExceptionCount);
			PrecisionCompare.v().printResults(9, false, false);
			break;
		case SBATCH:
			System.out.println("Running Batch with OPT (S-BATCH) version!!");
			Util.budgetExceptionCount = 0;
			start = System.currentTimeMillis();
			aliasPathReuser.processQueriesInBatchWithOPT(aliasqueries);
			end = System.currentTimeMillis();
			elapsedTime = end - start;
			System.out.println("Time taken by batch analysis with OPT: "+ ((float)elapsedTime/(float)1000));
			System.out.println("Out of budget exceptions in batch analysis with OPT: "+Util.budgetExceptionCount);
			PrecisionCompare.v().printResults(10, false, false);
			break;
		case RT:
			System.out.println("Running RT version!!");
			int exceptions2 = 0;
			Util.budgetExceptionCount = 0;
			PAMain.ALGO = 2;
			start = System.currentTimeMillis();
			raceDetection(aliasqueries, maa);
			end = System.currentTimeMillis();

			long elapsedTime2 = end - start;
			exceptions2 = Util.budgetExceptionCount;
			System.out.println("Time  -- opt1: "+ ((float)elapsedTime2/(float)1000));
			System.out.println("Out of budget exceptions: "+exceptions2);
			PrecisionCompare.v().printResults(2, false, false);

			break;
		case VC:
			System.out.println("Running VC version!!");
			int exceptions3 = 0;
			Util.budgetExceptionCount = 0;
			PAMain.ALGO = 3;
			start = System.currentTimeMillis();
			raceDetection(aliasqueries, maa);
			end = System.currentTimeMillis();

			long elapsedTime3 = end - start;
			exceptions3 = Util.budgetExceptionCount;
			System.out.println("Time  -- opt2: "+ ((float)elapsedTime3/(float)1000));
			System.out.println("Out of budget exceptions: "+exceptions3);
			PrecisionCompare.v().printResults(3, false, false);
			break;
		case SMART:
			System.out.println("Running SMART version!!");
			int exceptions5 = 0;
			Util.budgetExceptionCount = 0;
			PAMain.ALGO = 5;
			start = System.currentTimeMillis();
			raceDetection(aliasqueries, maa);
			end = System.currentTimeMillis();

			long elapsedTime5 = end - start;
			exceptions5 = Util.budgetExceptionCount;
			System.out.println("Time  -- opt1 & opt2: "+ ((float)elapsedTime5/(float)1000));
			System.out.println("Out of budget exceptions: "+exceptions5);
			PrecisionCompare.v().printResults(5, false, false);

			break;
		case BASIC:
			System.out.println("Running BASIC version!!");
			int exceptions1 = 0;
			Util.budgetExceptionCount = 0;
			PAMain.ALGO = 1;
			start = System.currentTimeMillis();
			raceDetection(aliasqueries, maa);
			end = System.currentTimeMillis();

			long elapsedTime1 = end - start;
			exceptions1 = Util.budgetExceptionCount;
			System.out.println("Time  -- No opt : "+ ((float)elapsedTime1/(float)1000));
			System.out.println("Out of budget exceptions: "+exceptions1);
			PrecisionCompare.v().printResults(1, false, false);
			break;
		}
	}

	private void raceDetectionUsingSPARK(Set<AliasQuery> aliasqueries){
		for (AliasQuery query : aliasqueries) {
			Local l1 = query.getL1();
			SootMethod m1 = query.getM1();
			Local l2 = query.getL2();
			SootMethod m2 = query.getM2();
			PrecisionCompare.v().getTechnique8().put(query, PAMain.v().sparkMayAlias(l1, m1, l2, m2));
		}
	}

	private void raceDetectionUsingManusPT(Set<AliasQuery> aliasqueries, MayAliasAnalysis maa){
		for (AliasQuery query : aliasqueries) {
			Local l1 = query.getL1();
			SootMethod m1 = query.getM1();
			Local l2 = query.getL2();
			SootMethod m2 = query.getM2();
			PrecisionCompare.v().getTechnique1().put(query, Util.mayAlias(l1, m1, l2, m2, maa));
		}
	}
	//int qcnt =0;
	private void raceDetection(Set<AliasQuery> aliasqueries, MayAliasAnalysis maa) {
		long elapsedTime = (long) 0.0;
		AliasGlobalVariables.nonConservativeAns = false;

		for (AliasQuery query : aliasqueries) {
			Local l1 = query.getL1();
			SootMethod m1 = query.getM1();
			Local l2 = query.getL2();
			SootMethod m2 = query.getM2();

			boolean res = true;
			Util.traversedNodes =0;

			//System.out.println(query);
			long start = System.currentTimeMillis();

			res = Util.mayAlias(l1, m1, l2, m2, maa);

			//System.out.println(res);
			long end = System.currentTimeMillis();
			elapsedTime += (end - start);

			/*if(AliasGlobalVariables.nonConservativeAns){*/
			switch(PAMain.ALGO){
			case 1:
				PrecisionCompare.traverseNodes1.put(query, Util.traversedNodes);
				break;
			case 2:
				PrecisionCompare.traverseNodes2.put(query, Util.traversedNodes);
				break;
			case 3:
				PrecisionCompare.traverseNodes3.put(query, Util.traversedNodes);
				break;
			case 5:
				PrecisionCompare.traverseNodes5.put(query, Util.traversedNodes);
				break;
			}
			/*	AliasGlobalVariables.nonConservativeAns = false;
			}*/


			//System.out.println("time for this query : "+(end-start) + "Ans : "+res);
			/*if(AliasGlobalVariables.metGlobalVar){
				//	System.out.println("reached global and looking for");
				AliasGlobalVariables.metGlobalVar = false;
				res = Util.mayAlias(l2, m2, l1, m1, maa);
			}

			if(AliasGlobalVariables.metGlobalVar){
				AliasGlobalVariables.metGlobalVar = false;
			}*/

			switch(PAMain.ALGO){
			case 1:
				PrecisionCompare.v().getTechnique1().put(query, res);
				PrecisionCompare.tech1Time.put(query, (end - start));
				break;
			case 2:
				PrecisionCompare.v().getTechnique2().put(query, res);
				PrecisionCompare.tech2Time.put(query, (end - start));
				break;
			case 3:
				PrecisionCompare.v().getTechnique3().put(query, res);
				PrecisionCompare.tech3Time.put(query, (end - start));
				break;
			case 5:
				PrecisionCompare.v().getTechnique5().put(query, res);
				PrecisionCompare.tech5Time.put(query, (end - start));
				break;
			}
			//PrecisionCompare.v().getTechnique3().put(query, res);

		}
		System.out.println("Total time for queries : "+ ((float)elapsedTime/(float)1000));
		//System.out.println("Budget Exceptions : "+Util.budgetExceptionCount);
	}
}



