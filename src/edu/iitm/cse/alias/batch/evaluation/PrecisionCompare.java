package edu.iitm.cse.alias.batch.evaluation;

import java.util.HashMap;
import java.util.Map.Entry;

import javax.management.Query;

import edu.iitm.cse.alias.batch.dsmodels.AliasGlobalVariables;
import edu.iitm.cse.alias.batch.dsmodels.AliasQuery;

/**
 * @author Jyothi Vedurada
 * @since Mar 9, 2019
 */
public class PrecisionCompare {
	private static PrecisionCompare theInst;

	HashMap<AliasQuery,Boolean> technique1 = new HashMap<>();
	HashMap<AliasQuery,Boolean> technique2 = new HashMap<>();
	HashMap<AliasQuery,Boolean> technique3 = new HashMap<>();
	HashMap<AliasQuery,Boolean> technique4 = new HashMap<>();
	HashMap<AliasQuery,Boolean> technique5 = new HashMap<>();
	HashMap<AliasQuery,Boolean> technique8 = new HashMap<>();

	public static HashMap<AliasQuery,Long> tech1Time = new HashMap<>();
	public static HashMap<AliasQuery,Long> tech2Time = new HashMap<>();
	public static HashMap<AliasQuery,Long> tech3Time = new HashMap<>();
	public static HashMap<AliasQuery,Long> tech4Time = new HashMap<>();
	public static HashMap<AliasQuery,Long> tech5Time = new HashMap<>();
	public static HashMap<AliasQuery,Long> tech8Time = new HashMap<>();

	public static HashMap<AliasQuery, Integer> traverseNodes1 = new HashMap<>();
	public static HashMap<AliasQuery, Integer> traverseNodes2 = new HashMap<>();
	public static HashMap<AliasQuery, Integer> traverseNodes3 = new HashMap<>();
	public static HashMap<AliasQuery, Integer> traverseNodes4 = new HashMap<>();
	public static HashMap<AliasQuery, Integer> traverseNodes5 = new HashMap<>();
	public static HashMap<AliasQuery, Integer> traverseNodes8 = new HashMap<>();

	public static PrecisionCompare v() {
		if (theInst == null) {
			theInst = new PrecisionCompare();		
		}
		return theInst;
	}

	public HashMap<AliasQuery, Boolean> getTechnique1() {
		return technique1;
	}
	public void setTechnique1(HashMap<AliasQuery, Boolean> technique1) {
		this.technique1 = technique1;
	}
	public HashMap<AliasQuery, Boolean> getTechnique2() {
		return technique2;
	}
	public void setTechnique2(HashMap<AliasQuery, Boolean> technique2) {
		this.technique2 = technique2;
	}
	public HashMap<AliasQuery, Boolean> getTechnique3() {
		return technique3;
	}
	public void setTechnique3(HashMap<AliasQuery, Boolean> technique3) {
		this.technique3 = technique3;
	}
	public HashMap<AliasQuery, Boolean> getTechnique4() {
		return technique4;
	}
	public void setTechnique4(HashMap<AliasQuery, Boolean> technique4) {
		this.technique4 = technique4;
	}
	public HashMap<AliasQuery, Boolean> getTechnique5() {
		return technique5;
	}
	public void setTechnique5(HashMap<AliasQuery, Boolean> technique5) {
		this.technique5 = technique5;
	}

	public HashMap<AliasQuery, Boolean> getTechnique8() {
		return technique8;
	}

	public void setTechnique8(HashMap<AliasQuery, Boolean> technique8) {
		this.technique8 = technique8;
	}

	public void printSPARKVsFASTApproxResults(){
		System.out.println("Precision w.r.to SPARK:");
		calculatePrecision(technique1, technique2);
		//TODO: also compare the precision w.r.to Manu Sridharan's work.
	}

	public void dumpTrace(int caseNo){
		switch(caseNo){
		case 1: System.out.println("case 1");
			printAllInfo(technique1, tech1Time, traverseNodes1);
			break;
		case 2: System.out.println("case 2");
			printAllInfo(technique2, tech2Time, traverseNodes2);
			break;
		case 3: System.out.println("case 3");
			printAllInfo(technique3, tech3Time, traverseNodes3);
			break;
		case 4: System.out.println("case 4");
			printAllInfo(technique4, tech4Time, traverseNodes4);
			break;
		case 5: System.out.println("case 5");
			printAllInfo(technique5, tech5Time, traverseNodes5);
			break;
		}
	}

	public void printAllInfo(HashMap<AliasQuery,Boolean> answers, HashMap<AliasQuery,Long> time,
			HashMap<AliasQuery, Integer> exceptions){
		for(AliasQuery query : answers.keySet()){
			System.out.println("Query: "+query.getID()+ " Time: "+time.get(query)+
					" Answer: "+answers.get(query)+ " Budget Exp: "+exceptions.get(query));
		}
	}

	public void printResults(int caseNo, boolean verifyOPT1, boolean verifyBatch){
		int yes = 0, no=0;
		switch(caseNo){
		case 1:
			yes = 0; no=0;
			System.out.println("Precision of vanilla analysis:");
			for(Entry<AliasQuery,Boolean> entry : technique1.entrySet()){
				if(entry.getValue() == true)
					yes++;
				else
					no++;
			}

			System.out.println("YES: "+yes+"  NO: "+no);
			System.out.println(" Timings using SPARK as pre-analysis: ");
			System.out.println("Time  -- No opt : "+calculatePerformanceWRTSpark(tech1Time, technique8,technique1));
			break;
		case 2:
			yes = 0; no=0;
			System.out.println("Precision of opt1 analysis:");
			for(Entry<AliasQuery,Boolean> entry : technique2.entrySet()){
				if(entry.getValue() == true)
					yes++;
				else
					no++;
			}

			System.out.println("YES: "+yes+"  NO: "+no);
			System.out.println(" Timings using SPARK as pre-analysis: ");
			System.out.println("Time  -- opt1: "+calculatePerformanceWRTSpark(tech2Time,technique8,technique2));
			break;
		case 3:
			yes = 0; no=0;
			System.out.println("Precision of opt2 analysis:");
			for(Entry<AliasQuery,Boolean> entry : technique3.entrySet()){
				if(entry.getValue() == true)
					yes++;
				else
					no++;
			}

			System.out.println("YES: "+yes+"  NO: "+no);
			System.out.println(" Timings using SPARK as pre-analysis: ");
			System.out.println("Time  -- opt2: "+calculatePerformanceWRTSpark(tech3Time,technique8,technique3));
			break;
		case 4:
			yes = 0; no=0;
			System.out.println("Precision of opt3 analysis:");
			for(Entry<AliasQuery,Boolean> entry : technique4.entrySet()){
				if(entry.getValue() == true)
					yes++;
				else
					no++;
			}

			System.out.println("YES: "+yes+"  NO: "+no);
			System.out.println(" Timings using SPARK as pre-analysis: ");
			System.out.println("Time  -- opt3: "+calculatePerformanceWRTSpark(tech4Time,technique8,technique4));
			break;
		case 5:
			yes = 0; no=0;
			System.out.println("Precision of opt1 & opt2 analysis:");
			for(Entry<AliasQuery,Boolean> entry : technique5.entrySet()){
				if(entry.getValue() == true)
					yes++;
				else
					no++;
			}

			System.out.println("YES: "+yes+"  NO: "+no);
			System.out.println(" Timings using SPARK as pre-analysis: ");
			System.out.println("Time  -- opt1 & 2: "+calculatePerformanceWRTSpark(tech5Time, technique8,technique5));
			break;
		case 8:
			yes = 0; no=0;
			System.out.println("Precision of SPARK analysis:");
			for(Entry<AliasQuery,Boolean> entry : technique8.entrySet()){
				if(entry.getValue() == true)
					yes++;
				else
					no++;
			}

			System.out.println("YES: "+yes+"  NO: "+no);
			break;
		case 9:
			yes = 0; no=0;
			System.out.println("Precision of Batch analysis without OPT:");
			for(Entry<AliasQuery,Boolean> entry : AliasGlobalVariables.results.entrySet()){
				if(entry.getValue() == true)
					yes++;
				else
					no++;
			}

			System.out.println("YES: "+yes+"  NO: "+no);
			System.out.println("Precision of Batch with SPARK as pre-analysis: ");
			System.out.println("Batch Without OPT : ");
			calculatePrecisionWRTSpark(technique8, AliasGlobalVariables.results);
			break;
		case 10:
			yes = 0; no=0;
			System.out.println("Precision of Batch analysis with OPT:");
			for(Entry<AliasQuery,Boolean> entry : AliasGlobalVariables.results_original.entrySet()){
				if(entry.getValue() == true)
					yes++;
				else
					no++;
			}

			System.out.println("YES: "+yes+"  NO: "+no);
			System.out.println("Precision of Batch with SPARK as pre-analysis: ");
			System.out.println("Batch With OPT : ");
			calculatePrecisionWRTSpark(technique8, AliasGlobalVariables.results_original);
			break;
		}

		/*yes = 0; no=0;
		System.out.println("Precision of all opt:");
		for(Entry<AliasQuery,Boolean> entry : technique6.entrySet()){
			if(entry.getValue() == true)
				yes++;
			else
				no++;
		}

		System.out.println("YES: "+yes+"  NO: "+no);*/

		//calculatePerformance();

		if(verifyBatch){
			System.out.println("Precision comparison of Batch w.r.to vanilla:");
			calculatePrecision(AliasGlobalVariables.results, technique1);
			System.out.println("Precision comparison of BatchOPT w.r.to vanilla:");
			calculatePrecision(AliasGlobalVariables.results_original, technique1);
			System.out.println("Precision comparison of Batch w.r.to allOPT:");
			calculatePrecision(AliasGlobalVariables.results, technique8);
			System.out.println("Precision comparison of BatchOPT w.r.to SPARK:");
			calculatePrecision(AliasGlobalVariables.results_original, technique8);
		}
		//System.out.println("Time  -- opt1 & 2 & 3: "+calculatePerformanceWRTSpark(tech6Time,technique8,technique6));
	}

	public void calculatePrecisionWRTSpark(HashMap<AliasQuery,Boolean> map2, HashMap<AliasQuery,Boolean> map3){
		int numRaces = 0;
		int numQueries = 0;
		for(Entry<AliasQuery,Boolean> entry : map2.entrySet()){
			Boolean sparkVal = map2.get(entry.getKey());
			Boolean predVal = map3.get(entry.getKey());
			if(sparkVal.booleanValue() == true){
				numQueries++;
				if(predVal.booleanValue() == false){
					numRaces++;
				}
			}
		}
		System.out.println("Num Queries after SPARK pre: "+numQueries );
		System.out.println("Num races (NOs) after SPARK pre: "+numRaces );
	}

	public float calculatePerformanceWRTSpark(HashMap<AliasQuery,Long> map1, HashMap<AliasQuery,Boolean> map2, HashMap<AliasQuery,Boolean> map3){
		Long elapsedTime = (long) 0.0f;
		int numRaces = 0;
		int numQueries = 0;
		for(Entry<AliasQuery,Boolean> entry : map2.entrySet()){
			Long time = map1.get(entry.getKey());
			Boolean sparkVal = map2.get(entry.getKey());
			Boolean predVal = map3.get(entry.getKey());
			if(sparkVal.booleanValue() == true){
				elapsedTime += time.longValue();
				numQueries++;
				if(predVal.booleanValue() == false){
					numRaces++;
				}
			}
		}
		System.out.println("Num races (NOs) after SPARK pre: "+numRaces );
		System.out.println("Num Queries after SPARK pre: "+numQueries );
		return ((float)elapsedTime/(float)1000.0f);
	}

	public void calculatePerformance(){
		int improve = 0;
		int cnt = 0;
		Long time1 = (long) 0.0;
		Long time2 = (long) 0.0;
		for(Entry<AliasQuery,Integer> entry1 : traverseNodes1.entrySet()){
			if(traverseNodes2.containsKey(entry1.getKey())){
				if(entry1.getValue().intValue() < traverseNodes2.get(entry1.getKey()).intValue()){
					System.out.println("can be negative as well");
				}
				improve += entry1.getValue().intValue()-traverseNodes2.get(entry1.getKey()).intValue();
				cnt++;
				time1 += tech1Time.get(entry1.getKey());
				time2 += tech2Time.get(entry1.getKey());
				//System.out.println(entry1.getKey());
				//System.out.println(" without type : "+entry1.getValue().intValue() + " with type : "+traverseNodes2.get(entry1.getKey()).intValue());
				if(technique1.get(entry1.getKey()).booleanValue() != technique2.get(entry1.getKey()).booleanValue()){
					System.out.println("Opt : "+technique1.get(entry1.getKey()).booleanValue()+"No opt : "+technique2.get(entry1.getKey()).booleanValue());
					System.out.println("query : "+entry1.getKey());
				}
			}else{
				System.out.println("Some issue");
				System.out.println("query : "+entry1.getKey());
				System.out.println("Opt : "+technique1.get(entry1.getKey()).booleanValue()+"No opt : "+technique2.get(entry1.getKey()).booleanValue());
			}
		}

		System.out.println("Total impr in Nodes with opt1 : "+improve + " : "+cnt);
		System.out.println("Avg imr in Nodes with opt1 : "+(float)improve/(float)cnt);
		System.out.println("Time Improvement with opt1 : "+ ((float)(time2-time1)/(float)1000.0f)  + "without types: "+ ((float)(time1)/(float)1000.0f)  + "with types : "+ ((float)(time2)/(float)1000.0f) );

		improve = 0;
		cnt = 0;
		time1 = (long) 0.0;
		time2 = (long) 0.0;
		for(Entry<AliasQuery,Integer> entry1 : traverseNodes3.entrySet()){
			if(traverseNodes5.containsKey(entry1.getKey())){
				if(entry1.getValue().intValue() < traverseNodes5.get(entry1.getKey()).intValue()){
					System.out.println("can be negative as well");
				}
				improve += entry1.getValue().intValue()-traverseNodes5.get(entry1.getKey()).intValue();
				cnt++;
				time1 += tech3Time.get(entry1.getKey());
				time2 += tech5Time.get(entry1.getKey());
				//	System.out.println(entry1.getKey());
				//	System.out.println(" without type : "+entry1.getValue().intValue() + " with type : "+traverseNodes4.get(entry1.getKey()).intValue());
				if(technique3.get(entry1.getKey()).booleanValue() != technique5.get(entry1.getKey()).booleanValue()){
					System.out.println("Opt : "+technique3.get(entry1.getKey()).booleanValue()+"No opt : "+technique5.get(entry1.getKey()).booleanValue());
					System.out.println("query : "+entry1.getKey());
				}
			}else{
				System.out.println("Some issue");
				System.out.println("query : "+entry1.getKey());
				System.out.println("Opt : "+technique3.get(entry1.getKey()).booleanValue()+"No opt : "+technique5.get(entry1.getKey()).booleanValue());
			}
		}

		System.out.println("Total impr in Nodes with opt1 & opt2 : "+improve + " : "+cnt);
		System.out.println("Avg impr in Nodes with opt1 & opt2 : "+(float)improve/(float)cnt );
		System.out.println("Time Improvement with opt1 & opt2: "+ ((float)(time2-time1)/(float)1000.0f) + "without types: "+((float)(time1)/(float)1000.0f)  + "with types : "+((float)(time2)/(float)1000.0f) );
	}

	public void calculatePrecision(HashMap<AliasQuery, Boolean> map1, HashMap<AliasQuery, Boolean> map2){
		int truePos = 0;
		int falsePos = 0;
		int trueNeg = 0;
		int falseNeg = 0;
		for(Entry<AliasQuery,Boolean> entry : map2.entrySet()){
			Boolean predictedVal = map1.get(entry.getKey());
			if(entry.getValue().equals(predictedVal)){
				if(predictedVal.booleanValue()){
					truePos++;
				}else{
					trueNeg++;
				}
			}else{
				if(predictedVal.booleanValue()){
					falsePos++;
					//System.out.println("false positive: "+entry.getKey());
				}else{
					falseNeg++;
				}
			}
		}

		System.out.println("True Positives: "+truePos);
		System.out.println("False Positives: "+falsePos);
		System.out.println("True Negatives: "+trueNeg);
		System.out.println("False Negatives: "+falseNeg);
	}

	public void calculatePrecisionAgainst2(HashMap<AliasQuery, Boolean> map1, HashMap<AliasQuery, Boolean> map2, HashMap<AliasQuery, Boolean> map3){
		int truePos = 0;
		int falsePos = 0;
		int trueNeg = 0;
		int falseNeg = 0;
		for(Entry<AliasQuery,Boolean> entry : map1.entrySet()){
			Boolean predictedVal = map1.get(entry.getKey());
			Boolean sparkVal = map2.get(entry.getKey());
			Boolean demandVal = map3.get(entry.getKey());

			if(predictedVal  == false){
				if(sparkVal == false){
					trueNeg++;
				}else if(demandVal == false){
					trueNeg++;
				}else{
					falseNeg++;	
					System.out.println("false Neg: "+entry.getKey());
				}

			}else{
				if(sparkVal == false){
					falsePos++;
				}else if(demandVal == false){
					falsePos++;
				}else
					truePos++;		
			}
		}

		System.out.println("True Positives: "+truePos);
		System.out.println("False Positives: "+falsePos);
		System.out.println("True Negatives: "+trueNeg);
		System.out.println("False Negatives: "+falseNeg);
	}
}
