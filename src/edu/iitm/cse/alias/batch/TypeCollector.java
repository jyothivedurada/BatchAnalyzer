package edu.iitm.cse.alias.batch;

import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import edu.iitm.cse.alias.batch.dsmodels.AliasGlobalVariables;
import edu.iitm.cse.alias.batch.dsmodels.AliasQuery;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.Type;

/**
 * @author Jyothi Vedurada
 * @since April 14, 2019
 */
public class TypeCollector {
		private static TypeCollector instance;
		private boolean applied;

		public static TypeCollector v() {
			if(instance == null) {
				instance = new TypeCollector();
			}
			return instance;
		}

		public void apply(Set<AliasQuery> aliasqueries) {	
			/*if(applied)
				return;*///TODO: remove this

			long start = System.currentTimeMillis();
			collectTypes(aliasqueries);
			long end = System.currentTimeMillis();

			long elapsedTime = end - start;

			System.out.println("Time elapsed -- methods selection : "+elapsedTime);

			int numTypes = Scene.v().getClasses().size();

			float sum = 0.0f;
			int sumTypes = 0;
			for(Entry<Type, HashSet<Type>> entry : AliasGlobalVariables.relevantTypesMap.entrySet()){
				HashSet<Type> types = new HashSet<>();
				types.addAll(entry.getValue());
				types.addAll(AliasGlobalVariables.defEnclTypes);
				sum += (float)types.size()/(float)numTypes;
				sumTypes += types.size();
				//System.out.println("Percentage of relevant types : "+ (float)entry.getValue().size()/(float)numTypes + " : "+entry.getValue().size() + " : "+numTypes );
				/*for(SootClass cc : Scene.v().getClasses()){
					if(!types.contains(cc.getType())){
						System.out.println("Not relevant : "+cc);
					}
				}
				break;*/
			}
			System.out.println("Avg percentage: "+ ((float)sum/(float)AliasGlobalVariables.relevantTypesMap.keySet().size())*100);
			System.out.println("Avg relevant types: "+ ((float)sumTypes/(float)AliasGlobalVariables.relevantTypesMap.keySet().size()));
			System.out.println("Total classes : "+numTypes);

			int numApplTypes = Scene.v().getApplicationClasses().size();
			System.out.println("Application classes : "+numApplTypes);

			sum = 0.0f;
			sumTypes = 0;
			for(Entry<Type, HashSet<Type>> entry : AliasGlobalVariables.relevantTypesMap.entrySet()){
				int appTypes =0;
				HashSet<Type> types = new HashSet<>();
				types.addAll(entry.getValue());
				types.addAll(AliasGlobalVariables.defEnclTypes);
				for(Type typ : types){
					if(typ instanceof RefType){
						if(((RefType)typ).getSootClass().isApplicationClass())
							appTypes++;
					}
				}
				sum += (float)appTypes/(float)numApplTypes;
				sumTypes += appTypes;
				//System.out.println("Percentage of relevant types : "+ (float)entry.getValue().size()/(float)numTypes + " : "+entry.getValue().size() + " : "+numTypes );
			}

			System.out.println("Avg app percentage: "+ ((float)sum/(float)AliasGlobalVariables.relevantTypesMap.keySet().size())*100);
			System.out.println("Avg relevant app types: "+ ((float)sumTypes/(float)AliasGlobalVariables.relevantTypesMap.keySet().size()));

			applied = true;
		}

		public void collectTypes(Set<AliasQuery> queries){
			HashSet<Type> defaultDirTypes = new HashSet<>();
			HashSet<Type> defaultEnclTypes = new HashSet<>();

			defaultDirTypes.add(Scene.v().getSootClass("java.lang.Object").getType());
			int sizeBefore = 0;
			int sizeAfter = 0;
			do {
				sizeBefore = defaultEnclTypes.size();
				//calculate default classes
				for (SootClass sc : Scene.v().getClasses()) {
					if(sc.isPhantom()) continue;
					HashSet<SootClass> visited = new HashSet<SootClass>();
					//System.out.println("New : "+sc.getType());
					if(!(defaultDirTypes.contains(sc.getType()) || defaultEnclTypes.contains(sc.getType())))
						BatchUtil.checkEnclosesDirectType(defaultDirTypes, sc, defaultEnclTypes, visited);
					visited = new HashSet<SootClass>();
				}

				HashSet<Type> oldDefSet = new HashSet<>(defaultEnclTypes);
				for (Type type: oldDefSet){
					SootClass clazz = ((RefType)type).getSootClass(); 
					if(!(clazz.getType().equals(Scene.v().getSootClass("java.lang.Object").getType()))){
						BatchUtil.addSuperTypes(clazz, defaultEnclTypes);
					}
				}
				sizeAfter = defaultEnclTypes.size();
				//System.out.println("iteration");
			}while(sizeAfter != sizeBefore);

			defaultEnclTypes.addAll(defaultDirTypes);
			AliasGlobalVariables.defEnclTypes = defaultEnclTypes;

			for(Type type : defaultEnclTypes){
				type.setAlwaysRelevant(true);
				type.setRelevant(true);
			}

			HashSet<Type> declaredTypes = new HashSet<>();
			//Compute D_all
			for(AliasQuery query: queries){
				Type type1 = query.getL1().getType();
				declaredTypes.add(type1);

				Type type2 = query.getL2().getType();
				if(type1 != type2)
					declaredTypes.add(type2);
				//System.out.println("typ:" +type1 + " : "+type2);
			}

			for(Type type1 : declaredTypes){
				HashSet<Type> directTypes = new HashSet<>();
				directTypes.add(type1);

				SootClass clazz = ((RefType)type1).getSootClass(); 
				BatchUtil.addSubTypesAndSuperTypes(clazz, directTypes);

				HashSet<Type> enclosureTypes = new HashSet<>();
				HashSet<SootClass> visited = new HashSet<SootClass>();

				sizeBefore = 0;
				sizeAfter = 0;
				do {
					sizeBefore = enclosureTypes.size();
					//Compute D'
					for (SootClass sc : Scene.v().getClasses()) {
						if(sc.isPhantom()) continue;
						//System.out.println("New : "+sc.getType());
						if(!(defaultEnclTypes.contains(sc.getType()) || directTypes.contains(sc.getType()) || enclosureTypes.contains(sc.getType()) ))
							BatchUtil.checkEnclosesDirectType(directTypes, sc, enclosureTypes, visited);
						visited = new HashSet<SootClass>();
					}

					HashSet<Type> oldSet = new HashSet<>(enclosureTypes);
					for (Type type: oldSet){
						clazz = ((RefType)type).getSootClass(); 
						if(!(clazz.getType().equals(Scene.v().getSootClass("java.lang.Object").getType()))){
							BatchUtil.addSuperTypes(clazz, enclosureTypes);
						}
					}
					sizeAfter = enclosureTypes.size();
				}while(sizeAfter != sizeBefore);

				enclosureTypes.addAll(directTypes);
				//enclosureTypes.addAll(defaultEnclTypes);
				//System.out.println(enclosureTypes);
				AliasGlobalVariables.relevantTypesMap.put(type1, enclosureTypes);
			}

		}

	}