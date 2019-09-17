package edu.iitm.cse.alias.batch;

import java.util.HashSet;
import java.util.LinkedList;

import soot.AnySubType;
import soot.ArrayType;
import soot.RefLikeType;
import soot.RefType;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.Type;

/**
 * @author Jyothi Vedurada
 * @since Jan 21, 2019
 */
public class BatchUtil {

	public static void addSubTypesAndSuperTypes(SootClass clazz, HashSet<Type> types) {
		if(clazz.isInterface()){
			/* The types which can be stored into the type of clazz: */
			// 1. direct implementers of it
			for (SootClass sootClass : Scene.v().getActiveHierarchy().getImplementersOf(clazz)){ 
				types.add(sootClass.getType());
				for (SootClass sootClass1 : Scene.v().getActiveHierarchy().getSubclassesOfIncluding(sootClass)){
					types.add(sootClass1.getType());
					// 1. super  classes
					for (SootClass sootClass2 : Scene.v().getActiveHierarchy().getSuperclassesOf(sootClass1)){ 
						types.add(sootClass2.getType());
						for (SootClass sootClass4 : sootClass2.getInterfaces()){ 
							types.add(sootClass4.getType());
							for (SootClass sootClass5 : Scene.v().getActiveHierarchy().getSuperinterfacesOf(sootClass4)){
								types.add(sootClass5.getType());
							}
						}
					}
					// 2. super interfaces
					for (SootClass sootClass2 : sootClass1.getInterfaces()){ 
						types.add(sootClass2.getType());
						for (SootClass sootClass3 : Scene.v().getActiveHierarchy().getSuperinterfacesOf(sootClass2)){
							types.add(sootClass3.getType());
						}
					}
				}
			}
			// 2. implementers of its subinterfaces
			for (SootClass sootClass : Scene.v().getActiveHierarchy().getSubinterfacesOf(clazz)){
				types.add(sootClass.getType());

				for (SootClass sootClass1 : Scene.v().getActiveHierarchy().getImplementersOf(sootClass)){ 
					types.add(sootClass1.getType());
					for (SootClass sootClass2 : Scene.v().getActiveHierarchy().getSubclassesOfIncluding(sootClass1)){
						types.add(sootClass2.getType());
						// 1. super classes
						for (SootClass sootClass3 : Scene.v().getActiveHierarchy().getSuperclassesOf(sootClass2)){ 
							types.add(sootClass3.getType());
							for (SootClass sootClass4 : sootClass3.getInterfaces()){ 
								types.add(sootClass4.getType());
								for (SootClass sootClass5 : Scene.v().getActiveHierarchy().getSuperinterfacesOf(sootClass4)){
									types.add(sootClass5.getType());
								}
							}
						}
						// 2. super interfaces
						for (SootClass sootClass3 : sootClass2.getInterfaces()){ 
							types.add(sootClass3.getType());
							for (SootClass sootClass4 : Scene.v().getActiveHierarchy().getSuperinterfacesOf(sootClass3)){
								types.add(sootClass4.getType());
							}
						}
					}
				}
			}

			/* The types into which clazz can be stored */
			for (SootClass sootClass : Scene.v().getActiveHierarchy().getSuperinterfacesOf(clazz)){
				types.add(sootClass.getType());
			}

			/* The types into which all the types that can flow to clazz can be stored */
			// all super types, their directly implemented interfaces and their super interfaces
			//Merged the code into above for loops

		}else {
			/* The types which can be stored into the type of clazz: */
			// all possible subclasses of clazz and their implemented interfaces
			for (SootClass sootClass : Scene.v().getActiveHierarchy().getSubclassesOfIncluding(clazz)){
				types.add(sootClass.getType());
				for (SootClass sootClass1 : sootClass.getInterfaces()){ 
					types.add(sootClass1.getType());
					for (SootClass sootClass2 : Scene.v().getActiveHierarchy().getSuperinterfacesOf(sootClass1)){
						types.add(sootClass2.getType());
					}
				}
			}
			/* The types into which clazz can be stored: */
			// 1. Super classes of clazz and their implemented interfaces
			for (SootClass sootClass : Scene.v().getActiveHierarchy().getSuperclassesOf(clazz)){ 
				types.add(sootClass.getType());
				for (SootClass sootClass1 : sootClass.getInterfaces()){ 
					types.add(sootClass1.getType());
					for (SootClass sootClass2 : Scene.v().getActiveHierarchy().getSuperinterfacesOf(sootClass1)){
						types.add(sootClass2.getType());
					}
				}
			}

			/* The types into which all the types that can flow to clazz can be stored: */
			//all interfaces and super interfaces of all subclasses
			//merged into above code
			/*for (SootClass sootClass : Scene.v().getActiveHierarchy().getSubclassesOf(clazz)){
				for (SootClass sootClass1 : sootClass.getInterfaces()){ 
					types.add(sootClass1.getType());
					for (SootClass sootClass2 : Scene.v().getActiveHierarchy().getSuperinterfacesOf(sootClass1)){
						types.add(sootClass2.getType());
					}
				}
			}*/
		}
		
		/*for(Type type : types){
			if(type.toString().contains("sun.security.util.BitArray")){
				System.out.println("Found BitArray : "+clazz);
				break;
			}
		}*/
	}

	public static boolean checkEnclosesDirectType(HashSet<Type> directTypes, SootClass sc, HashSet<Type> enclosureTypes, HashSet<SootClass> visited) {
		if(visited.contains(sc))
			return false;
		visited.add(sc);
		boolean returnVal = false;
		HashSet<SootField> fields = getDirectAndInheritedFields(sc);
		for(SootField field: fields){
			Type fieldType = field.getType();
			if(!(fieldType instanceof RefLikeType))
				continue;
			if(fieldType instanceof ArrayType)
				fieldType = ((ArrayType)fieldType).baseType;
			if(directTypes.contains(fieldType) || enclosureTypes.contains(fieldType)){
				enclosureTypes.add(sc.getType());
				return true;
			}else if(fieldType instanceof RefType){
				boolean found = checkEnclosesDirectType(directTypes, ((RefType)fieldType).getSootClass(), enclosureTypes, visited);
				if(found){
					enclosureTypes.add(sc.getType());
					return true;
				}
			}
		}

		return returnVal;
	}

	private static HashSet<SootField> getDirectAndInheritedFields(SootClass cl) {
		HashSet<SootField> returnVal = new HashSet<>();
		boolean first = true;
		while(true) {
			if(!cl.isPhantom()){
				if(first){
					returnVal.addAll(cl.getFields());
					first = false;
				} else{
					for (SootField field : cl.getFields()){
						if(!field.isPrivate() || isLibMismatch(field, cl)){
							returnVal.add(field);
						}
					}
				}

				// Since this class is not phantom, we look at its interfaces
				LinkedList<SootClass> queue = new LinkedList<SootClass>();
				queue.addAll( cl.getInterfaces() );
				while( !queue.isEmpty() ) {
					SootClass iface = queue.removeFirst();
					returnVal.addAll(iface.getFields());
					queue.addAll( iface.getInterfaces() );
				}

				// visit the superclass
				if( cl.hasSuperclass() ) cl = cl.getSuperclass();
				else break;
			}else break;
		}
		return returnVal;
	}

	/**
	 * @param field
	 * @return
	 */
	private static boolean isLibMismatch(SootField field, SootClass sc) {
		if((sc.toString().contains("java.util.ArrayList") && field.toString().contains("elementData")) || 
				(sc.toString().contains("org.apache.lucene.util.PriorityQueue") && field.toString().contains("heap"))){
			return true;
		}
			
		return false;
	}

	/**
	 * @param clazz
	 * @param enclosureTypes
	 */
	public static void addSuperTypes(SootClass clazz, HashSet<Type> types) {
		if(clazz.isInterface()){
			for (SootClass sootClass : Scene.v().getActiveHierarchy().getSuperinterfacesOf(clazz)){
				types.add(sootClass.getType());
			}	
		}else{
			for (SootClass sootClass : Scene.v().getActiveHierarchy().getSuperclassesOfIncluding(clazz)){ 
				types.add(sootClass.getType());
				for (SootClass sootClass1 : sootClass.getInterfaces()){ 
					types.add(sootClass1.getType());
					for (SootClass sootClass2 : Scene.v().getActiveHierarchy().getSuperinterfacesOf(sootClass1)){
						types.add(sootClass2.getType());
					}
				}
			}
		}
	}

}
