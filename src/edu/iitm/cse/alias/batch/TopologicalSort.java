package edu.iitm.cse.alias.batch;

import java.util.ArrayList;
import java.util.HashSet;

import soot.util.MultiMap;

public class TopologicalSort<T> {
	   HashSet<T> visited;
	   //it is actually reverse topological order with root at the end.
	   ArrayList<T> topoOrder;
	   MultiMap<T, T> map;
	   
	   public TopologicalSort() {
		   visited = new HashSet<T>();
	   }
	   
	   public ArrayList<T> topologicalSort(MultiMap<T, T> map) {
		   topoOrder = new ArrayList<T>();
		   this.map = map;
		   for(T key: map.keySet()) {
			   if(!visited.contains(key)) {
				   visitChildren(key);
			   }
		   }
		   return topoOrder;
	   }
	   
	   void visitChildren(T cls_nm) {
		   if(visited.contains(cls_nm))
			   return;
		   visited.add(cls_nm);
		   if(map.get(cls_nm) != null) {
			   for(T other_cls: map.get(cls_nm)) {
				   visitChildren(other_cls);
			   }
		   }
		   topoOrder.add(cls_nm);
	   }
}
