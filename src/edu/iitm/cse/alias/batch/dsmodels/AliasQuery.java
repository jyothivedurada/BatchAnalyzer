package edu.iitm.cse.alias.batch.dsmodels;

import java.util.Set;

import edu.osu.cse.pa.spg.AbstractAllocNode;
import soot.Local;
import soot.SootMethod;

/**
 * @author Jyothi Vedurada
 * @since Nov 25, 2018
 */
public class AliasQuery {
	static int IDCNTR = 0;
	int ID;
	Local l1;
	Local l2;
	SootMethod m1;
	SootMethod m2;
	Set<AbstractAllocNode> nodes1;
	Set<AbstractAllocNode> nodes2;
	Set<AbstractAllocNode> NonAliasGroupIds; //source nodes of the effective query groups that could not be answered 'yes' or that were answered 'no' 
	boolean isAnswered = false;
	
	public AliasQuery(Local l1, Local l2, SootMethod m1, SootMethod m2) {
		this.ID = IDCNTR++;
		this.l1 = l1;
		this.l2 = l2;
		this.m1 = m1;
		this.m2 = m2;
	}

	public Local getL1() {
		return l1;
	}
	public void setL1(Local l1) {
		this.l1 = l1;
	}
	public Local getL2() {
		return l2;
	}
	public void setL2(Local l2) {
		this.l2 = l2;
	}
	public SootMethod getM1() {
		return m1;
	}
	public void setM1(SootMethod m1) {
		this.m1 = m1;
	}
	public SootMethod getM2() {
		return m2;
	}
	public void setM2(SootMethod m2) {
		this.m2 = m2;
	}
	public Set<AbstractAllocNode> getNodes1() {
		return nodes1;
	}

	public void setNodes1(Set<AbstractAllocNode> nodes1) {
		this.nodes1 = nodes1;
	}

	public Set<AbstractAllocNode> getNodes2() {
		return nodes2;
	}

	public void setNodes2(Set<AbstractAllocNode> nodes2) {
		this.nodes2 = nodes2;
	}

	public boolean isAnswered() {
		return isAnswered;
	}

	public void setAnswered(boolean isAnswered) {
		this.isAnswered = isAnswered;
	}

	public Set<AbstractAllocNode> getNonAliasGroupIds() {
		return NonAliasGroupIds;
	}

	public void setNonAliasGroupIds(Set<AbstractAllocNode> nonAliasGroupIds) {
		NonAliasGroupIds = nonAliasGroupIds;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((l1 == null) ? 0 : l1.hashCode());
		result = prime * result + ((l2 == null) ? 0 : l2.hashCode());
		result = prime * result + ((m1 == null) ? 0 : m1.hashCode());
		result = prime * result + ((m2 == null) ? 0 : m2.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		AliasQuery other = (AliasQuery) obj;
		if (l1 == null) {
			if (other.l1 != null)
				return false;
		} else if (l1 != other.l1)
			return false;
		if (l2 == null) {
			if (other.l2 != null)
				return false;
		} else if (l2 != other.l2)
			return false;
		if (m1 == null) {
			if (other.m1 != null)
				return false;
		} else if (m1 != other.m1)
			return false;
		if (m2 == null) {
			if (other.m2 != null)
				return false;
		} else if (m2 != other.m2)
			return false;
		return true;
	}
	
	public static int getIDCNTR() {
		return IDCNTR;
	}

	public static void setIDCNTR(int iDCNTR) {
		IDCNTR = iDCNTR;
	}

	public int getID() {
		return ID;
	}

	public void setID(int iD) {
		ID = iD;
	}

	@Override
	public String toString() {
		return "AliasQuery:"+ ID +" [l1=" + l1 + ", l2=" + l2 + ", m1=" + m1 + ", m2=" + m2 + ", nodes1=" + nodes1 + ", nodes2="
				+ nodes2 + ", NonAliasGroupIds=" + NonAliasGroupIds + ", isAnswered=" + isAnswered + "]";
	}
}
