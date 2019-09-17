package edu.iitm.cse.common.dsmodels;

public class MutableInt {

	int value;
	
	public MutableInt(int value) {
		this.value = value;
	}
	

	public int getValue() {
		return value;
	}

	public void setValue(int value) {
		this.value = value;
	}
	
	public void increment(){
		this.value++;
	}
}
