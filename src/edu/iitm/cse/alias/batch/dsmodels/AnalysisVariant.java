package edu.iitm.cse.alias.batch.dsmodels;

/**
 * @author Jyothi Vedurada
 * @since Sep 16, 2019
 */
public enum AnalysisVariant {

	BATCH(0),

	SBATCH(1),

	RT(2),

	VC(3),

	BASIC(4),

	SMART(5);


	private int mode;

	private AnalysisVariant(int mode){
		this.mode = mode;
	}

	public int mode() {
		return mode;
	}

	public static AnalysisVariant valueOf(int type) {
		for (AnalysisVariant vMode : values()) {
			if (vMode.mode == type)
				return vMode;
		}

		throw new IllegalArgumentException(
				"No enum const Type with type " + type);

	}

	public static AnalysisVariant OfName(String name) {
		for (AnalysisVariant vMode : AnalysisVariant.class.getEnumConstants()) {
			if (vMode.name().equals(name))
				return vMode;
		}

		throw new IllegalArgumentException(
				"No enum const Type with name " + name);
	}
}
