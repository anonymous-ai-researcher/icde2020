package concepts;

import org.apache.commons.lang3.builder.HashCodeBuilder;

/**
 * @author Yizheng
 */
public class AtomicConcept extends ConceptExpression implements Comparable<AtomicConcept> {
		
	private static int definer_index = 1;
		
	public AtomicConcept() {
		super();
	}

	public AtomicConcept(String str) {
		super(str);
	}

	@Override
	public String toString() {
		return this.getText();
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(17, 37).append(this.getText()).toHashCode();
	}

	@Override
	public int compareTo(AtomicConcept concept) {
		int i = this.getText().compareTo(concept.getText());
		return i;
	}

	public static int getDefiner_index() {
		return definer_index;
	}

	public static void setDefiner_index(int definer_index) {
		AtomicConcept.definer_index = definer_index;
	}

}
