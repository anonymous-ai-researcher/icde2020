package checkreducedform;

import java.util.List;

import checkfrequency.FChecker;
import concepts.AtomicConcept;
import connectives.Negation;
import connectives.Or;
import formula.Formula;

public class RFChecker {

	public RFChecker() {

	}


	public boolean isAReducedFormPositive(AtomicConcept concept, List<Formula> formula_list) {

		FChecker fc = new FChecker();

		for (Formula formula : formula_list) {
			if (fc.positive(concept, formula) == 0) {

			} else if (formula.equals(concept) || (formula instanceof Or
					&& fc.positive(concept, formula) == 1
					&& fc.negative(concept, formula) == 0
					&& formula.getSubFormulas().contains(concept))) {

			} else {
				return false;
			}
		}

		return true;
	}


	public boolean isAReducedFormNegative(AtomicConcept concept, List<Formula> formula_list) {

		FChecker fc = new FChecker();

		for (Formula formula : formula_list) {
			if (fc.negative(concept, formula) == 0) {

			} else if (formula.equals(new Negation(concept)) || (formula instanceof Or
				 && fc.negative(concept, formula) == 1 
				 && fc.positive(concept, formula) == 0
				 && formula.getSubFormulas().contains(new Negation(concept)))) {

			} else {
				return false;
			}
		}

		return true;
	}

}
