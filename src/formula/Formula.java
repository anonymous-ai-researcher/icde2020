/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package formula;

import concepts.AtomicConcept;
import concepts.BottomConcept;
import concepts.TopConcept;
import connectives.And;
import connectives.Equivalence;
import connectives.Exists;
import connectives.Forall;
import connectives.Inclusion;
import connectives.Negation;
import connectives.Or;
import individual.Individual;
import roles.AtomicRole;
import roles.BottomRole;
import roles.TopRole;
import simplification.Simplifier;

import java.util.ArrayList;
import java.util.List;

import org.apache.commons.lang3.builder.HashCodeBuilder;

/**
 *
 * @author Yizheng
 */
public class Formula {

	private List<Formula> subformulas;
	private String text;

	public Formula() {

	}

	public Formula(String str) {
		this.setText(str);
	}
	
	public Formula(int arity) {
		this.subformulas = new ArrayList<>(arity);
	}

	public String getText() {
		return this.text;
	}

	public void setText(String text) {
		this.text = text;
	}

	public List<Formula> getSubFormulas() {
		return this.subformulas;
	}

	public void setSubFormulas(Formula formula) {
		this.subformulas.add(formula);
	}

	public void setSubFormulas(Formula formula1, Formula formula2) {
		this.subformulas.add(formula1);
		this.subformulas.add(formula2);
	}

	public void setSubFormulas(List<Formula> list) {
		this.subformulas.addAll(list);
	}

	@Override
	public boolean equals(Object object) {

		if (this == object) {
			return true;
		} else if (object == null || this.getClass() != object.getClass()) {
			return false;
		} else if ((this instanceof AtomicConcept && object instanceof AtomicConcept)
				|| (this instanceof AtomicRole && object instanceof AtomicRole)
				|| (this instanceof Individual && object instanceof Individual)) {
			return this.toString().equals(object.toString());

		} else if (this instanceof Negation && object instanceof Negation) {
			Negation neg = (Negation) object;
			return this.getSubFormulas().get(0).equals(neg.getSubFormulas().get(0));
		} else if (this instanceof Exists && object instanceof Exists) {
			Exists exi = (Exists) object;
			return this.getSubFormulas().get(0).equals(exi.getSubFormulas().get(0))
					&& this.getSubFormulas().get(1).equals(exi.getSubFormulas().get(1));
		} else if (this instanceof Forall && object instanceof Forall) {
			Forall all = (Forall) object;
			return this.getSubFormulas().get(0).equals(all.getSubFormulas().get(0))
					&& this.getSubFormulas().get(1).equals(all.getSubFormulas().get(1));
		} else if (this instanceof Inclusion && object instanceof Inclusion) {
			Inclusion inc = (Inclusion) object;
			return this.getSubFormulas().get(0).equals(inc.getSubFormulas().get(0))
					&& this.getSubFormulas().get(1).equals(inc.getSubFormulas().get(1));
		} else if (this instanceof Equivalence && object instanceof Equivalence) {
			Equivalence equiv = (Equivalence) object;
			return this.getSubFormulas().get(0).equals(equiv.getSubFormulas().get(0))
					&& this.getSubFormulas().get(1).equals(equiv.getSubFormulas().get(1));
		} else if (this instanceof And && object instanceof And) {
			And and = (And) object;
			return this.getSubFormulas().containsAll(and.getSubFormulas())
					&& and.getSubFormulas().containsAll(this.getSubFormulas())
					&& this.getSubFormulas().size() == and.getSubFormulas().size();
		} else if (this instanceof Or && object instanceof Or) {
			Or or = (Or) object;
			return this.getSubFormulas().containsAll(or.getSubFormulas())
					&& or.getSubFormulas().containsAll(this.getSubFormulas())
					&& this.getSubFormulas().size() == or.getSubFormulas().size();
		} else {
			return false;
		}

	}
	
	/*
	 * && this.getSubFormulas().size() == and.getSubFormulas().size()
	 */

	/*public boolean negationComplement(Formula formula) {

		PreProcessor pp = new PreProcessor();

		Formula formula1 = pp.getNNF(this);
		Formula formula2 = pp.getNNF(formula);

		return (formula1 instanceof Negation && formula1.getSubFormulas().get(0).equals(formula2))
				|| (formula2 instanceof Negation && formula2.getSubFormulas().get(0).equals(formula1));
	}*/
	
	
	public boolean negationComplement(Formula formula) {

		Simplifier pp = new Simplifier();

		Formula formula1 = pp.removeDoubleNegations(this);
		Formula formula2 = pp.removeDoubleNegations(formula);

		return (formula1 instanceof Negation && formula1.getSubFormulas().get(0).equals(formula2))
				|| (formula2 instanceof Negation && formula2.getSubFormulas().get(0).equals(formula1));
	}

	@Override
	public Formula clone() throws CloneNotSupportedException {

		if (this == TopConcept.getInstance()) {
			return TopConcept.getInstance();

		} else if (this == BottomConcept.getInstance()) {
			return BottomConcept.getInstance();

		} else if (this == TopRole.getInstance()) {
			return TopRole.getInstance();

		} else if (this == BottomRole.getInstance()) {
			return BottomRole.getInstance();

		} else if (this instanceof AtomicConcept) {
			return new AtomicConcept(this.getText());

		} else if (this instanceof AtomicRole) {
			return new AtomicRole(this.getText());

		} else if (this instanceof Individual) {
			return new Individual(this.getText());

		} else if (this instanceof Negation) {
			return new Negation(this.getSubFormulas().get(0).clone());

		} else if (this instanceof Exists) {
			return new Exists(this.getSubFormulas().get(0).clone(),
					this.getSubFormulas().get(1).clone());

		} else if (this instanceof Forall) {
			return new Forall(this.getSubFormulas().get(0).clone(),
					this.getSubFormulas().get(1).clone());

		} else if (this instanceof Inclusion) {
			return new Inclusion(this.getSubFormulas().get(0).clone(),
					this.getSubFormulas().get(1).clone());

		} else if (this instanceof Equivalence) {
			return new Equivalence(this.getSubFormulas().get(0).clone(),
					this.getSubFormulas().get(1).clone());

		} else if (this instanceof And) {
			List<Formula> conjunct_list = this.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(conjunct.clone());
			}
			return new And(new_conjunct_list);
			
		} else if (this instanceof Or) {
			List<Formula> disjunct_list = this.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(disjunct.clone());
			}
			return new Or(new_disjunct_list);
		}

		return this;
	}

	@Override
	public int hashCode() {
		return new HashCodeBuilder(17, 37).append(this.getSubFormulas()).toHashCode();
	}

}
