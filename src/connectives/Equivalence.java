/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package connectives;

import formula.Formula;

/**
 *
 * @author Yizheng
 */
public class Equivalence extends Formula {
	
	public Equivalence() {
		super();
	}

	public Equivalence(Formula lefthand, Formula righthand) {
		super(2);
		this.setSubFormulas(lefthand, righthand);
	}

	@Override
	public String toString() {
		Formula lefthand = this.getSubFormulas().get(0);
		Formula righthand = this.getSubFormulas().get(1);

		if ((lefthand instanceof And || lefthand instanceof Or)
				&& (righthand instanceof And || righthand instanceof Or)) {
			return "(" + lefthand + ") \u2261 (" + righthand + ")";
		} else if ((lefthand instanceof And || lefthand instanceof Or) && !(righthand instanceof And)
				&& !(righthand instanceof Or)) {
			return "(" + lefthand + ") \u2261 " + righthand;
		} else if (!(lefthand instanceof And) && !(lefthand instanceof Or)
				&& (righthand instanceof And || righthand instanceof Or)) {
			return lefthand + " \u2261 (" + righthand + ")";
		} else {
			return lefthand + " \u2261 " + righthand;
		}
	}

}
