package inference;

import java.util.ArrayList;
import java.util.List;
import checkexistence.EChecker;
import checkfrequency.FChecker;
import concepts.AtomicConcept;
import concepts.BottomConcept;
import concepts.TopConcept;
import roles.AtomicRole;
import roles.BottomRole;
import roles.TopRole;
import simplification.Simplifier;
import connectives.And;
import connectives.Exists;
import connectives.Forall;
import connectives.Negation;
import connectives.Or;
import formula.Formula;
import individual.Individual;

public class Inferencer {
	
	public Inferencer() {

	}

	public List<List<Formula>> getCombinations(List<Formula> input_list) {

		List<List<Formula>> output_list = new ArrayList<>();

		int nCnt = input_list.size();

		int nBit = (0xFFFFFFFF >>> (32 - nCnt));

		for (int i = 1; i <= nBit; i++) {
			output_list.add(new ArrayList<>());
			for (int j = 0; j < nCnt; j++) {
				if ((i << (31 - j)) >> 31 == -1) {
					output_list.get(i - 1).add(input_list.get(j));
				}
			}
		}

		return output_list;
	}
	
	
	public List<Formula> combination_A(AtomicConcept concept, List<Formula> formula_list)
			throws CloneNotSupportedException {
		
		//System.out.println("combine formula_list = " + formula_list);
		List<Formula> output_list = new ArrayList<>();
				
		// C or A
		List<Formula> positive_star_premises = new ArrayList<>();
		// C or exists r.A
		List<Formula> positive_exists_premises = new ArrayList<>();
		// C or exists r.(A or B)
		List<Formula> positive_exists_disjunction_premises = new ArrayList<>();
		// C or forall r.A
		List<Formula> positive_forall_premises = new ArrayList<>();
		// C or forall r.(A or B)
		List<Formula> positive_forall_disjunction_premises = new ArrayList<>();
		// C or ~A
		List<Formula> negative_star_premises = new ArrayList<>();
		// C or exists r.~A
		List<Formula> negative_exists_premises = new ArrayList<>();
		// C or exists r.(~A or B)
		List<Formula> negative_exists_disjunction_premises = new ArrayList<>();
		// C or forall r.~A
		List<Formula> negative_forall_premises = new ArrayList<>();
		// C or forall r.(~A or B)
		List<Formula> negative_forall_disjunction_premises = new ArrayList<>();

		EChecker ec = new EChecker();

		for (Formula formula : formula_list) {
			//If concept is not present in formula, then formula is directly put into the output_list. 
			if (!ec.isPresent(concept, formula)) {
				output_list.add(formula);
            //if formula has the form C or A, where C is the bottom concept (false)
			} else if (formula.equals(concept)) {
				positive_star_premises.add(formula);
			//if formula has the form C or ~A, where C is the bottom concept (false)
			} else if (formula.equals(new Negation(concept))) {
				negative_star_premises.add(formula);
			//if formula has the form C or exists r.A, where C is the bottom concept (false)
			} else if (formula instanceof Exists && formula.getSubFormulas().get(1).equals(concept)) {
				positive_exists_premises.add(formula);

			} else if (formula instanceof Exists && formula.getSubFormulas().get(1) instanceof Or
					&& formula.getSubFormulas().get(1).getSubFormulas().contains(concept)) {
				positive_exists_disjunction_premises.add(formula);
				
			} else if (formula instanceof Exists && formula.getSubFormulas().get(1).equals(new Negation(concept))) {
				negative_exists_premises.add(formula);

			} else if (formula instanceof Exists && formula.getSubFormulas().get(1) instanceof Or 
					&& formula.getSubFormulas().get(1).getSubFormulas().contains(new Negation(concept))) {
				negative_exists_disjunction_premises.add(formula);
				
			} else if (formula instanceof Forall && formula.getSubFormulas().get(1).equals(concept)) {
				positive_forall_premises.add(formula);

			} else if (formula instanceof Forall && formula.getSubFormulas().get(1) instanceof Or
					&& formula.getSubFormulas().get(1).getSubFormulas().contains(concept)) {
				positive_forall_disjunction_premises.add(formula);
				
			} else if (formula instanceof Forall && formula.getSubFormulas().get(1).equals(new Negation(concept))) {
				negative_forall_premises.add(formula);

			} else if (formula instanceof Forall && formula.getSubFormulas().get(1) instanceof Or
					&& formula.getSubFormulas().get(1).getSubFormulas().contains(new Negation(concept))) {
				negative_forall_disjunction_premises.add(formula);
				
			} else if (formula instanceof Or) {
				
				List<Formula> disjunct_list = formula.getSubFormulas();

				if (disjunct_list.contains(concept)) {
					positive_star_premises.add(formula);

				} else if (disjunct_list.contains(new Negation(concept))) {
					negative_star_premises.add(formula);
			
				} else {
					for (Formula disjunct : disjunct_list) {
						if (disjunct instanceof Exists && disjunct.getSubFormulas().get(1).equals(concept)) {
							positive_exists_premises.add(formula);
							break;
						} else if (disjunct instanceof Exists && disjunct.getSubFormulas().get(1) instanceof Or
								&& disjunct.getSubFormulas().get(1).getSubFormulas().contains(concept)) {
							positive_exists_disjunction_premises.add(formula);
							break;
						} else if (disjunct instanceof Exists
								&& disjunct.getSubFormulas().get(1).equals(new Negation(concept))) {
							negative_exists_premises.add(formula);
							break;
						} else if (disjunct instanceof Exists && disjunct.getSubFormulas().get(1) instanceof Or
								&& disjunct.getSubFormulas().get(1).getSubFormulas().contains(new Negation(concept))) {
							negative_exists_disjunction_premises.add(formula);
							break;
						} else if (disjunct instanceof Forall && disjunct.getSubFormulas().get(1).equals(concept)) {
							positive_forall_premises.add(formula);
							break;
						} else if (disjunct instanceof Forall && disjunct.getSubFormulas().get(1) instanceof Or
								&& disjunct.getSubFormulas().get(1).getSubFormulas().contains(concept)) {
							positive_forall_disjunction_premises.add(formula);
							break;
						} else if (disjunct instanceof Forall
								&& disjunct.getSubFormulas().get(1).equals(new Negation(concept))) {
							negative_forall_premises.add(formula);
							break;
						} else if (disjunct instanceof Forall && disjunct.getSubFormulas().get(1) instanceof Or
								&& disjunct.getSubFormulas().get(1).getSubFormulas().contains(new Negation(concept))) {
							negative_forall_disjunction_premises.add(formula);
							break;
						} 
					}
				}

			} else {
				output_list.add(formula);
			}
		}
		//System.out.println("=====================================================");
		/*System.out.println("positive_star_premises = " + positive_star_premises);
		System.out.println("positive_exists_premises = " + positive_exists_premises);
		System.out.println("positive_exists_disjunction_premises = " + positive_exists_disjunction_premises);
		System.out.println("positive_forall_premises = " + positive_forall_premises.size());
		System.out.println("positive_forall_disjunction_premises = " + positive_forall_disjunction_premises);
		System.out.println("negative_star_premises = " + negative_star_premises);
		System.out.println("negative_exists_premises = " + negative_exists_premises);
		System.out.println("negative_exists_disjunction_premises = " + negative_exists_disjunction_premises);
		System.out.println("negative_forall_premises = " + negative_forall_premises.size());
		System.out.println("negative_forall_disjunction_premises = " + negative_forall_disjunction_premises);*/
		//
		//[6]
		if (!negative_star_premises.isEmpty()) {
			
			if (negative_star_premises.contains(new Negation(concept))) {
				
				if (!positive_star_premises.isEmpty()) {
					for (Formula ps_premise : positive_star_premises) {
						output_list.add(AckermannReplace(concept, ps_premise, BottomConcept.getInstance()));
					}
				}
				if (!positive_exists_premises.isEmpty()) {
					for (Formula pe_premise : positive_exists_premises) {
						output_list.add(AckermannReplace(concept, pe_premise, BottomConcept.getInstance()));
					}
				}
				if (!positive_exists_disjunction_premises.isEmpty()) {
					for (Formula ped_premise : positive_exists_disjunction_premises) {
						output_list.add(AckermannReplace(concept, ped_premise, BottomConcept.getInstance()));
					}
				}
				if (!positive_forall_premises.isEmpty()) {
					for (Formula pf_premise : positive_forall_premises) {
						output_list.add(AckermannReplace(concept, pf_premise, BottomConcept.getInstance()));
					}
				}
				if (!positive_forall_disjunction_premises.isEmpty()) {
					for (Formula pfd_premise : positive_forall_disjunction_premises) {
						output_list.add(AckermannReplace(concept, pfd_premise, BottomConcept.getInstance()));
					}
				}
				
			} else {
				
				List<Formula> and_list = new ArrayList<>();
				
				for (Formula ns_premise : negative_star_premises) {
					
					Formula ns_def = null;
					
					List<Formula> def_disjunct_list = new ArrayList<>(ns_premise.getSubFormulas());
					//remove ~A from (D or ~A), leaving D alone
					def_disjunct_list.remove(new Negation(concept));
					//if D is not a disjunction
					if (def_disjunct_list.size() == 1) {
						ns_def = def_disjunct_list.get(0);
				    //if D is a disjunction
					} else {
						ns_def = new Or(def_disjunct_list);
					}

					and_list.add(ns_def);
					
					if (!positive_star_premises.isEmpty()) {
						for (Formula ps_premise : positive_star_premises) {
							output_list.add(AckermannReplace(concept, ps_premise, ns_def));
						}
					}
					if (!positive_forall_premises.isEmpty()) {
						for (Formula pf_premise : positive_forall_premises) {
							output_list.add(AckermannReplace(concept, pf_premise, ns_def));
						}
					}
					if (!positive_forall_disjunction_premises.isEmpty()) {
						for (Formula pfd_premise : positive_forall_disjunction_premises) {
							output_list.add(AckermannReplace(concept, pfd_premise, ns_def));
						}
					}
				}
				
				Formula ns_def_and = null;
				
				if (and_list.size() == 1) {
				    ns_def_and = and_list.get(0);
				} else {
					ns_def_and = new And(and_list);
				}
				
				if (!positive_exists_premises.isEmpty()) {
									
					for (Formula pe_premise : positive_exists_premises) {
						output_list.add(AckermannReplace(concept, pe_premise, ns_def_and));
					}
				}	
				if (!positive_exists_disjunction_premises.isEmpty()) {
					
					for (Formula ped_premise : positive_exists_disjunction_premises) {
						output_list.add(AckermannReplace(concept, ped_premise, ns_def_and));
					}
				}	
			}
		}

		//[1]
		if (!positive_star_premises.isEmpty()) {
						
			if (positive_star_premises.contains(concept)) {
								
				if (!negative_exists_premises.isEmpty()) {
					for (Formula ne_premise : negative_exists_premises) {
						output_list.add(AckermannReplace(concept, ne_premise, TopConcept.getInstance()));
					}
				}
				if (!negative_exists_disjunction_premises.isEmpty()) {
					for (Formula ned_premise : negative_exists_disjunction_premises) {
						output_list.add(AckermannReplace(concept, ned_premise, TopConcept.getInstance()));
					}
				}
				if (!negative_forall_premises.isEmpty()) {
					for (Formula nf_premise : negative_forall_premises) {
						output_list.add(AckermannReplace(concept, nf_premise, TopConcept.getInstance()));
					}
				}
				if (!negative_forall_disjunction_premises.isEmpty()) {
					for (Formula nfd_premise : negative_forall_disjunction_premises) {
						output_list.add(AckermannReplace(concept, nfd_premise, TopConcept.getInstance()));
					}
				}
				
			} else {
				
				List<Formula> or_list = new ArrayList<>();
				
				for (Formula ps_premise : positive_star_premises) {
					
					Formula ps_def = null;
					
					List<Formula> def_disjunct_list = new ArrayList<>(ps_premise.getSubFormulas());
					//remove A from C or A, leaving C alone
					def_disjunct_list.remove(concept);
					
					if (def_disjunct_list.size() == 1) {
						if (def_disjunct_list.get(0) instanceof Negation) {
							ps_def = def_disjunct_list.get(0).getSubFormulas().get(0);
						} else {
						    ps_def = new Negation(def_disjunct_list.get(0));
						}
					} else {
						ps_def = new Negation(new Or(def_disjunct_list));
					}
					
					or_list.add(ps_def);
				}
				
				Formula ps_def_or = null;
				
				if (or_list.size() == 1) {
				    ps_def_or = or_list.get(0);
				} else {
					ps_def_or = new Or(or_list);
				}	
				
				if (!negative_exists_premises.isEmpty()) {			
					for (Formula ne_premise : negative_exists_premises) {
						output_list.add(AckermannReplace(concept, ne_premise, ps_def_or));
					}
				}
				if (!negative_exists_disjunction_premises.isEmpty()) {			
					for (Formula ned_premise : negative_exists_disjunction_premises) {
						output_list.add(AckermannReplace(concept, ned_premise, ps_def_or));
					}
				}
				if (!negative_forall_premises.isEmpty()) {
					for (Formula nf_premise : negative_forall_premises) {
						output_list.add(AckermannReplace(concept, nf_premise, ps_def_or));
					}
				}
				if (!negative_forall_disjunction_premises.isEmpty()) {
					for (Formula nfd_premise : negative_forall_disjunction_premises) {
						output_list.add(AckermannReplace(concept, nfd_premise, ps_def_or));
					}
				}				
			}
		}

		//&& (!positive_exists_premises.isEmpty() || !positive_forall_premises.isEmpty())
		//[7]
		if (!negative_exists_premises.isEmpty()) {
			//[7,2]
			if (!positive_exists_premises.isEmpty()) {
				if (negative_star_premises.isEmpty()) {
					for (Formula pe_premise : positive_exists_premises) {
						output_list.add(PurifyPositive(concept, pe_premise));
					}
				}
				if (positive_star_premises.isEmpty()) {
					for (Formula ne_premise : negative_exists_premises) {
						output_list.add(PurifyNegative(concept, ne_premise));
					}
				}
			}
			//[7,3]
			if (!positive_exists_disjunction_premises.isEmpty()) {
				if (negative_star_premises.isEmpty()) {
					for (Formula ped_premise : positive_exists_disjunction_premises) {
						output_list.add(PurifyPositive(concept, ped_premise));
					}
				}
				if (positive_star_premises.isEmpty() && positive_exists_premises.isEmpty()) {
					for (Formula ne_premise : negative_exists_premises) {
						output_list.add(PurifyNegative(concept, ne_premise));
					}
				}
			}
			//[7,4]
			if (!positive_forall_premises.isEmpty()) {			
				if (positive_star_premises.isEmpty() && positive_exists_premises.isEmpty() &&
						positive_exists_disjunction_premises.isEmpty()) {
					for (Formula ne_premise : negative_exists_premises) {
						output_list.add(PurifyNegative(concept, ne_premise));
					}
				}

				for (Formula pf_premise : positive_forall_premises) {
					List<Formula> pf_disjunct_list = null;
					Formula pf_role = null;
					if (pf_premise instanceof Forall) {
						pf_disjunct_list = new ArrayList<>();
						//C or forall r.A, pf_role = r
						pf_role = pf_premise.getSubFormulas().get(0);
					} else {
						pf_disjunct_list = new ArrayList<>(pf_premise.getSubFormulas());
						for (Formula pf_disjunct : pf_disjunct_list) {
							//to find the concept of forall r.A
							if (ec.isPresent(concept, pf_disjunct)) {
								pf_role = pf_disjunct.getSubFormulas().get(0);
								pf_disjunct_list.remove(pf_disjunct);
								break;
							}
						}
					}

					for (Formula ne_premise : negative_exists_premises) {
						List<Formula> E_list = null;
						
						if (ne_premise instanceof Exists) {
							//exists r.~A, ne_role = r
							Formula ne_role = ne_premise.getSubFormulas().get(0);
							if (ne_role.equals(pf_role)) {
								E_list = new ArrayList<>();
								E_list.addAll(pf_disjunct_list);
								if (E_list.isEmpty()) {

								} else if (E_list.size() == 1) {
									output_list.add(E_list.get(0));
								} else {
									output_list.add(new Or(E_list));
								}
							}
							//C or exists r.~A 
						} else {
							List<Formula> ne_disjunct_list = new ArrayList<>(ne_premise.getSubFormulas());
							for (Formula ne_disjunct : ne_disjunct_list) {
								//to find the concept of exists r.~A
								if (ec.isPresent(concept, ne_disjunct)) {
									// exists r.~A, ne_role = r
									Formula ne_role = ne_disjunct.getSubFormulas().get(0);
									if (ne_role.equals(pf_role)) {
										E_list = new ArrayList<>();
										E_list.addAll(pf_disjunct_list);
										ne_disjunct_list.remove(ne_disjunct);
										E_list.addAll(ne_disjunct_list);
										if (E_list.size() == 1) {
											output_list.add(E_list.get(0));
											break;
										} else {
											output_list.add(new Or(E_list));
											break;
										}
									}
								}
							}
						}
					}
				}
			}
			//[7,5]
			if (!positive_forall_disjunction_premises.isEmpty()) {
				if (positive_star_premises.isEmpty() && positive_exists_premises.isEmpty() &&
						positive_exists_disjunction_premises.isEmpty() && positive_forall_premises.isEmpty()) {
					for (Formula ne_premise : negative_exists_premises) {
						output_list.add(PurifyNegative(concept, ne_premise));
					}
				}
				
				for (Formula pfd_premise : positive_forall_disjunction_premises) {
					List<Formula> pfd_disjunct_list = null;
					List<Formula> pdf_filler_list = null;
					Formula pfd_role = null;
					Formula pfd_new_filler = null;
					if (pfd_premise instanceof Forall) {
						pfd_disjunct_list = new ArrayList<>();
						pdf_filler_list = new ArrayList<>(pfd_premise.getSubFormulas().get(1).getSubFormulas());
						pdf_filler_list.remove(concept);
						//C or forall r.(A or D), pf_role = r
						pfd_role = pfd_premise.getSubFormulas().get(0);
					} else {
						pfd_disjunct_list = new ArrayList<>(pfd_premise.getSubFormulas());
						for (Formula pfd_disjunct : pfd_disjunct_list) {
							//to find the concept of forall r.(A or D)
							if (ec.isPresent(concept, pfd_disjunct)) {
								pdf_filler_list = new ArrayList<>(pfd_disjunct.getSubFormulas().get(1).getSubFormulas());
								pdf_filler_list.remove(concept);
								pfd_role = pfd_disjunct.getSubFormulas().get(0);
								pfd_disjunct_list.remove(pfd_disjunct);
								break;
							}
						}
					}
					
					if (pdf_filler_list.isEmpty()) {
						pfd_new_filler = BottomConcept.getInstance();
						
					} else if (pdf_filler_list.size() == 1) {
						pfd_new_filler = new Exists(pfd_role, pdf_filler_list.get(0));
						
					} else {
						pfd_new_filler = new Exists(pfd_role, new Or(pdf_filler_list));
					}

					for (Formula ne_premise : negative_exists_premises) {
						List<Formula> E_list = null;
						
						if (ne_premise instanceof Exists) {
							//exists r.~A, ne_role = r
							Formula ne_role = ne_premise.getSubFormulas().get(0);
							if (ne_role.equals(pfd_role)) {
								E_list = new ArrayList<>();
								E_list.addAll(pfd_disjunct_list);
								E_list.add(pfd_new_filler);
								if (E_list.isEmpty()) {

								} else if (E_list.size() == 1) {
									output_list.add(E_list.get(0));
								} else {
									output_list.add(new Or(E_list));
								}
							}
							//C or exists r.~A 
						} else {
							List<Formula> ne_disjunct_list = new ArrayList<>(ne_premise.getSubFormulas());
							for (Formula ne_disjunct : ne_disjunct_list) {
								//to find the concept of exists r.~A
								if (ec.isPresent(concept, ne_disjunct)) {
									// exists r.~A, ne_role = r
									Formula ne_role = ne_disjunct.getSubFormulas().get(0);
									if (ne_role.equals(pfd_role)) {
										E_list = new ArrayList<>();
										E_list.addAll(pfd_disjunct_list);
										ne_disjunct_list.remove(ne_disjunct);
										E_list.addAll(ne_disjunct_list);
										E_list.add(pfd_new_filler);
										if (E_list.size() == 1) {
											output_list.add(E_list.get(0));
											break;
										} else {
											output_list.add(new Or(E_list));
											break;
										}
									}
								}
							}
						}
					}
				}			
			}	
		}
		
		//[8]
		if (!negative_exists_disjunction_premises.isEmpty()) {
			//[8,2]
			if (!positive_exists_premises.isEmpty()) {
				if (negative_star_premises.isEmpty() && negative_exists_premises.isEmpty()) {
					for (Formula pe_premise : positive_exists_premises) {
						output_list.add(PurifyPositive(concept, pe_premise));
					}
				}
				if (positive_star_premises.isEmpty()) {
					for (Formula ned_premise : negative_exists_disjunction_premises) {
						output_list.add(PurifyNegative(concept, ned_premise));
					}
				}
			}
			//[8,3]
			if (!positive_exists_disjunction_premises.isEmpty()) {
				if (negative_star_premises.isEmpty() && negative_exists_premises.isEmpty()) {
					for (Formula ped_premise : positive_exists_disjunction_premises) {
						output_list.add(PurifyPositive(concept, ped_premise));
					}
				}
				if (positive_star_premises.isEmpty() && positive_exists_premises.isEmpty()) {
					for (Formula ned_premise : negative_exists_disjunction_premises) {
						output_list.add(PurifyNegative(concept, ned_premise));
					}
				}
			}
			//[8,4]
			if (!positive_forall_premises.isEmpty()) {
				
				if (positive_star_premises.isEmpty() && positive_exists_premises.isEmpty() &&
						positive_exists_disjunction_premises.isEmpty()) {
					for (Formula ned_premise : negative_exists_disjunction_premises) {
						output_list.add(PurifyNegative(concept, ned_premise));
					}
				}

				for (Formula pf_premise : positive_forall_premises) {
					List<Formula> pf_disjunct_list = null;
					Formula pf_role = null;
					if (pf_premise instanceof Forall) {
						pf_disjunct_list = new ArrayList<>();
						//C or forall r.A, pf_role = r
						pf_role = pf_premise.getSubFormulas().get(0);
					} else {
						pf_disjunct_list = new ArrayList<>(pf_premise.getSubFormulas());
						for (Formula pf_disjunct : pf_disjunct_list) {
							//to find the concept of forall r.A
							if (ec.isPresent(concept, pf_disjunct)) {
								pf_role = pf_disjunct.getSubFormulas().get(0);
								pf_disjunct_list.remove(pf_disjunct);
								break;
							}
						}
					}

					for (Formula ned_premise : negative_exists_disjunction_premises) {
						List<Formula> E_list = null;
						List<Formula> ned_filler_list = null;
						Formula ned_new_filler = null;
						
						if (ned_premise instanceof Exists) {
							//exists r.(~A or F), ne_role = r
							Formula ned_role = ned_premise.getSubFormulas().get(0);
							if (ned_role.equals(pf_role)) {
								ned_filler_list = new ArrayList<>(ned_premise.getSubFormulas().get(1).getSubFormulas());
								ned_filler_list.remove(new Negation(concept));
								if (ned_filler_list.isEmpty()) {
									
								} else if (ned_filler_list.size() == 1) {
									ned_new_filler = new Exists(ned_role, ned_filler_list.get(0));
									
								} else {
									ned_new_filler = new Exists(ned_role, new Or(ned_filler_list));
								}
								E_list = new ArrayList<>();
								E_list.addAll(pf_disjunct_list);
								if (ned_new_filler != null) {
									E_list.add(ned_new_filler);
								}
								if (E_list.isEmpty()) {

								} else if (E_list.size() == 1) {
									output_list.add(E_list.get(0));
								} else {
									output_list.add(new Or(E_list));
								}
							}
							//C or exists r.~A 
						} else {
							List<Formula> ned_disjunct_list = new ArrayList<>(ned_premise.getSubFormulas());
							for (Formula ned_disjunct : ned_disjunct_list) {
								//to find the concept of exists r.~A
								if (ec.isPresent(concept, ned_disjunct)) {
									// exists r.~A, ne_role = r
									Formula ned_role = ned_disjunct.getSubFormulas().get(0);
									if (ned_role.equals(pf_role)) {
										ned_filler_list = new ArrayList<>(ned_disjunct.getSubFormulas().get(1).getSubFormulas());
										ned_filler_list.remove(new Negation(concept));
										if (ned_filler_list.isEmpty()) {
											
										} else if (ned_filler_list.size() == 1) {
											ned_new_filler = new Exists(ned_role, ned_filler_list.get(0));
											
										} else {
											ned_new_filler = new Exists(ned_role, new Or(ned_filler_list));
										}
										E_list = new ArrayList<>();
										E_list.addAll(pf_disjunct_list);
										ned_disjunct_list.remove(ned_disjunct);
										E_list.addAll(ned_disjunct_list);
										if (ned_new_filler != null) {
											E_list.add(ned_new_filler);
										}
										if (E_list.size() == 1) {
											output_list.add(E_list.get(0));
											break;
										} else {
											output_list.add(new Or(E_list));
											break;
										}
									}
								}
							}
						}
					}
				}
			}
			//[8,5]
			if (!positive_forall_disjunction_premises.isEmpty()) {
				if (positive_star_premises.isEmpty() && positive_exists_premises.isEmpty() &&
						positive_exists_disjunction_premises.isEmpty() && positive_forall_premises.isEmpty()) {
					for (Formula ned_premise : negative_exists_disjunction_premises) {
						output_list.add(PurifyNegative(concept, ned_premise));
					}
				}
				
				for (Formula pfd_premise : positive_forall_disjunction_premises) {
					List<Formula> pfd_disjunct_list = null;
					List<Formula> pfd_filler_list = null;
					Formula pfd_role = null;
					Formula ned_new_filler = null;
					if (pfd_premise instanceof Forall) {
						pfd_disjunct_list = new ArrayList<>();
						pfd_filler_list = new ArrayList<>(pfd_premise.getSubFormulas().get(1).getSubFormulas());
						pfd_filler_list.remove(concept);
						//C or forall r.(A or D), pf_role = r
						pfd_role = pfd_premise.getSubFormulas().get(0);
					} else {
						pfd_disjunct_list = new ArrayList<>(pfd_premise.getSubFormulas());
						for (Formula pfd_disjunct : pfd_disjunct_list) {
							//to find the concept of forall r.(A or D)
							if (ec.isPresent(concept, pfd_disjunct)) {
								pfd_filler_list = new ArrayList<>(pfd_disjunct.getSubFormulas().get(1).getSubFormulas());
								pfd_filler_list.remove(concept);
								pfd_role = pfd_disjunct.getSubFormulas().get(0);
								pfd_disjunct_list.remove(pfd_disjunct);
								break;
							}
						}
					}
					
					/*if (pdf_filler_list.isEmpty()) {
						pfd_new_filler = BottomConcept.getInstance();
						
					} else if (pdf_filler_list.size() == 1) {
						pfd_new_filler = new Exists(pfd_role, pdf_filler_list.get(0));
						
					} else {
						pfd_new_filler = new Exists(pfd_role, new Or(pdf_filler_list));
					}*/

					for (Formula ned_premise : negative_exists_disjunction_premises) {
						List<Formula> ned_filler_list = null;
						List<Formula> E_list = null;
						if (ned_premise instanceof Exists) {
							//exists r.~A, ne_role = r
							Formula ned_role = ned_premise.getSubFormulas().get(0);
							if (ned_role.equals(pfd_role)) {
								ned_filler_list = new ArrayList<>(ned_premise.getSubFormulas().get(1).getSubFormulas());
								ned_filler_list.remove(new Negation(concept));
								ned_filler_list.addAll(pfd_filler_list);
								if (ned_filler_list.isEmpty()) {
									
								} else if (ned_filler_list.size() == 1) {
									ned_new_filler = new Exists(ned_role, ned_filler_list.get(0));
									
								} else {
									ned_new_filler = new Exists(ned_role, new Or(ned_filler_list));
								}
								E_list = new ArrayList<>();
								E_list.addAll(pfd_disjunct_list);
								E_list.add(ned_new_filler);
								if (E_list.isEmpty()) {

								} else if (E_list.size() == 1) {
									output_list.add(E_list.get(0));
								} else {
									output_list.add(new Or(E_list));
								}
							}
							//C or exists r.~A 
						} else {
							List<Formula> ned_disjunct_list = new ArrayList<>(ned_premise.getSubFormulas());
							for (Formula ned_disjunct : ned_disjunct_list) {
								//to find the concept of exists r.~A
								if (ec.isPresent(concept, ned_disjunct)) {
									// exists r.~A, ne_role = r
									Formula ned_role = ned_disjunct.getSubFormulas().get(0);
									if (ned_role.equals(pfd_role)) {
										ned_filler_list = new ArrayList<>(ned_disjunct.getSubFormulas().get(1).getSubFormulas());
										ned_filler_list.remove(new Negation(concept));
										ned_filler_list.addAll(pfd_filler_list);
										if (ned_filler_list.isEmpty()) {
											
										} else if (ned_filler_list.size() == 1) {
											ned_new_filler = new Exists(ned_role, ned_filler_list.get(0));
											
										} else {
											ned_new_filler = new Exists(ned_role, new Or(ned_filler_list));
										}
										E_list = new ArrayList<>();
										E_list.addAll(pfd_disjunct_list);
										ned_disjunct_list.remove(ned_disjunct);
										E_list.addAll(ned_disjunct_list);
										E_list.add(ned_new_filler);
										if (E_list.size() == 1) {
											output_list.add(E_list.get(0));
											break;
										} else {
											output_list.add(new Or(E_list));
											break;
										}
									}
								}
							}
						}
					}
				}			
			}	
		}

		//[9]
		if (!negative_forall_premises.isEmpty()) {
			//[9,2]
			if (!positive_exists_premises.isEmpty()) {

				if (negative_star_premises.isEmpty() && negative_exists_premises.isEmpty()
						&& negative_exists_disjunction_premises.isEmpty()) {
					for (Formula pe_premise : positive_exists_premises) {
						output_list.add(PurifyPositive(concept, pe_premise));
					}
				}

				for (Formula pe_premise : positive_exists_premises) {

					List<Formula> pe_disjunct_list = null;
					Formula pe_role = null;
					if (pe_premise instanceof Exists) {
						pe_disjunct_list = new ArrayList<>();
						pe_role = pe_premise.getSubFormulas().get(0);

					} else {
						pe_disjunct_list = new ArrayList<>(pe_premise.getSubFormulas());
						for (Formula pe_disjunct : pe_disjunct_list) {
							if (ec.isPresent(concept, pe_disjunct)) {
								pe_role = pe_disjunct.getSubFormulas().get(0);
								pe_disjunct_list.remove(pe_disjunct);
								break;
							}
						}
					}

					for (Formula nf_premise : negative_forall_premises) {
						List<Formula> E_list = null;

						if (nf_premise instanceof Forall) {
							Formula nf_role = nf_premise.getSubFormulas().get(0);
							if (nf_role.equals(pe_role)) {
								E_list = new ArrayList<>();
								E_list.addAll(pe_disjunct_list);
								if (E_list.isEmpty()) {

								} else if (E_list.size() == 1) {
									output_list.add(E_list.get(0));
								} else {
									output_list.add(new Or(E_list));
								}
							}

						} else {
							List<Formula> nf_disjunct_list = new ArrayList<>(nf_premise.getSubFormulas());
							for (Formula nf_disjunct : nf_disjunct_list) {
								if (ec.isPresent(concept, nf_disjunct)) {
									Formula nf_role = nf_disjunct.getSubFormulas().get(0);
									if (nf_role.equals(pe_role)) {
										E_list = new ArrayList<>();
										E_list.addAll(pe_disjunct_list);
										nf_disjunct_list.remove(nf_disjunct);
										E_list.addAll(nf_disjunct_list);
										if (E_list.size() == 1) {
											output_list.add(E_list.get(0));
											break;
										} else {
											output_list.add(new Or(E_list));
											break;
										}
									}
								}
							}
						}
					}
				}
			}
			//[9,3]
			if (!positive_exists_disjunction_premises.isEmpty()) {
				
				if (negative_star_premises.isEmpty() && negative_exists_premises.isEmpty() &&
						negative_exists_disjunction_premises.isEmpty()) {
					for (Formula ped_premise : positive_exists_disjunction_premises) {
						output_list.add(PurifyPositive(concept, ped_premise));
					}
				}

				for (Formula nf_premise : negative_forall_premises) {
					List<Formula> nf_disjunct_list = null;
					Formula nf_role = null;
					if (nf_premise instanceof Forall) {
						nf_disjunct_list = new ArrayList<>();
						//C or forall r.~A, pf_role = r
						nf_role = nf_premise.getSubFormulas().get(0);
					} else {
						nf_disjunct_list = new ArrayList<>(nf_premise.getSubFormulas());
						for (Formula nf_disjunct : nf_disjunct_list) {
							//to find the concept of forall r.A
							if (ec.isPresent(concept, nf_disjunct)) {
								nf_role = nf_disjunct.getSubFormulas().get(0);
								nf_disjunct_list.remove(nf_disjunct);
								break;
							}
						}
					}

					for (Formula ped_premise : positive_exists_disjunction_premises) {
						List<Formula> E_list = null;
						List<Formula> ped_filler_list = null;
						Formula ped_new_filler = null;
						
						if (ped_premise instanceof Exists) {
							//exists r.(~A or F), ne_role = r
							Formula ped_role = ped_premise.getSubFormulas().get(0);
							if (ped_role.equals(nf_role)) {
								ped_filler_list = new ArrayList<>(ped_premise.getSubFormulas().get(1).getSubFormulas());
								ped_filler_list.remove(concept);
								if (ped_filler_list.isEmpty()) {
									
								} else if (ped_filler_list.size() == 1) {
									ped_new_filler = new Exists(ped_role, ped_filler_list.get(0));
									
								} else {
									ped_new_filler = new Exists(ped_role, new Or(ped_filler_list));
								}
								E_list = new ArrayList<>(nf_disjunct_list);
								if (ped_new_filler != null) {
									E_list.add(ped_new_filler);
								}
								if (E_list.isEmpty()) {

								} else if (E_list.size() == 1) {
									output_list.add(E_list.get(0));
								} else {
									output_list.add(new Or(E_list));
								}
							}
							//C or exists r.(~A or D) 
						} else {
							List<Formula> ped_disjunct_list = new ArrayList<>(ped_premise.getSubFormulas());
							for (Formula ped_disjunct : ped_disjunct_list) {
								//to find the concept of exists r.~A
								if (ec.isPresent(concept, ped_disjunct)) {
									// exists r.~A, ne_role = r
									Formula ped_role = ped_disjunct.getSubFormulas().get(0);
									if (ped_role.equals(nf_role)) {
										ped_filler_list = new ArrayList<>(ped_disjunct.getSubFormulas().get(1).getSubFormulas());
										ped_filler_list.remove(concept);
										if (ped_filler_list.isEmpty()) {
											
										} else if (ped_filler_list.size() == 1) {
											ped_new_filler = new Exists(ped_role, ped_filler_list.get(0));
											
										} else {
											ped_new_filler = new Exists(ped_role, new Or(ped_filler_list));
										}
										E_list = new ArrayList<>(nf_disjunct_list);
										ped_disjunct_list.remove(ped_disjunct);
										E_list.addAll(ped_disjunct_list);
										if (ped_new_filler != null) {
											E_list.add(ped_new_filler);
										}
										if (E_list.size() == 1) {
											output_list.add(E_list.get(0));
											break;
										} else {
											output_list.add(new Or(E_list));
											break;
										}
									}
								}
							}
						}
					}
				}
			}
			//[9,4]
			if (!positive_forall_premises.isEmpty()) {

				for (Formula pf_premise : positive_forall_premises) {
					
					List<Formula> pf_disjunct_list = null;
					Formula pf_role = null;
					if (pf_premise instanceof Forall) {
						pf_disjunct_list = new ArrayList<>();
						pf_role = pf_premise.getSubFormulas().get(0);
					} else {
						pf_disjunct_list = new ArrayList<>(pf_premise.getSubFormulas());
						for (Formula pf_disjunct : pf_disjunct_list) {
							if (ec.isPresent(concept, pf_disjunct)) {
								pf_role = pf_disjunct.getSubFormulas().get(0);
								pf_disjunct_list.remove(pf_disjunct);
								break;
							}
						}
					}

					for (Formula nf_premise : negative_forall_premises) {
						List<Formula> E_list = null;
						if (nf_premise instanceof Forall) {
							Formula nf_role = nf_premise.getSubFormulas().get(0);
							if (nf_role.equals(pf_role)) {
								E_list = new ArrayList<>();
								E_list.addAll(pf_disjunct_list);
								if (E_list.isEmpty()) {
									output_list.add(new Forall(nf_role, BottomConcept.getInstance()));
								} else {
									E_list.add(new Forall(nf_role, BottomConcept.getInstance()));
									output_list.add(new Or(E_list));
								}
							}

						} else {

							List<Formula> nf_disjunct_list = new ArrayList<>(nf_premise.getSubFormulas());
							for (Formula nf_disjunct : nf_disjunct_list) {
								if (ec.isPresent(concept, nf_disjunct)) {
									Formula nf_role = nf_disjunct.getSubFormulas().get(0);
									if (nf_role.equals(pf_role)) {
										E_list = new ArrayList<>();
										E_list.addAll(pf_disjunct_list);
										nf_disjunct_list.remove(nf_disjunct);
										E_list.addAll(nf_disjunct_list);
										E_list.add(new Forall(nf_role, BottomConcept.getInstance()));
										output_list.add(new Or(E_list));
										break;
									}
								}
							}
						}
					}
				}
			}
			//[9,5]
			if (!positive_forall_disjunction_premises.isEmpty()) {

				for (Formula pfd_premise : positive_forall_disjunction_premises) {
					
					List<Formula> pfd_disjunct_list = null;
					List<Formula> pfd_filler_list = null;
					Formula pfd_new_filler = null;
					Formula pfd_role = null;
					if (pfd_premise instanceof Forall) {
						pfd_disjunct_list = new ArrayList<>();
						pfd_role = pfd_premise.getSubFormulas().get(0);
						pfd_filler_list = new ArrayList<>(pfd_premise.getSubFormulas().get(1).getSubFormulas());
						pfd_filler_list.remove(concept);
					} else {
						pfd_disjunct_list = new ArrayList<>(pfd_premise.getSubFormulas());
						for (Formula pfd_disjunct : pfd_disjunct_list) {
							if (ec.isPresent(concept, pfd_disjunct)) {
								pfd_filler_list = new ArrayList<>(pfd_disjunct.getSubFormulas().get(1).getSubFormulas());
								pfd_filler_list.remove(concept);
								pfd_role = pfd_disjunct.getSubFormulas().get(0);
								pfd_disjunct_list.remove(pfd_disjunct);
								break;
							}
						}
					}
					if (pfd_filler_list.isEmpty()) {
						pfd_new_filler = BottomConcept.getInstance();
						
					} else if (pfd_filler_list.size() == 1) {
						pfd_new_filler = pfd_filler_list.get(0);
						
					} else {
						pfd_new_filler = new Or(pfd_filler_list);
					}

					for (Formula nf_premise : negative_forall_premises) {
						List<Formula> E_list = null;
						if (nf_premise instanceof Forall) {
							Formula nf_role = nf_premise.getSubFormulas().get(0);
							if (nf_role.equals(pfd_role)) {
								E_list = new ArrayList<>();
								E_list.addAll(pfd_disjunct_list);
								if (E_list.isEmpty()) {
									output_list.add(new Forall(nf_role, pfd_new_filler));
								} else {
									E_list.add(new Forall(nf_role, pfd_new_filler));
									output_list.add(new Or(E_list));
								}
							}

						} else {

							List<Formula> nf_disjunct_list = new ArrayList<>(nf_premise.getSubFormulas());
							for (Formula nf_disjunct : nf_disjunct_list) {
								if (ec.isPresent(concept, nf_disjunct)) {
									Formula nf_role = nf_disjunct.getSubFormulas().get(0);
									if (nf_role.equals(pfd_role)) {
										E_list = new ArrayList<>();
										E_list.addAll(pfd_disjunct_list);
										nf_disjunct_list.remove(nf_disjunct);
										E_list.addAll(nf_disjunct_list);
										E_list.add(new Forall(nf_role, pfd_new_filler));
										output_list.add(new Or(E_list));
										break;
									}
								}
							}
						}
					}
				}
			}
		}
		
		//[10]
		if (!negative_forall_disjunction_premises.isEmpty()) {
			//[10,2]
			if (!positive_exists_premises.isEmpty()) {

				if (negative_star_premises.isEmpty() && negative_exists_premises.isEmpty()
						&& negative_exists_disjunction_premises.isEmpty() && negative_forall_premises.isEmpty()) {
					for (Formula pe_premise : positive_exists_premises) {
						output_list.add(PurifyPositive(concept, pe_premise));
					}
				}

				for (Formula pe_premise : positive_exists_premises) {

					List<Formula> pe_disjunct_list = null;
					Formula pe_role = null;
					if (pe_premise instanceof Exists) {
						pe_disjunct_list = new ArrayList<>();
						pe_role = pe_premise.getSubFormulas().get(0);

					} else {
						pe_disjunct_list = new ArrayList<>(pe_premise.getSubFormulas());
						for (Formula pe_disjunct : pe_disjunct_list) {
							if (ec.isPresent(concept, pe_disjunct)) {
								pe_role = pe_disjunct.getSubFormulas().get(0);
								pe_disjunct_list.remove(pe_disjunct);
								break;
							}
						}
					}

					for (Formula nfd_premise : negative_forall_disjunction_premises) {
						List<Formula> E_list = null;
						List<Formula> nfd_filler_list = null;
						Formula nfd_new_filler = null;

						if (nfd_premise instanceof Forall) {
							Formula nfd_role = nfd_premise.getSubFormulas().get(0);
							if (nfd_role.equals(pe_role)) {
								nfd_filler_list = new ArrayList<>(nfd_premise.getSubFormulas().get(1).getSubFormulas());
								nfd_filler_list.remove(new Negation(concept));
								if (nfd_filler_list.isEmpty()) {
									nfd_new_filler = BottomConcept.getInstance();
								} else if (nfd_filler_list.size() == 1) {
									nfd_new_filler = nfd_filler_list.get(0);
								} else {
									nfd_new_filler = new Or(nfd_filler_list);
								}
								E_list = new ArrayList<>(pe_disjunct_list);
								E_list.addAll(pe_disjunct_list);
								E_list.add(new Forall(nfd_role, nfd_new_filler));
								if (E_list.isEmpty()) {

								} else if (E_list.size() == 1) {
									output_list.add(E_list.get(0));
								} else {
									output_list.add(new Or(E_list));
								}
							}

						} else {
							List<Formula> nfd_disjunct_list = new ArrayList<>(nfd_premise.getSubFormulas());
							for (Formula nfd_disjunct : nfd_disjunct_list) {
								if (ec.isPresent(concept, nfd_disjunct)) {
									Formula nfd_role = nfd_disjunct.getSubFormulas().get(0);
									if (nfd_role.equals(pe_role)) {
										nfd_filler_list = new ArrayList<>(nfd_disjunct.getSubFormulas().get(1).getSubFormulas());
										nfd_filler_list.remove(new Negation(concept));
										if (nfd_filler_list.isEmpty()) {
											nfd_new_filler = BottomConcept.getInstance();
										} else if (nfd_filler_list.size() == 1) {
											nfd_new_filler = nfd_filler_list.get(0);
										} else {
											nfd_new_filler = new Or(nfd_filler_list);
										}
										E_list = new ArrayList<>(pe_disjunct_list);
										nfd_disjunct_list.remove(nfd_disjunct);
										E_list.addAll(nfd_disjunct_list);
										E_list.add(new Forall(nfd_role, nfd_new_filler));
										if (E_list.size() == 1) {
											output_list.add(E_list.get(0));
											break;
										} else {
											output_list.add(new Or(E_list));
											break;
										}
									}
								}
							}
						}
					}
				}
			}
			//[10,3]
			if (!positive_exists_disjunction_premises.isEmpty()) {
				
				if (negative_star_premises.isEmpty() && negative_exists_premises.isEmpty() &&
						negative_exists_disjunction_premises.isEmpty() && negative_forall_premises.isEmpty()) {
					for (Formula ped_premise : positive_exists_disjunction_premises) {
						output_list.add(PurifyPositive(concept, ped_premise));
					}
				}

				for (Formula nfd_premise : negative_forall_disjunction_premises) {
					List<Formula> nfd_disjunct_list = null;
					List<Formula> nfd_filler_list = null;
					//Formula nfd_new_filler = null;
					Formula nfd_role = null;
					if (nfd_premise instanceof Forall) {
						nfd_disjunct_list = new ArrayList<>();
						//C or forall r.~A, pf_role = r
						nfd_filler_list = new ArrayList<>(nfd_premise.getSubFormulas().get(1).getSubFormulas());
						nfd_filler_list.remove(new Negation(concept));
						nfd_role = nfd_premise.getSubFormulas().get(0);
					} else {
						nfd_disjunct_list = new ArrayList<>(nfd_premise.getSubFormulas());
						for (Formula nfd_disjunct : nfd_disjunct_list) {
							//to find the concept of forall r.A
							if (ec.isPresent(concept, nfd_disjunct)) {
								nfd_filler_list = new ArrayList<>(nfd_disjunct.getSubFormulas().get(1).getSubFormulas());
								nfd_filler_list.remove(new Negation(concept));
								nfd_role = nfd_disjunct.getSubFormulas().get(0);
								nfd_disjunct_list.remove(nfd_disjunct);
								break;
							}
						}
					}

					for (Formula ped_premise : positive_exists_disjunction_premises) {
						List<Formula> E_list = null;
						List<Formula> ped_filler_list = null;
						Formula ped_new_filler = null;
						Formula ped_role = null;
						if (ped_premise instanceof Exists) {
							//exists r.(~A or F), ne_role = r
							ped_role = ped_premise.getSubFormulas().get(0);
							if (ped_role.equals(nfd_role)) {
								ped_filler_list = new ArrayList<>(ped_premise.getSubFormulas().get(1).getSubFormulas());
								ped_filler_list.remove(concept);
								ped_filler_list.addAll(nfd_filler_list);
								if (ped_filler_list.isEmpty()) {
									
								} else if (ped_filler_list.size() == 1) {
									ped_new_filler = ped_filler_list.get(0);
									
								} else {
									ped_new_filler = new Or(ped_filler_list);
								}
								E_list = new ArrayList<>(nfd_disjunct_list);
								if (ped_new_filler != null) {
									E_list.add(new Exists(ped_role, ped_new_filler));
								}
								if (E_list.isEmpty()) {

								} else if (E_list.size() == 1) {
									output_list.add(E_list.get(0));
								} else {
									output_list.add(new Or(E_list));
								}
							}
							//C or exists r.(~A or D) 
						} else {
							List<Formula> ped_disjunct_list = new ArrayList<>(ped_premise.getSubFormulas());
							for (Formula ped_disjunct : ped_disjunct_list) {
								//to find the concept of exists r.~A
								if (ec.isPresent(concept, ped_disjunct)) {
									// exists r.~A, ne_role = r
									ped_role = ped_disjunct.getSubFormulas().get(0);
									if (ped_role.equals(nfd_role)) {
										ped_filler_list = new ArrayList<>(ped_disjunct.getSubFormulas().get(1).getSubFormulas());
										ped_filler_list.remove(concept);
										ped_filler_list.addAll(nfd_filler_list);
										if (ped_filler_list.isEmpty()) {
											
										} else if (ped_filler_list.size() == 1) {
											ped_new_filler = ped_filler_list.get(0);
											
										} else {
											ped_new_filler = new Or(ped_filler_list);
										}
										E_list = new ArrayList<>(nfd_disjunct_list);
										ped_disjunct_list.remove(ped_disjunct);
										E_list.addAll(ped_disjunct_list);
										if (ped_new_filler != null) {
											E_list.add(new Exists(ped_role, ped_new_filler));
										}
										if (E_list.size() == 1) {
											output_list.add(E_list.get(0));
											break;
										} else {
											output_list.add(new Or(E_list));
											break;
										}
									}
								}
							}
						}
					}
				}
			}
			//[10,4]
			if (!positive_forall_premises.isEmpty()) {

				for (Formula pf_premise : positive_forall_premises) {
					
					List<Formula> pf_disjunct_list = null;
					Formula pf_role = null;
					if (pf_premise instanceof Forall) {
						pf_disjunct_list = new ArrayList<>();
						pf_role = pf_premise.getSubFormulas().get(0);
					} else {
						pf_disjunct_list = new ArrayList<>(pf_premise.getSubFormulas());
						for (Formula pf_disjunct : pf_disjunct_list) {
							if (ec.isPresent(concept, pf_disjunct)) {
								pf_role = pf_disjunct.getSubFormulas().get(0);
								pf_disjunct_list.remove(pf_disjunct);
								break;
							}
						}
					}

					for (Formula nfd_premise : negative_forall_disjunction_premises) {
						List<Formula> E_list = null;
						List<Formula> nfd_filler_list = null;
						Formula nfd_new_filler = null;
						if (nfd_premise instanceof Forall) {
							Formula nfd_role = nfd_premise.getSubFormulas().get(0);
							if (nfd_role.equals(pf_role)) {
								nfd_filler_list = new ArrayList<>(nfd_premise.getSubFormulas().get(1).getSubFormulas());
								nfd_filler_list.remove(new Negation(concept));
								if (nfd_filler_list.isEmpty()) {
									nfd_new_filler = BottomConcept.getInstance();
								} else if (nfd_filler_list.size() == 1) {
									nfd_new_filler = nfd_filler_list.get(0);
								} else {
									nfd_new_filler = new Or(nfd_filler_list);
								}
								E_list = new ArrayList<>(pf_disjunct_list);
								E_list.addAll(pf_disjunct_list);
								E_list.add(new Forall(nfd_role, nfd_new_filler));
								if (E_list.isEmpty()) {

								} else {
									output_list.add(new Or(E_list));
								}
							}

						} else {

							List<Formula> nfd_disjunct_list = new ArrayList<>(nfd_premise.getSubFormulas());
							for (Formula nfd_disjunct : nfd_disjunct_list) {
								if (ec.isPresent(concept, nfd_disjunct)) {
									Formula nfd_role = nfd_disjunct.getSubFormulas().get(0);
									if (nfd_role.equals(pf_role)) {
										nfd_filler_list = new ArrayList<>(nfd_disjunct.getSubFormulas().get(1).getSubFormulas());
										nfd_filler_list.remove(new Negation(concept));
										if (nfd_filler_list.isEmpty()) {
											nfd_new_filler = BottomConcept.getInstance();
										} else if (nfd_filler_list.size() == 1) {
											nfd_new_filler = nfd_filler_list.get(0);
										} else {
											nfd_new_filler = new Or(nfd_filler_list);
										}
										E_list = new ArrayList<>(pf_disjunct_list);
										nfd_disjunct_list.remove(nfd_disjunct);
										E_list.addAll(nfd_disjunct_list);
										E_list.add(new Forall(nfd_role, nfd_new_filler));
										output_list.add(new Or(E_list));
										break;
									}
								}
							}
						}
					}
				}
			}
			//[10,5]
			if (!positive_forall_disjunction_premises.isEmpty()) {

				for (Formula pfd_premise : positive_forall_disjunction_premises) {
					
					List<Formula> pfd_disjunct_list = null;
					List<Formula> pfd_filler_list = null;
					Formula pfd_role = null;
					if (pfd_premise instanceof Forall) {
						pfd_disjunct_list = new ArrayList<>();
						pfd_role = pfd_premise.getSubFormulas().get(0);
						pfd_filler_list = new ArrayList<>(pfd_premise.getSubFormulas().get(1).getSubFormulas());
						pfd_filler_list.remove(concept);
					} else {
						pfd_disjunct_list = new ArrayList<>(pfd_premise.getSubFormulas());
						for (Formula pfd_disjunct : pfd_disjunct_list) {
							if (ec.isPresent(concept, pfd_disjunct)) {
								pfd_filler_list = new ArrayList<>(pfd_disjunct.getSubFormulas().get(1).getSubFormulas());
								pfd_filler_list.remove(concept);
								pfd_role = pfd_disjunct.getSubFormulas().get(0);
								pfd_disjunct_list.remove(pfd_disjunct);
								break;
							}
						}
					}
					/*if (pfd_filler_list.isEmpty()) {
						pfd_new_filler = BottomConcept.getInstance();
						
					} else if (pfd_filler_list.size() == 1) {
						pfd_new_filler = pfd_filler_list.get(0);
						
					} else {
						pfd_new_filler = new Or(pfd_filler_list);
					}*/

					for (Formula nfd_premise : negative_forall_disjunction_premises) {
						List<Formula> E_list = null;
						List<Formula> nfd_filler_list = null;
						Formula nfd_new_filler = null;
						if (nfd_premise instanceof Forall) {
							Formula nfd_role = nfd_premise.getSubFormulas().get(0);
							if (nfd_role.equals(pfd_role)) {
								nfd_filler_list = new ArrayList<>(nfd_premise.getSubFormulas().get(1).getSubFormulas());
								nfd_filler_list.remove(new Negation(concept));
								nfd_filler_list.addAll(pfd_filler_list);
								if (nfd_filler_list.isEmpty()) {
									nfd_new_filler = BottomConcept.getInstance();									
								} else if (nfd_filler_list.size() == 1) {
									nfd_new_filler = nfd_filler_list.get(0);									
								} else {
									nfd_new_filler = new Or(nfd_filler_list);
								}
								E_list = new ArrayList<>(pfd_disjunct_list);
								E_list.add(new Forall(nfd_role, nfd_new_filler));
								output_list.add(new Or(E_list));
							}

						} else {

							List<Formula> nfd_disjunct_list = new ArrayList<>(nfd_premise.getSubFormulas());
							for (Formula nfd_disjunct : nfd_disjunct_list) {
								if (ec.isPresent(concept, nfd_disjunct)) {
									Formula nfd_role = nfd_disjunct.getSubFormulas().get(0);
									if (nfd_role.equals(pfd_role)) {
										nfd_filler_list = new ArrayList<>(nfd_disjunct.getSubFormulas().get(1).getSubFormulas());
										nfd_filler_list.remove(new Negation(concept));
										nfd_filler_list.addAll(pfd_filler_list);
										if (nfd_filler_list.isEmpty()) {
											nfd_new_filler = BottomConcept.getInstance();									
										} else if (nfd_filler_list.size() == 1) {
											nfd_new_filler = nfd_filler_list.get(0);									
										} else {
											nfd_new_filler = new Or(nfd_filler_list);
										}
										E_list = new ArrayList<>(pfd_disjunct_list);
										nfd_disjunct_list.remove(nfd_disjunct);
										E_list.addAll(nfd_disjunct_list);
										E_list.add(new Forall(nfd_role, nfd_new_filler));
										output_list.add(new Or(E_list));
										break;
									}
								}
							}
						}
					}
				}
			}
		}
		//System.out.println("The output list of Ackermann_A: " + output_list);
		return output_list;
	}
		
	public List<Formula> Ackermann_R(AtomicRole role, List<Formula> formula_list)
			throws CloneNotSupportedException {

		List<Formula> output_list = new ArrayList<>();

		List<Formula> positive_TBox_premises = new ArrayList<>();
		List<Formula> negative_TBox_premises = new ArrayList<>();

		EChecker ec = new EChecker();

		for (Formula formula : formula_list) {
			if (!ec.isPresent(role, formula)) {
				output_list.add(formula);

			} else if (formula instanceof Exists) {
				positive_TBox_premises.add(formula);

			} else if (formula instanceof Forall) {
				negative_TBox_premises.add(formula);

			} else if (formula instanceof Or) {
				List<Formula> disjunct_list = formula.getSubFormulas();

				for (Formula disjunct : disjunct_list) {
					if (disjunct instanceof Exists && disjunct.getSubFormulas().get(0).equals(role)) {
						positive_TBox_premises.add(formula);
						break;
					} else if (disjunct instanceof Forall && disjunct.getSubFormulas().get(0).equals(role)) {
						negative_TBox_premises.add(formula);
						break;
					}
				}

			}
		}
		
		System.out.println("positive_TBox_premises = " + positive_TBox_premises);
		System.out.println("negative_TBox_premises = " + negative_TBox_premises);

		if (positive_TBox_premises.isEmpty() || negative_TBox_premises.isEmpty()) {
			return output_list;
		
		} else {
			
			Simplifier pp = new Simplifier();
			
			List<List<Formula>> combination_list = getCombinations(negative_TBox_premises);
			//System.out.println("combination_list = " + combination_list);
			
			for (Formula pt_premise : positive_TBox_premises) {
				List<Formula> pt_C_list = new ArrayList<>();
				List<Formula> pt_D_list = new ArrayList<>();

				if (pt_premise instanceof Exists) {
					if (pt_premise.getSubFormulas().get(1) instanceof And) {
						pt_D_list.addAll(pt_premise.getSubFormulas().get(1).getSubFormulas());
					} else {
						pt_D_list.add(pt_premise.getSubFormulas().get(1));
					}

				} else {
					List<Formula> pt_disjunct_list = pt_premise.getSubFormulas();

					for (Formula pt_disjunct : pt_disjunct_list) {
						if (pt_disjunct instanceof Exists && pt_disjunct.getSubFormulas().get(0).equals(role)) {
							if (pt_disjunct.getSubFormulas().get(1) instanceof And) {
								pt_D_list.addAll(pt_disjunct.getSubFormulas().get(1).getSubFormulas());
							} else {
								pt_D_list.add(pt_disjunct.getSubFormulas().get(1));
							}
						} else {
							pt_C_list.add(pt_disjunct);
						}
					}

				}

				for (List<Formula> combination : combination_list) {
					List<Formula> CE_list = new ArrayList<>(pt_C_list);
					List<Formula> DF_list = new ArrayList<>(pt_D_list);

					for (Formula nt_premise : combination) {
						if (nt_premise instanceof Forall) {
							if (nt_premise.getSubFormulas().get(1) instanceof And) {
								DF_list.addAll(nt_premise.getSubFormulas().get(1).getSubFormulas());
							} else {
								DF_list.add(nt_premise.getSubFormulas().get(1));
							}

						} else {
							List<Formula> nt_disjunct_list = nt_premise.getSubFormulas();
							for (Formula nt_disjunct : nt_disjunct_list) {
								if (nt_disjunct instanceof Forall
										&& nt_disjunct.getSubFormulas().get(0).equals(role)) {
									if (nt_disjunct.getSubFormulas().get(1) instanceof And) {
										DF_list.addAll(nt_disjunct.getSubFormulas().get(1).getSubFormulas());
									} else {
										DF_list.add(nt_disjunct.getSubFormulas().get(1));
									}

								} else {
									CE_list.add(nt_disjunct);
								}
							}
						}
					}

					Formula DF = null;

					if (DF_list.size() == 1) {
						DF = DF_list.get(0);
					} else {
						DF = new And(DF_list);
					}
					
					//System.out.println("DF = " + DF);
					//System.out.println("pp.getSimplifiedForm(DF) = " + pp.getSimplifiedForm(DF));

					if (pp.getSimplifiedForm(DF.clone()) == BottomConcept.getInstance()) {

						if (CE_list.isEmpty()) {
							continue;
						} else if (CE_list.size() == 1) {
							output_list.add(CE_list.get(0));
							continue;
						} else {
							output_list.add(new Or(CE_list));
							continue;
						}
					}
				}
			}			
		}
		
		return output_list;
	}

			
	/*public List<Formula> Ackermann_R(AtomicRole role, List<Formula> formula_list)
			throws CloneNotSupportedException {

		// System.out.println("role = " + role);
		// System.out.println("formula_list = " + formula_list);

		List<Formula> output_list = new ArrayList<>();

		List<Formula> positive_RBox_premises = new ArrayList<>();
		List<Formula> negative_RBox_premises = new ArrayList<>();
		List<Formula> positive_TBox_premises = new ArrayList<>();
		List<Formula> negative_TBox_premises = new ArrayList<>();

		EChecker ec = new EChecker();
		FChecker fc = new FChecker();

		for (Formula formula : formula_list) {
			if (fc.positive(role, formula) + fc.negative(role, formula) > 1) {
				return formula_list;
						
			} else if (!ec.isPresent(role, formula)) {
				output_list.add(formula);

			} else if (formula.equals(role)) {
				positive_RBox_premises.add(formula);

			} else if (formula.equals(new Negation(role))) {
				negative_RBox_premises.add(formula);

			} else if (formula instanceof Exists && formula.getSubFormulas().get(0).equals(role)) {
				positive_TBox_premises.add(formula);

			} else if (formula instanceof Forall && formula.getSubFormulas().get(0).equals(role)) {
				negative_TBox_premises.add(formula);

			} else if (formula instanceof Or) {
				List<Formula> disjunct_list = formula.getSubFormulas();

				if (disjunct_list.contains(role)) {
					positive_RBox_premises.add(formula);

				} else if (disjunct_list.contains(new Negation(role))) {
					negative_RBox_premises.add(formula);

				} else {
					for (Formula disjunct : disjunct_list) {
						if (disjunct instanceof Exists && disjunct.getSubFormulas().get(0).equals(role)) {
							positive_TBox_premises.add(formula);
							break;
						} else if (disjunct instanceof Forall && disjunct.getSubFormulas().get(0).equals(role)) {
							negative_TBox_premises.add(formula);
							break;
						}
					}
				}
			}
		}

		if (negative_TBox_premises.isEmpty() && negative_RBox_premises.isEmpty()) {
			return output_list;
		}

		if (positive_TBox_premises.isEmpty() && positive_RBox_premises.isEmpty()) {
			return output_list;
		}

		//
		if (!negative_RBox_premises.isEmpty()) {

			if (negative_RBox_premises.contains(new Negation(role))) {
				if (!positive_RBox_premises.isEmpty()) {
					for (Formula pr_premise : positive_RBox_premises) {
						output_list.add(AckermannReplace(role, pr_premise, BottomRole.getInstance()));
					}
				}
				if (!positive_TBox_premises.isEmpty()) {
					for (Formula pt_premise : positive_TBox_premises) {
						output_list.add(AckermannReplace(role, pt_premise, BottomRole.getInstance()));
					}
				}

			} else {

				for (Formula nr_premise : negative_RBox_premises) {

					Formula nr_def = null;
					List<Formula> nr_def_list = new ArrayList<>(nr_premise.getSubFormulas());
					nr_def_list.remove(new Negation(role));
					if (nr_def_list.size() == 1) {
						nr_def = nr_def_list.get(0);
					} else {
						nr_def = new Or(nr_def_list);
					}

					if (!positive_RBox_premises.isEmpty()) {
						for (Formula pr_premise : positive_RBox_premises) {
							output_list.add(AckermannReplace(role, pr_premise, nr_def));
						}
					}
					if (!positive_TBox_premises.isEmpty()) {
						for (Formula pt_premise : positive_TBox_premises) {
							output_list.add(AckermannReplace(role, pt_premise, nr_def));
						}
					}
				}
			}
		}

		//
		if (!positive_RBox_premises.isEmpty()) {

			if (positive_RBox_premises.contains(role)) {
				if (!negative_TBox_premises.isEmpty()) {
					for (Formula nt_premise : negative_TBox_premises) {
						output_list.add(AckermannReplace(role, nt_premise, TopRole.getInstance()));
					}
				}

			} else {

				for (Formula pr_premise : positive_RBox_premises) {

					Formula pr_def = null;
					List<Formula> pr_def_list = new ArrayList<>(pr_premise.getSubFormulas());
					pr_def_list.remove(role);
					if (pr_def_list.size() == 1) {
						pr_def = new Negation(pr_def_list.get(0));
					} else {
						pr_def = new Negation(new Or(pr_def_list));
					}
					if (!negative_TBox_premises.isEmpty()) {
						for (Formula nt_premise : negative_TBox_premises) {
							output_list.add(AckermannReplace(role, nt_premise, pr_def));
						}
					}
				}
			}
		}

		//
		if (!positive_TBox_premises.isEmpty() && !negative_TBox_premises.isEmpty()) {
			
			PreProcessor pp = new PreProcessor();

			if (negative_RBox_premises.isEmpty()) {
				
				for (Formula pt_premise : positive_TBox_premises) {
					List<Formula> pt_C_list = new ArrayList<>();
					List<Formula> pt_D_list = new ArrayList<>();

					if (pt_premise instanceof Exists) {
						if (pt_premise.getSubFormulas().get(1) instanceof And) {
							pt_D_list.addAll(pt_premise.getSubFormulas().get(1).getSubFormulas());
						} else {
							pt_D_list.add(pt_premise.getSubFormulas().get(1));
						}

					} else {
						List<Formula> pt_disjunct_list = pt_premise.getSubFormulas();

						for (Formula pt_disjunct : pt_disjunct_list) {
							if (pt_disjunct instanceof Exists && pt_disjunct.getSubFormulas().get(0).equals(role)) {
								if (pt_disjunct.getSubFormulas().get(1) instanceof And) {
									pt_D_list.addAll(pt_disjunct.getSubFormulas().get(1).getSubFormulas());
								} else {
									pt_D_list.add(pt_disjunct.getSubFormulas().get(1));
								}
							} else {
								pt_C_list.add(pt_disjunct);
							}
						}
					}
						
					List<List<Formula>> combination_list = getCombinations(negative_TBox_premises);
						
					for (List<Formula> combination : combination_list) {
						List<Formula> CE_list = new ArrayList<>(pt_C_list);
						List<Formula> DF_list = new ArrayList<>(pt_D_list);

						for (Formula nt_premise : combination) {
							if (nt_premise instanceof Forall) {
								if (nt_premise.getSubFormulas().get(1) instanceof And) {
									DF_list.addAll(nt_premise.getSubFormulas().get(1).getSubFormulas());
								} else {
									DF_list.add(nt_premise.getSubFormulas().get(1));
								}

							} else {
								List<Formula> nt_disjunct_list = nt_premise.getSubFormulas();
								for (Formula nt_disjunct : nt_disjunct_list) {
									if (nt_disjunct instanceof Forall
											&& nt_disjunct.getSubFormulas().get(0).equals(role)) {
										if (nt_disjunct.getSubFormulas().get(1) instanceof And) {
											DF_list.addAll(nt_disjunct.getSubFormulas().get(1).getSubFormulas());
										} else {
											DF_list.add(nt_disjunct.getSubFormulas().get(1));
										}

									} else {
										CE_list.add(nt_disjunct);
									}
								}
							}
						}

						Formula DF = null;

						if (DF_list.size() == 1) {
							DF = DF_list.get(0);
						} else {
							DF = new And(DF_list);
						}

						if (pp.getSimplifiedForm(DF) == BottomConcept.getInstance() || pp.getSimplifiedForm(DF) == BottomConcept.getInstance()) {

							if (CE_list.isEmpty()) {
								continue;
							} else if (CE_list.size() == 1) {
								output_list.add(CE_list.get(0));
								continue;
							} else {
								output_list.add(new Or(CE_list));
								continue;
							}

						} else {
							continue;
						}
					}
				}

			} else {

				List<List<Formula>> combination_list = getCombinations(negative_TBox_premises);

				for (Formula nr_premise : negative_RBox_premises) {
					Formula nr_def = null;
					if (nr_premise.equals(new Negation(role))) {
						nr_def = BottomRole.getInstance();
					} else {
						List<Formula> nr_def_list = new ArrayList<>(nr_premise.getSubFormulas());
						nr_def_list.remove(new Negation(role));
						if (nr_def_list.size() == 1) {
							nr_def = nr_def_list.get(0);
						} else {
							nr_def = new Or(nr_def_list);
						}
					}

					for (Formula pt_premise : positive_TBox_premises) {
						List<Formula> pt_C_list = new ArrayList<>();
						List<Formula> pt_D_list = new ArrayList<>();

						if (pt_premise instanceof Exists) {
							if (pt_premise.getSubFormulas().get(1) instanceof And) {
								pt_D_list.addAll(pt_premise.getSubFormulas().get(1).getSubFormulas());
							} else {
								pt_D_list.add(pt_premise.getSubFormulas().get(1));
							}

						} else {
							List<Formula> pt_disjunct_list = pt_premise.getSubFormulas();

							for (Formula pt_disjunct : pt_disjunct_list) {
								if (pt_disjunct instanceof Exists && pt_disjunct.getSubFormulas().get(0).equals(role)) {
									if (pt_disjunct.getSubFormulas().get(1) instanceof And) {
										pt_D_list.addAll(pt_disjunct.getSubFormulas().get(1).getSubFormulas());
									} else {
										pt_D_list.add(pt_disjunct.getSubFormulas().get(1));
									}
								} else {
									pt_C_list.add(pt_disjunct);
								}
							}

						}

						for (List<Formula> combination : combination_list) {
							List<Formula> CE_list = new ArrayList<>(pt_C_list);
							List<Formula> DF_list = new ArrayList<>(pt_D_list);

							for (Formula nt_premise : combination) {
								if (nt_premise instanceof Forall) {
									if (nt_premise.getSubFormulas().get(1) instanceof And) {
										DF_list.addAll(nt_premise.getSubFormulas().get(1).getSubFormulas());
									} else {
										DF_list.add(nt_premise.getSubFormulas().get(1));
									}

								} else {
									List<Formula> nt_disjunct_list = nt_premise.getSubFormulas();
									for (Formula nt_disjunct : nt_disjunct_list) {
										if (nt_disjunct instanceof Forall
												&& nt_disjunct.getSubFormulas().get(0).equals(role)) {
											if (nt_disjunct.getSubFormulas().get(1) instanceof And) {
												DF_list.addAll(nt_disjunct.getSubFormulas().get(1).getSubFormulas());
											} else {
												DF_list.add(nt_disjunct.getSubFormulas().get(1));
											}

										} else {
											CE_list.add(nt_disjunct);
										}
									}
								}
							}

							Formula DF = null;

							if (DF_list.size() == 1) {
								DF = DF_list.get(0);
							} else {
								DF = new And(DF_list);
							}

							if (pp.getSimplifiedForm(DF) == BottomConcept.getInstance()
									|| pp.getSimplifiedForm(DF) == BottomConcept.getInstance()) {

								if (CE_list.isEmpty()) {
									continue;
								} else if (CE_list.size() == 1) {
									output_list.add(CE_list.get(0));
									continue;
								} else {
									output_list.add(new Or(CE_list));
									continue;
								}

							} else {

								if (CE_list.isEmpty()) {
									output_list.add(new Exists(nr_def, DF));
									continue;
								} else {
									CE_list.add(new Exists(nr_def, DF));
									output_list.add(new Or(CE_list));
									continue;
								}
							}
						}
					}
				}
			}
		} 
		
		return output_list;
	}*/
	
	
	
	public List<Formula> AckermannPositive(AtomicConcept concept, List<Formula> input_list) throws CloneNotSupportedException {

		List<Formula> output_list = new ArrayList<>();
		List<Formula> toBeReplaced_list = new ArrayList<>();
		List<Formula> toReplace_list = new ArrayList<>();

		FChecker cf = new FChecker();

		for (Formula formula : input_list) {
			if (cf.positive(concept, formula) == 0) {
				toBeReplaced_list.add(formula);

			} else {
				toReplace_list.add(formula);
			}
		}

		Formula definition = null;
		List<Formula> disjunct_list = new ArrayList<>();

		for (Formula toReplace : toReplace_list) {
			if (toReplace.equals(concept)) {
				definition = TopConcept.getInstance();
				break;
				
			} else {
				List<Formula> other_list = new ArrayList<>(toReplace.getSubFormulas());
				other_list.remove(concept);
				if (other_list.size() == 1) {
					disjunct_list.add(new Negation(other_list.get(0)));
					continue;
				} else {
					disjunct_list.add(new Negation(new Or(other_list)));
					continue;
				}
			}
		}

		if (definition != TopConcept.getInstance()) {
			if (disjunct_list.size() == 1) {
				definition = disjunct_list.get(0);
			} else {
				definition = new Or(disjunct_list);
			}
		}

		for (Formula toBeReplaced : toBeReplaced_list) {
			output_list.add(AckermannReplace(concept, toBeReplaced, definition));
		}

		return output_list;
	}
	
	public List<Formula> AckermannNegative(AtomicConcept concept, List<Formula> input_list)
			throws CloneNotSupportedException {
		
		List<Formula> output_list = new ArrayList<>();
		List<Formula> toBeReplaced_list = new ArrayList<>();
		List<Formula> toReplace_list = new ArrayList<>();

		FChecker cf = new FChecker();

		for (Formula formula : input_list) {
			if (cf.negative(concept, formula) == 0) {
				toBeReplaced_list.add(formula);

			} else {
				toReplace_list.add(formula);
			}
		}

		Formula definition = null;
		List<Formula> disjunct_list = new ArrayList<>();

		for (Formula toReplace : toReplace_list) {
			if (toReplace.equals(new Negation(concept))) {
				definition = BottomConcept.getInstance();
				break;
				
			} else {
				List<Formula> other_list = new ArrayList<>(toReplace.getSubFormulas());
				other_list.remove(new Negation(concept));
				if (other_list.size() == 1) {
					disjunct_list.add(other_list.get(0));
					continue;
				} else {
					disjunct_list.add(new Or(other_list));
					continue;
				}
			}
		}

		if (definition != BottomConcept.getInstance()) {
			if (disjunct_list.size() == 1) {
				definition = disjunct_list.get(0);
			} else {
				definition = new And(disjunct_list);
			}
		}

		for (Formula toBeReplaced : toBeReplaced_list) {
			output_list.add(AckermannReplace(concept, toBeReplaced, definition));
		}

		return output_list;
	}

	public List<Formula> PurifyPositive(AtomicRole role, List<Formula> input_list)
			throws CloneNotSupportedException {

		FChecker cf = new FChecker();

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			if (cf.positive(role, formula) == 0) {
				output_list.add(formula);
			} else {
				output_list.add(PurifyPositive(role, formula));
			}
		}

		return output_list;
	}

	public List<Formula> PurifyPositive(AtomicConcept concept, List<Formula> input_list)
			throws CloneNotSupportedException {

		FChecker cf = new FChecker();

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			if (cf.positive(concept, formula) == 0) {
				output_list.add(formula);
			} else {
				output_list.add(PurifyPositive(concept, formula));
			}
		}

		return output_list;
	}

	public List<Formula> PurifyNegative(AtomicRole role, List<Formula> input_list)
			throws CloneNotSupportedException {

		FChecker cf = new FChecker();

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			if (cf.negative(role, formula) == 0) {
				output_list.add(formula);
			} else {
				output_list.add(PurifyNegative(role, formula));
			}
		}

		return output_list;
	}

	public List<Formula> PurifyNegative(AtomicConcept concept, List<Formula> inputList)
			throws CloneNotSupportedException {

		FChecker cf = new FChecker();

		List<Formula> outputList = new ArrayList<>();

		for (Formula formula : inputList) {
			if (cf.negative(concept, formula) == 0) {
				outputList.add(formula);
			} else {
				outputList.add(PurifyNegative(concept, formula));
			}
		}

		return outputList;
	}

	public Formula AckermannReplace(AtomicRole role, Formula toBeReplaced, Formula definition) {

		if (toBeReplaced instanceof AtomicConcept) {
			return new AtomicConcept(toBeReplaced.getText());

		} else if (toBeReplaced instanceof AtomicRole) {
			return toBeReplaced.equals(role) ? definition : new AtomicRole(toBeReplaced.getText());

		} else if (toBeReplaced instanceof Individual) {
			return new Individual(toBeReplaced.getText());
		
		} else if (toBeReplaced instanceof Negation) {
			return new Negation(AckermannReplace(role, toBeReplaced.getSubFormulas().get(0), definition));

		} else if (toBeReplaced instanceof Exists) {
			return new Exists(AckermannReplace(role, toBeReplaced.getSubFormulas().get(0), definition),
					AckermannReplace(role, toBeReplaced.getSubFormulas().get(1), definition));

		} else if (toBeReplaced instanceof Forall) {
			return new Forall(AckermannReplace(role, toBeReplaced.getSubFormulas().get(0), definition),
					AckermannReplace(role, toBeReplaced.getSubFormulas().get(1), definition));

		} else if (toBeReplaced instanceof And) {
			List<Formula> conjunct_list = toBeReplaced.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(AckermannReplace(role, conjunct, definition));
			}
			return new And(new_conjunct_list);

		} else if (toBeReplaced instanceof Or) {
			List<Formula> disjunct_list = toBeReplaced.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(AckermannReplace(role, disjunct, definition));
			}
			return new Or(new_disjunct_list);

		}

		return toBeReplaced;
	}
	
	public Formula AckermannReplace(AtomicConcept concept, Formula toBeReplaced, Formula definition) {

		if (toBeReplaced instanceof AtomicConcept) {
			return toBeReplaced.equals(concept) ? definition : new AtomicConcept(toBeReplaced.getText());
			
		} else if (toBeReplaced instanceof AtomicRole) {
			return new AtomicRole(toBeReplaced.getText());

		} else if (toBeReplaced instanceof Individual) {
			return new Individual(toBeReplaced.getText());
		
		} else if (toBeReplaced instanceof Negation) {
			return new Negation(AckermannReplace(concept, toBeReplaced.getSubFormulas().get(0), definition));
			
		} else if (toBeReplaced instanceof Exists) {
			return new Exists(AckermannReplace(concept, toBeReplaced.getSubFormulas().get(0), definition),
					AckermannReplace(concept, toBeReplaced.getSubFormulas().get(1), definition));

		} else if (toBeReplaced instanceof Forall) {
			return new Forall(AckermannReplace(concept, toBeReplaced.getSubFormulas().get(0), definition),
					AckermannReplace(concept, toBeReplaced.getSubFormulas().get(1), definition));

		} else if (toBeReplaced instanceof And) {
			List<Formula> conjunct_list = toBeReplaced.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(AckermannReplace(concept, conjunct, definition));
			}
			return new And(new_conjunct_list);
			
		} else if (toBeReplaced instanceof Or) {
			List<Formula> disjunct_list = toBeReplaced.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(AckermannReplace(concept, disjunct, definition));
			}
			return new Or(new_disjunct_list);
			
		}
		
		return toBeReplaced;
	}
	
	public Formula PurifyPositive(AtomicRole role, Formula formula) {
		
		if (formula instanceof AtomicConcept) {
			return new AtomicConcept(formula.getText());
		
		} else if (formula instanceof AtomicRole) {
			return formula.equals(role) ? TopRole.getInstance() : new AtomicRole(formula.getText());
		
		} else if (formula instanceof Individual) {
			return new Individual(formula.getText());
		
		} else if (formula instanceof Negation) {
			return new Negation(PurifyPositive(role, formula.getSubFormulas().get(0)));
			
		} else if (formula instanceof Exists) {
			return new Exists(PurifyPositive(role, formula.getSubFormulas().get(0)),
					PurifyPositive(role, formula.getSubFormulas().get(1)));
		
		} else if (formula instanceof Forall) {
			return new Forall(PurifyPositive(role, formula.getSubFormulas().get(0)),
					PurifyPositive(role, formula.getSubFormulas().get(1)));
			
		} else if (formula instanceof And) {
			List<Formula> conjunct_list = formula.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(PurifyPositive(role, conjunct));
			}
			return new And(new_conjunct_list);
			
		} else if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(PurifyPositive(role, disjunct));
			}
			return new Or(new_disjunct_list);
		}

		return formula;
	}
	
	public Formula PurifyNegative(AtomicRole role, Formula formula) {
		
		if (formula instanceof AtomicConcept) {
			return new AtomicConcept(formula.getText());
		
		} else if (formula instanceof AtomicRole) {
			return formula.equals(role) ? BottomRole.getInstance() : new AtomicRole(formula.getText());
		
		} else if (formula instanceof Individual) {
			return new Individual(formula.getText());
		
		} else if (formula instanceof Negation) {
			return new Negation(PurifyNegative(role, formula.getSubFormulas().get(0)));
			
		} else if (formula instanceof Exists) {
			return new Exists(PurifyNegative(role, formula.getSubFormulas().get(0)),
					PurifyNegative(role, formula.getSubFormulas().get(1)));
		
		} else if (formula instanceof Forall) {
			return new Forall(PurifyNegative(role, formula.getSubFormulas().get(0)),
					PurifyNegative(role, formula.getSubFormulas().get(1)));
			
		} else if (formula instanceof And) {
			List<Formula> conjunct_list = formula.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(PurifyNegative(role, conjunct));
			}
			return new And(new_conjunct_list);
			
		} else if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(PurifyNegative(role, disjunct));
			}
			return new Or(new_disjunct_list);
		}

		return formula;
	}
	
	public Formula PurifyPositive(AtomicConcept concept, Formula formula) {

		if (formula instanceof AtomicConcept) {
			return formula.equals(concept) ? TopConcept.getInstance() : new AtomicConcept(formula.getText());
			
		} else if (formula instanceof AtomicRole) {
			return new AtomicRole(formula.getText());

		} else if (formula instanceof Individual) {
			return new Individual(formula.getText());
		
		} else if (formula instanceof Negation) {
			return new Negation(PurifyPositive(concept, formula.getSubFormulas().get(0)));
			
		} else if (formula instanceof Exists) {
			return new Exists(PurifyPositive(concept, formula.getSubFormulas().get(0)),
					PurifyPositive(concept, formula.getSubFormulas().get(1)));
		
		} else if (formula instanceof Forall) {
			return new Forall(PurifyPositive(concept, formula.getSubFormulas().get(0)),
					PurifyPositive(concept, formula.getSubFormulas().get(1)));
			
		} else if (formula instanceof And) {
			List<Formula> conjunct_list = formula.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(PurifyPositive(concept, conjunct));
			}
			return new And(new_conjunct_list);
			
		} else if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(PurifyPositive(concept, disjunct));
			}
			return new Or(new_disjunct_list);
		}

		return formula;
	}
			
	public Formula PurifyNegative(AtomicConcept concept, Formula formula) {

		if (formula instanceof AtomicConcept) {
			return formula.equals(concept) ? BottomConcept.getInstance() : new AtomicConcept(formula.getText());

		} else if (formula instanceof AtomicRole) {
			return new AtomicRole(formula.getText());

		} else if (formula instanceof Individual) {
			return new Individual(formula.getText());
		
		} else if (formula instanceof Negation) {
			return new Negation(PurifyNegative(concept, formula.getSubFormulas().get(0)));
			
		} else if (formula instanceof Exists) {
			return new Exists(PurifyNegative(concept, formula.getSubFormulas().get(0)),
					PurifyNegative(concept, formula.getSubFormulas().get(1)));

		} else if (formula instanceof Forall) {
			return new Forall(PurifyNegative(concept, formula.getSubFormulas().get(0)),
					PurifyNegative(concept, formula.getSubFormulas().get(1)));

		} else if (formula instanceof And) {
			List<Formula> conjunct_list = formula.getSubFormulas();
			List<Formula> new_conjunct_list = new ArrayList<>();
			for (Formula conjunct : conjunct_list) {
				new_conjunct_list.add(PurifyNegative(concept, conjunct));
			}
			return new And(new_conjunct_list);

		} else if (formula instanceof Or) {
			List<Formula> disjunct_list = formula.getSubFormulas();
			List<Formula> new_disjunct_list = new ArrayList<>();
			for (Formula disjunct : disjunct_list) {
				new_disjunct_list.add(PurifyNegative(concept, disjunct));
			}
			return new Or(new_disjunct_list);
		}

		return formula;
	}
	
}
