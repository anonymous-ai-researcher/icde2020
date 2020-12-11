package inference;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import checkexistence.EChecker;
import checkfrequency.FChecker;
import concepts.AtomicConcept;
import connectives.And;
import connectives.Exists;
import connectives.Forall;
import connectives.Negation;
import connectives.Or;
import formula.Formula;
import roles.AtomicRole;
import simplification.Simplifier;

public class Introducer {
	
	public Introducer() {
	
	}
	
	public static Map<Formula, AtomicConcept> definer_map = new HashMap<>();
	public static Set<AtomicConcept> definer_set = new HashSet<>();
	
	public List<Formula> introduceDefiners(AtomicConcept concept, List<Formula> input_list) throws CloneNotSupportedException {

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			output_list.addAll(introduceDefiners(concept, formula));
		}

		return output_list;
	}
	

	
	private List<Formula> introduceDefiners(AtomicConcept concept, Formula formula) throws CloneNotSupportedException {
		
		EChecker ec = new EChecker();
		FChecker fc = new FChecker();
		Simplifier pp = new Simplifier();
		
		List<Formula> output_list = new ArrayList<>();
		
		Integer frequency = fc.positive(concept, formula) + fc.negative(concept, formula);
		
		//if concept is not present in formula, then formula is returned immediately.
		if (frequency == 0) {		
			output_list.add(formula);
		//if concept is present in formula once	
		} else if (frequency == 1) {
			
            if (formula instanceof Exists || formula instanceof Forall) {	
            	
				Formula filler = formula.getSubFormulas().get(1);
				// Q r.A || Q r.~A, for Q in {exists, forall}
				if (filler.equals(concept) || filler.equals(new Negation(concept))) {
					//already in A-reduced form
					output_list.add(formula);

				} else if (filler instanceof Or) {
					
					List<Formula> disjunct_list = filler.getSubFormulas();
					// Q r.(A or D) || Q r.(~A or D), for Q in {exists, forall}
					if (disjunct_list.contains(concept) || disjunct_list.contains(new Negation(concept))) {
						//already in A-reduced form
						output_list.add(formula);
					}
					
				} else {
					//if filler has not been defined previously, then define it now 
					if (definer_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						definer_map.put(filler, definer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
						//List<Formula> conjunct_list = pp.getCNF(pp.getSimplifiedForm(Collections.singletonList(filler)));
						List<Formula> conjunct_list = pp.getCNF(filler);
						for (Formula conjunct : conjunct_list) {
							List<Formula> disjunct_list = new ArrayList<>();
							disjunct_list.add(new Negation(definer));
							if (conjunct instanceof Or) {
								disjunct_list.addAll(conjunct.getSubFormulas());
							} else {
								disjunct_list.add(conjunct);	
							}
							output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
						}
					//if filler has been defined previously, then use the definer directly
					} else {
						AtomicConcept definer = definer_map.get(filler);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}				
				}
				
			} else if (formula instanceof Or) {

				List<Formula> disjuncts = formula.getSubFormulas();

				if (disjuncts.contains(concept) || disjuncts.contains(new Negation(concept))) {
					output_list.add(formula);

				} else {

					for (Formula disjunct : disjuncts) {
						if (ec.isPresent(concept, disjunct)) {
							
							if (disjunct instanceof Exists || disjunct instanceof Forall) {
								
								Formula filler = disjunct.getSubFormulas().get(1);

								if (filler.equals(concept) || filler.equals(new Negation(concept))) {
									output_list.add(formula);
									break;

								} else if (filler instanceof Or && (filler.getSubFormulas().contains(concept)
										|| filler.getSubFormulas().contains(new Negation(concept)))) {									
									output_list.add(formula);
									break;

								} else {

									if (definer_map.get(filler) == null) {
										AtomicConcept definer = new AtomicConcept(
												"Definer_" + AtomicConcept.getDefiner_index());
										AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
										definer_set.add(definer);
										definer_map.put(filler, definer);
										disjunct.getSubFormulas().set(1, definer);
										output_list.add(formula);
								        //List<Formula> conjunct_list = pp.getCNF(pp.getSimplifiedForm(Collections.singletonList(filler)));
										List<Formula> conjunct_list = pp.getCNF(filler);
										for (Formula conjunct : conjunct_list) {
											List<Formula> disjunct_list = new ArrayList<>();
											disjunct_list.add(new Negation(definer));
											if (conjunct instanceof Or) {
												disjunct_list.addAll(conjunct.getSubFormulas());
											} else {
												disjunct_list.add(conjunct);
											}
											output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
										}
										break;

									} else {
										AtomicConcept definer = definer_map.get(filler);
										disjunct.getSubFormulas().set(1, definer);
										output_list.add(formula);
										break;
									}
								}											
							}	
						}
					}
				}

			} else {
				// none of the cases of Exists, Forall, Or
				output_list.add(formula);
				
			}

		} else {
			
			if (formula instanceof Exists || formula instanceof Forall) {
				
				Formula filler = formula.getSubFormulas().get(1);
				
				if (definer_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					definer_map.put(filler, definer);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
					//List<Formula> conjunct_list = pp.getCNF(pp.getSimplifiedForm(Collections.singletonList(filler)));
					List<Formula> conjunct_list = pp.getCNF(filler);
					for (Formula conjunct : conjunct_list) {
						List<Formula> disjunct_list = new ArrayList<>();
						disjunct_list.add(new Negation(definer));
						if (conjunct instanceof Or) {
							disjunct_list.addAll(conjunct.getSubFormulas());
						} else {
							disjunct_list.add(conjunct);	
						}
						output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
					}

				} else {
					AtomicConcept definer = definer_map.get(filler);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
				}	
				
			} else if (formula instanceof Or) {
				
			    List<Formula> disjuncts = formula.getSubFormulas();
				
				for (int i = 0; i < disjuncts.size(); i++) {						
					Formula disjunct = disjuncts.get(i);
					
					if (ec.isPresent(concept, disjunct)
							&& (disjunct instanceof Exists || disjunct instanceof Forall)) {
						if ((fc.positive(concept, formula) + fc.negative(concept, formula))
								- (fc.positive(concept, disjunct) + fc.negative(concept, disjunct)) > 0) {					

							if (definer_map.get(disjunct) == null) {
								AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								definer_map.put(disjunct, definer);
								disjuncts.set(i, definer);
								List<Formula> disjunct_list = new ArrayList<>();
								disjunct_list.add(new Negation(definer));
								disjunct_list.add(disjunct);
								output_list.addAll(introduceDefiners(concept, formula));
								output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
								break;

							} else {
								AtomicConcept definer = definer_map.get(disjunct);
								disjuncts.set(i, definer);
								output_list.addAll(introduceDefiners(concept, formula));
								break;
							} 

						} else {
                            
							Formula filler = disjunct.getSubFormulas().get(1);

							if (definer_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								definer_map.put(filler, definer);
								disjuncts.get(i).getSubFormulas().set(1, definer);
								output_list.add(formula);
								//List<Formula> conjunct_list = pp.getCNF(pp.getSimplifiedForm(Collections.singletonList(filler)));
								List<Formula> conjunct_list = pp.getCNF(filler);
								for (Formula conjunct : conjunct_list) {
									List<Formula> disjunct_list = new ArrayList<>();
									disjunct_list.add(new Negation(definer));
									if (conjunct instanceof Or) {
										disjunct_list.addAll(conjunct.getSubFormulas());
									} else {
										disjunct_list.add(conjunct);	
									}
									output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
								}
								break;

							} else {
								AtomicConcept definer = definer_map.get(filler);
								disjuncts.get(i).getSubFormulas().set(1, definer);
								output_list.add(formula);
								break;
							}
						}
					}
				}
		
			} else {
						
				output_list.add(formula);
			}			
		}
		
		return output_list;
	}
	
	public List<Formula> introduceDefiners(AtomicRole role, List<Formula> input_list) throws CloneNotSupportedException {

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			output_list.addAll(introduceDefiners(role, formula));
		}

		return output_list;
	}
	
	private List<Formula> introduceDefiners(AtomicRole role, Formula formula) throws CloneNotSupportedException {
		
		EChecker ec = new EChecker();
		FChecker fc = new FChecker();
		Simplifier pp = new Simplifier();

		List<Formula> output_list = new ArrayList<>();

		if (ec.isPresent(role, formula)) {
			
			if (formula instanceof Exists || formula instanceof Forall) {
				Formula filler = formula.getSubFormulas().get(1);
				
				if (ec.isPresent(role, filler)) {				
					Formula filler_negated = pp.getSimplifiedForm(new Negation(filler.clone()));
					
					if (definer_map.get(filler) != null) {
						AtomicConcept definer = definer_map.get(filler);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
					
					} else if (definer_map.get(filler_negated) != null) {
						Formula definer_negated = new Negation(definer_map.get(filler_negated));
						formula.getSubFormulas().set(1, definer_negated);
						output_list.add(formula);
						
						List<Formula> conjunct_list = pp.getCNF(pp.getSimplifiedForm(Collections.singletonList(filler.clone())));
						for (Formula conjunct : conjunct_list) {
							List<Formula> disjunct_list = new ArrayList<>();
							disjunct_list.add(definer_map.get(filler_negated));
							if (conjunct instanceof Or) {
								disjunct_list.addAll(conjunct.getSubFormulas());
							} else {
								disjunct_list.add(conjunct);	
							}
							output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
						}
											
					} else {					
						AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						definer_map.put(filler, definer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
						//List<Formula> conjunct_list = pp.getCNF(pp.getSimplifiedForm(Collections.singletonList(filler.clone())));
						List<Formula> conjunct_list = null;
						if (filler instanceof And) {
							conjunct_list = filler.getSubFormulas();
						} else {
							conjunct_list = pp.getCNF(filler);
						}
						for (Formula conjunct : conjunct_list) {
							List<Formula> disjunct_list = new ArrayList<>();
							disjunct_list.add(new Negation(definer));
							if (conjunct instanceof Or) {
								disjunct_list.addAll(conjunct.getSubFormulas());
							} else {
								disjunct_list.add(conjunct);	
							}
							output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
						}										
					}
										
				} else {
					output_list.add(formula);
				}

			} else if (formula instanceof Or) {
				List<Formula> disjuncts = formula.getSubFormulas();
				
				if (fc.positive(role, formula) + fc.negative(role, formula) == 1) {
					for (Formula disjunct : disjuncts) {
						if (ec.isPresent(role, disjunct)) {
							Formula filler = disjunct.getSubFormulas().get(1);
							if (ec.isPresent(role, filler)) {
								Formula filler_negated = pp.getSimplifiedForm(new Negation(filler.clone()));
								if (definer_map.get(filler) != null) {
									AtomicConcept definer = definer_map.get(filler);
									disjunct.getSubFormulas().set(1, definer);
									output_list.add(formula);
									break;
								
								} else if (definer_map.get(filler_negated) != null) {
									Formula definer_negated = new Negation(definer_map.get(filler_negated));
									disjunct.getSubFormulas().set(1, definer_negated);
									output_list.add(formula);
									
									//List<Formula> conjunct_list = pp.getCNF(pp.getSimplifiedForm(Collections.singletonList(filler.clone())));
									List<Formula> conjunct_list = null;
									if (filler instanceof And) {
										conjunct_list = filler.getSubFormulas();
									} else {
										conjunct_list = pp.getCNF(filler);
									}
									for (Formula conjunct : conjunct_list) {
										List<Formula> disjunct_list = new ArrayList<>();
										disjunct_list.add(definer_map.get(filler_negated));
										if (conjunct instanceof Or) {
											disjunct_list.addAll(conjunct.getSubFormulas());
										} else {
											disjunct_list.add(conjunct);	
										}
										output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
									}
									
									break;
									
								} else {	
									AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
									AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
									definer_set.add(definer);
									definer_map.put(filler, definer);
									disjunct.getSubFormulas().set(1, definer);
									output_list.add(formula);
									//List<Formula> conjunct_list = pp.getCNF(pp.getSimplifiedForm(Collections.singletonList(filler.clone())));
									List<Formula> conjunct_list = null;
									if (filler instanceof And) {
										conjunct_list = filler.getSubFormulas();
									} else {
										conjunct_list = pp.getCNF(filler);
									}
									for (Formula conjunct : conjunct_list) {
										List<Formula> disjunct_list = new ArrayList<>();
										disjunct_list.add(new Negation(definer));
										if (conjunct instanceof Or) {
											disjunct_list.addAll(conjunct.getSubFormulas());
										} else {
											disjunct_list.add(conjunct);	
										}
										output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
									}
									break;
								}
								
							} else {
								output_list.add(formula);
							}
						}
					}
					// Case: >= 2
				} else {

					for (int i = 0; i < disjuncts.size(); i++) {
						Formula disjunct = disjuncts.get(i);
						if (ec.isPresent(role, disjunct)) {
							if ((fc.positive(role, formula) + fc.negative(role, formula))
									- (fc.positive(role, disjunct) + fc.negative(role, disjunct)) > 0) {
								
								Formula disjunct_negated = pp.getSimplifiedForm(new Negation(disjunct.clone()));
								
								if (definer_map.get(disjunct) != null) {
									AtomicConcept definer = definer_map.get(disjunct);
									disjuncts.set(i, definer);
									output_list.addAll(introduceDefiners(role, formula));
									break;
								
								} else if (definer_map.get(disjunct_negated) != null) {
									Formula definer_negated = new Negation(definer_map.get(disjunct_negated));
									disjuncts.set(i, definer_negated);						
									List<Formula> disjunct_list = new ArrayList<>();
									disjunct_list.add(definer_map.get(disjunct_negated));
									disjunct_list.add(disjunct);
									output_list.addAll(introduceDefiners(role, formula));
									output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
									break;
									
								} else {	
									AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
									AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
									definer_set.add(definer);
									definer_map.put(disjunct, definer);
									disjuncts.set(i, definer);
									List<Formula> disjunct_list = new ArrayList<>();
									disjunct_list.add(new Negation(definer));
									disjunct_list.add(disjunct);
									output_list.addAll(introduceDefiners(role, formula));
									output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
									break;
								}
								
							} else {
								
								Formula filler = disjunct.getSubFormulas().get(1);
								Formula filler_negated = pp.getSimplifiedForm(new Negation(filler.clone()));
								
								if (definer_map.get(filler) != null) {
									AtomicConcept definer = definer_map.get(filler);
									disjunct.getSubFormulas().set(1, definer);
									output_list.add(formula);
									break;
								
								} else if (definer_map.get(filler_negated) != null) {
									Formula definer_negated = new Negation(definer_map.get(filler_negated));
									disjunct.getSubFormulas().set(1, definer_negated);
									output_list.add(formula);
									//List<Formula> conjunct_list = pp.getCNF(pp.getSimplifiedForm(Collections.singletonList(filler.clone())));
									List<Formula> conjunct_list = null;
									if (filler instanceof And) {
										conjunct_list = filler.getSubFormulas();
									} else {
										conjunct_list = pp.getCNF(filler);
									}
									for (Formula conjunct : conjunct_list) {
										List<Formula> disjunct_list = new ArrayList<>();
										disjunct_list.add(definer_map.get(filler_negated));
										if (conjunct instanceof Or) {
											disjunct_list.addAll(conjunct.getSubFormulas());
										} else {
											disjunct_list.add(conjunct);	
										}
										output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
									}
									
									break;
									
								} else {	
									AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
									AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
									definer_set.add(definer);
									definer_map.put(filler, definer);
									disjunct.getSubFormulas().set(1, definer);
									output_list.add(formula);
									//List<Formula> conjunct_list = pp.getCNF(pp.getSimplifiedForm(Collections.singletonList(filler.clone())));
									List<Formula> conjunct_list = null;
									if (filler instanceof And) {
										conjunct_list = filler.getSubFormulas();
									} else {
										conjunct_list = pp.getCNF(filler);
									}
									for (Formula conjunct : conjunct_list) {
										List<Formula> disjunct_list = new ArrayList<>();
										disjunct_list.add(new Negation(definer));
										if (conjunct instanceof Or) {
											disjunct_list.addAll(conjunct.getSubFormulas());
										} else {
											disjunct_list.add(conjunct);	
										}
										output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
									}
									break;
								}
							}
						}
					}
				}

			} else {
				output_list.add(formula);
			}

		} else {
			output_list.add(formula);
		}
		
		//System.out.println("output_list = " + output_list);

		return output_list;
	}

}
