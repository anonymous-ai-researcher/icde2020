package inference;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLEntity;

import checkexistence.EChecker;
import checkfrequency.FChecker;
import concepts.AtomicConcept;
import connectives.And;
import connectives.Exists;
import connectives.Forall;
import connectives.Negation;
import connectives.Or;
import convertion.BackConverter;
import formula.Formula;
import roles.AtomicRole;
import simplification.Simplifier;

public class DefinerIntroducer {

	public DefinerIntroducer() {

	}

	public static Map<Formula, AtomicConcept> definer_map = new HashMap<>();
	public static Set<OWLEntity> owldefiner_set = new HashSet<>();
	public Set<AtomicConcept> definer_set = new HashSet<>();

	public List<Formula> introduceDefiners(AtomicConcept concept, List<Formula> input_list)
			throws CloneNotSupportedException {

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			output_list.addAll(introduceDefiners(concept, formula));
		}

		return output_list;
	}
	
	//public int i = 1;

	private List<Formula> introduceDefiners(AtomicConcept concept, Formula formula) throws CloneNotSupportedException {
		
		BackConverter bc = new BackConverter();
		EChecker ec = new EChecker();
		FChecker fc = new FChecker();
		Simplifier pp = new Simplifier();
		
		List<Formula> output_list = new ArrayList<>();

		if (fc.positive(concept, formula) + fc.negative(concept, formula) == 1) {

			if (formula instanceof Exists || formula instanceof Forall) {

				Formula filler = formula.getSubFormulas().get(1);

				if (filler.equals(concept) || filler.equals(new Negation(concept))) {

					output_list.add(formula);

				} else if (filler instanceof Or && (filler.getSubFormulas().contains(concept)
						|| filler.getSubFormulas().contains(new Negation(concept)))) {

					output_list.add(formula);

				} else {

					if (definer_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_map.put(filler, definer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
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
							//System.out.println("new Or(disjunct_list) 1 = " + new Or(disjunct_list));
							output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
						}

					} else {
						AtomicConcept definer = definer_map.get(filler);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}
				}

			} else if (formula instanceof Or) {

				List<Formula> disjuncts = formula.getSubFormulas();
				// System.out.println("disjuncts = " + disjuncts);
				if (disjuncts.contains(concept) || disjuncts.contains(new Negation(concept))) {
					output_list.add(formula);

				} else {

					for (Formula disjunct : disjuncts) {
						if (ec.isPresent(concept, disjunct)) {
							// do we really need this step? cause can only be Exists or Forall
							// if (disjunct instanceof Exists || disjunct instanceof Forall) {

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
									owldefiner_set.add(bc.getClassfromConcept(definer));
									definer_map.put(filler, definer);
									disjunct.getSubFormulas().set(1, definer);
									output_list.add(formula);
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
										// System.out.println("disjunct_list = " + disjunct_list);
										//System.out.println("new Or(disjunct_list) 2 = " + new Or(disjunct_list));
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
							// }
						}
					}
				}

			} else {
				// none of the cases of Exists, Forall, Or
				output_list.add(formula);
			}

		} else if (fc.positive(concept, formula) + fc.negative(concept, formula) > 1) {

			if (formula instanceof Exists || formula instanceof Forall) {

				Formula filler = formula.getSubFormulas().get(1);

				if (definer_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_map.put(filler, definer);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
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
						//System.out.println("new Or(disjunct_list) 3 = " + new Or(disjunct_list));
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
					// unsure about this: && (disjunct instanceof Exists || disjunct instanceof
					// Forall)
					if (ec.isPresent(concept, disjunct)) {
						if ((fc.positive(concept, formula) + fc.negative(concept, formula))
								- (fc.positive(concept, disjunct) + fc.negative(concept, disjunct)) > 0) {

							if (definer_map.get(disjunct) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer_" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_map.put(disjunct, definer);
								disjuncts.set(i, definer);
								List<Formula> disjunct_list = new ArrayList<>();
								disjunct_list.add(new Negation(definer));
								disjunct_list.add(disjunct);
								//System.out.println("formula 4 = " + formula);
								//System.out.println("new Or(disjunct_list) 4 = " + new Or(disjunct_list));
								output_list.addAll(introduceDefiners(concept, formula));
								output_list.addAll(introduceDefiners(concept, new Or(disjunct_list)));
								break;

							} else {
								AtomicConcept definer = definer_map.get(disjunct);
								disjuncts.set(i, definer);
								//System.out.println("formula 5 = " + formula);
								output_list.addAll(introduceDefiners(concept, formula));
								break;
							}

						} else {
							Formula filler = disjunct.getSubFormulas().get(1);

							if (definer_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer_" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_map.put(filler, definer);
								disjuncts.get(i).getSubFormulas().set(1, definer);
								output_list.add(formula);
								// List<Formula> conjunct_list =
								// pp.getCNF(pp.getSimplifiedForm(Collections.singletonList(filler)));
								// List<Formula> conjunct_list = pp.getCNF(filler);
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
									//System.out.println("new Or(disjunct_list) 6 = " + new Or(disjunct_list));
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

		} else {
			// do not contain A
			output_list.add(formula);
		}

		return output_list;
	}

	public List<Formula> introduceDefiners(AtomicRole role, List<Formula> input_list)
			throws CloneNotSupportedException {

		List<Formula> output_list = new ArrayList<>();

		for (Formula formula : input_list) {
			output_list.addAll(introduceDefiners(role, formula));
		}

		return output_list;
	}

	private List<Formula> introduceDefiners(AtomicRole role, Formula formula) throws CloneNotSupportedException {

		BackConverter bc = new BackConverter();
		EChecker ec = new EChecker();
		FChecker fc = new FChecker();
		Simplifier pp = new Simplifier();

		List<Formula> output_list = new ArrayList<>();

		if (fc.positive(role, formula) + fc.negative(role, formula) == 1) {

			if (formula instanceof Exists || formula instanceof Forall) {
				Formula formula_role = formula.getSubFormulas().get(0);
				Formula filler = formula.getSubFormulas().get(1);
				if (formula_role.equals(role)) {
					output_list.add(formula);

				} else {
					if (definer_map.get(filler) == null) {
						AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
						AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
						definer_set.add(definer);
						owldefiner_set.add(bc.getClassfromConcept(definer));
						definer_map.put(filler, definer);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
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

					} else {
						AtomicConcept definer = definer_map.get(filler);
						formula.getSubFormulas().set(1, definer);
						output_list.add(formula);
					}
				}

			} else if (formula instanceof Or) {

				List<Formula> disjuncts = formula.getSubFormulas();

				if (disjuncts.contains(role) || disjuncts.contains(new Negation(role))) {
					output_list.add(formula);

				} else {
					for (Formula disjunct : disjuncts) {
						if (ec.isPresent(role, disjunct)) {
							Formula disjunct_role = disjunct.getSubFormulas().get(0);
							if (disjunct_role.equals(role)) {
								output_list.add(formula);
								break;

							} else {
								Formula filler = disjunct.getSubFormulas().get(1);

								if (definer_map.get(filler) == null) {
									AtomicConcept definer = new AtomicConcept(
											"Definer_" + AtomicConcept.getDefiner_index());
									AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
									definer_set.add(definer);
									owldefiner_set.add(bc.getClassfromConcept(definer));
									definer_map.put(filler, definer);
									disjunct.getSubFormulas().set(1, definer);
									output_list.add(formula);
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

		} else if (fc.positive(role, formula) + fc.negative(role, formula) > 1) {

			if (formula instanceof Exists || formula instanceof Forall) {
				Formula filler = formula.getSubFormulas().get(1);

				if (definer_map.get(filler) == null) {
					AtomicConcept definer = new AtomicConcept("Definer_" + AtomicConcept.getDefiner_index());
					AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
					definer_set.add(definer);
					owldefiner_set.add(bc.getClassfromConcept(definer));
					definer_map.put(filler, definer);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
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

				} else {
					AtomicConcept definer = definer_map.get(filler);
					formula.getSubFormulas().set(1, definer);
					output_list.add(formula);
				}

			} else if (formula instanceof Or) {

				List<Formula> disjuncts = formula.getSubFormulas();

				for (int i = 0; i < disjuncts.size(); i++) {
					Formula disjunct = disjuncts.get(i);

					if (ec.isPresent(role, disjunct)) {
						if ((fc.positive(role, formula) + fc.negative(role, formula))
								- (fc.positive(role, disjunct) + fc.negative(role, disjunct)) > 0) {

							if (definer_map.get(disjunct) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer_" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_map.put(disjunct, definer);
								disjuncts.set(i, definer);
								List<Formula> disjunct_list = new ArrayList<>();
								disjunct_list.add(new Negation(definer));
								disjunct_list.add(disjunct);
								output_list.addAll(introduceDefiners(role, formula));
								output_list.addAll(introduceDefiners(role, new Or(disjunct_list)));
								break;

							} else {
								AtomicConcept definer = definer_map.get(disjunct);
								disjuncts.set(i, definer);
								output_list.addAll(introduceDefiners(role, formula));
								break;
							}

						} else {

							Formula filler = disjunct.getSubFormulas().get(1);

							if (definer_map.get(filler) == null) {
								AtomicConcept definer = new AtomicConcept(
										"Definer_" + AtomicConcept.getDefiner_index());
								AtomicConcept.setDefiner_index(AtomicConcept.getDefiner_index() + 1);
								definer_set.add(definer);
								owldefiner_set.add(bc.getClassfromConcept(definer));
								definer_map.put(filler, definer);
								disjuncts.get(i).getSubFormulas().set(1, definer);
								output_list.add(formula);
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

		} else {
			output_list.add(formula);
		}
		// System.out.println("output_list = " + output_list);
		return output_list;
	}

}
