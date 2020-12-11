package forgetting;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import com.google.common.collect.Sets;

import checkfrequency.FChecker;
import checkreducedform.RFChecker;
import concepts.AtomicConcept;
import convertion.BackConverter;
import convertion.Converter;
import extraction.SubsetExtractor;
import formula.Formula;
import inference.Inferencer;
import inference.DefinerIntroducer;
import roles.AtomicRole;
import simplification.Simplifier;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;


public class Forgetter {
	

	public OWLOntology Forgetting(Set<OWLClass> c_sig_owl, Set<OWLObjectProperty> r_sig_owl, OWLOntology onto)
			throws CloneNotSupportedException, OWLOntologyCreationException {
		

		System.out.println("The Forgetting Starts:");
		
		if (c_sig_owl.isEmpty() && r_sig_owl.isEmpty()) {
			return onto;
		}
		
		System.out.println("c_sig_owl = " + c_sig_owl.size());
		System.out.println("r_sig_owl = " + r_sig_owl.size());
		System.out.println("onto = " + onto.getLogicalAxiomCount());

		Converter ct = new Converter();
		BackConverter bc = new BackConverter();
		
		OWLOntology onto_subclassof = ct.toOWLSubClassOfAxiom(onto);
		
		System.out.println("onto_subclassof= " + onto_subclassof.getLogicalAxiomCount());
		
		Set<OWLClass> c_sig_owl_m = Sets.difference(onto_subclassof.getClassesInSignature(), c_sig_owl);
		Set<OWLEntity> c_sig_owl_m_entity = new HashSet<>(c_sig_owl_m);
		
		Set<OWLObjectProperty> r_sig_owl_m = Sets.difference(onto_subclassof.getObjectPropertiesInSignature(), r_sig_owl);
		Set<OWLEntity> r_sig_owl_m_entity = new HashSet<>(r_sig_owl_m);
		
		Set<OWLEntity> sig_owl_m_entity = Sets.union(c_sig_owl_m_entity, r_sig_owl_m_entity);
		
		Simplifier simp = new Simplifier();
		SubsetExtractor se = new SubsetExtractor();
		DefinerIntroducer di = new DefinerIntroducer();
		Inferencer inf = new Inferencer();
		FChecker fc = new FChecker();
		RFChecker rfc = new RFChecker();

		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager, onto_subclassof,
				ModuleType.BOT);
		
		OWLOntology module = extractor.extractAsOntology(sig_owl_m_entity, IRI.generateDocumentIRI());
		System.out.println("module = " + module.getLogicalAxiomCount());
		OWLOntology result = manager.createOntology(IRI.generateDocumentIRI());
		//Set<OWLLogicalAxiom> remaining = Sets.difference(refined_onto.getLogicalAxioms(), module.getLogicalAxioms());
		
		
		List<Formula> clause_list_normalised = simp.getCNF(simp.getSimplifiedForm(simp.getClauses(ct.OntologyConverter(module))));
		Set<AtomicConcept> c_sig = ct.getConceptsfromClasses(c_sig_owl);
		Set<AtomicRole> r_sig = ct.getRolesfromObjectProperties(r_sig_owl);
		
		if (!c_sig.isEmpty()) {
			//SyntacticLocalityModuleExtractor c_extractor = new SyntacticLocalityModuleExtractor(manager, module, ModuleType.BOT);
			
			//OWLOntology c_module = c_extractor.extractAsOntology(c_sig_owl_m_entity, IRI.generateDocumentIRI());
			List<Formula> c_sig_list_normalised = se.getConceptSubset(c_sig, clause_list_normalised);
			List<Formula> pivot_list_normalised = null;
			int j = 1;
			for (AtomicConcept concept : c_sig) {
				System.out.println("Forgetting Concept [" + j + "] = " + concept);
				j++;
				pivot_list_normalised = simp
						.getCNF(simp.getSimplifiedForm(se.getConceptSubset(concept, c_sig_list_normalised)));
				//System.out.println("=====================================================================");
				//System.out.println("pivot_list_normalised = " + pivot_list_normalised);
				//System.out.println("=====================================================================");
				
				if (pivot_list_normalised.isEmpty()) {

				} else if (fc.negative(concept, pivot_list_normalised) == 0) {
					//System.out.println("2");
					c_sig_list_normalised.addAll(
							simp.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(concept, pivot_list_normalised))));

				} else if (fc.positive(concept, pivot_list_normalised) == 0) {
					//System.out.println("3");
					c_sig_list_normalised.addAll(
							simp.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(concept, pivot_list_normalised))));

				} else if (rfc.isAReducedFormPositive(concept, pivot_list_normalised)) {
					//System.out.println("4");
					c_sig_list_normalised.addAll(
							simp.getCNF(simp.getSimplifiedForm(inf.AckermannPositive(concept, pivot_list_normalised))));

				} else if (rfc.isAReducedFormNegative(concept, pivot_list_normalised)) {
					//System.out.println("5");
					c_sig_list_normalised.addAll(
							simp.getCNF(simp.getSimplifiedForm(inf.AckermannNegative(concept, pivot_list_normalised))));

				} else {
					//System.out.println("6");
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(di.introduceDefiners(concept, pivot_list_normalised)));
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(inf.combination_A(concept, pivot_list_normalised)));
					
					c_sig_list_normalised.addAll(pivot_list_normalised);
				}
			}

			clause_list_normalised.addAll(c_sig_list_normalised);
		}
		
		if (!r_sig.isEmpty()) {
			List<Formula> r_sig_list_normalised = se.getRoleSubset(r_sig, clause_list_normalised);
			List<Formula> pivot_list_normalised = null;
			int i = 1;
			for (AtomicRole role : r_sig) {
				System.out.println("Forgetting Role [" + i + "] = " + role);
				i++;
				pivot_list_normalised = simp
						.getCNF(simp.getSimplifiedForm(se.getRoleSubset(role, r_sig_list_normalised)));
				if (pivot_list_normalised.isEmpty()) {

				} else {
					pivot_list_normalised = di.introduceDefiners(role, pivot_list_normalised);
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(inf.Ackermann_R(role, pivot_list_normalised)));
					r_sig_list_normalised.addAll(pivot_list_normalised);
				}
			}

			clause_list_normalised.addAll(r_sig_list_normalised);
		}
		
		if (!di.definer_set.isEmpty()) {
			List<Formula> d_sig_list_normalised = se.getConceptSubset(di.definer_set,
					clause_list_normalised);
			List<Formula> pivot_list_normalised = null;
			Set<AtomicConcept> definer_set = null;

			int k = 1;
			do {
				// System.out.println("d_sig_list_normalised = " + d_sig_list_normalised);
				if (di.definer_set.isEmpty()) {
					System.out.println("Forgetting Successful!");
					System.out.println("===================================================");
					clause_list_normalised.addAll(d_sig_list_normalised);
					manager.addAxioms(result, bc.toOWLAxioms(bc.toAxioms(clause_list_normalised)));
					return result;
				}

				definer_set = new HashSet<>(di.definer_set);

				for (AtomicConcept concept : definer_set) {
					System.out.println("Forgetting Definer [" + k + "] = " + concept);
					k++;
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(se.getConceptSubset(concept, d_sig_list_normalised)));
					if (pivot_list_normalised.isEmpty()) {

					} else if (fc.negative(concept, pivot_list_normalised) == 0) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(concept, pivot_list_normalised))));
						di.definer_set.remove(concept);

					} else if (fc.positive(concept, pivot_list_normalised) == 0) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(concept, pivot_list_normalised))));
						di.definer_set.remove(concept);

					} else if (rfc.isAReducedFormPositive(concept, pivot_list_normalised)) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.AckermannPositive(concept, pivot_list_normalised))));
						di.definer_set.remove(concept);

					} else if (rfc.isAReducedFormNegative(concept, pivot_list_normalised)) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.AckermannNegative(concept, pivot_list_normalised))));
						di.definer_set.remove(concept);

					} else {
						pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
						pivot_list_normalised = simp
								.getCNF(simp.getSimplifiedForm(inf.combination_A(concept, pivot_list_normalised)));
						d_sig_list_normalised.addAll(pivot_list_normalised);
						di.definer_set.remove(concept);

					}
				}

			} while (definer_set.size() > di.definer_set.size());
			//// this is the case of the cyclic cases, that's why the ACK_A is not re-used.
			// In case the results of contains this case. report!
			do {
				if (di.definer_set.isEmpty()) {
					System.out.println("Forgetting Successful!");
					System.out.println("===================================================");
					clause_list_normalised.addAll(d_sig_list_normalised);
					manager.addAxioms(result, bc.toOWLAxioms(bc.toAxioms(clause_list_normalised)));
					return result;
				}

				//System.out.println("The formula might contain cyclic case: " + d_sig_list_normalised);

				definer_set = new HashSet<>(di.definer_set);

				for (AtomicConcept concept : definer_set) {
					System.out.println("Forgetting Definer [" + k + "] = " + concept);
					k++;
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(se.getConceptSubset(concept, d_sig_list_normalised)));
					if (pivot_list_normalised.isEmpty()) {
						di.definer_set.remove(concept);

					} else if (fc.negative(concept, pivot_list_normalised) == 0) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(concept, pivot_list_normalised))));
						di.definer_set.remove(concept);

					} else if (fc.positive(concept, pivot_list_normalised) == 0) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(concept, pivot_list_normalised))));
						di.definer_set.remove(concept);

					} else if (rfc.isAReducedFormPositive(concept, pivot_list_normalised)) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.AckermannPositive(concept, pivot_list_normalised))));
						di.definer_set.remove(concept);

					} else if (rfc.isAReducedFormNegative(concept, pivot_list_normalised)) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.AckermannNegative(concept, pivot_list_normalised))));
						di.definer_set.remove(concept);

					} else {
						d_sig_list_normalised.addAll(pivot_list_normalised);
					}
				}

			} while (definer_set.size() > di.definer_set.size());

		} else {
			System.out.println("Forgetting Successful!");
			manager.addAxioms(result, bc.toOWLAxioms(bc.toAxioms(clause_list_normalised)));
			return result;
		}
 
		/*if (!c_sig.isEmpty()) {
			SyntacticLocalityModuleExtractor c_extractor = new SyntacticLocalityModuleExtractor(manager, module,
					ModuleType.BOT);
			Set<OWLEntity> c_sig_AsEntity = Sets.difference(set1, set2);
			OWLOntology c_module = c_extractor.extractAsOntology(, IRI.generateDocumentIRI());
			OWLOntology c_module = extractor.extractAsOntology(c_sig, IRI.generateDocumentIRI());
			System.out.println("c_module = " + c_module);
			System.out.println("c_module size = " + c_module.getLogicalAxiomCount());
			int l = 1;
			for (OWLLogicalAxiom ola : refined_onto.getLogicalAxioms()) {
				System.out.println("ola refined_onto[" + l + "] = " + ola);
				l++;
			}
			System.out.println("====================================================");
			manager.removeAxioms(refined_onto, c_module.getLogicalAxioms());
			int j = 1;
			for (OWLLogicalAxiom ola : refined_onto.getLogicalAxioms()) {
				System.out.println("ola refined_onto_after[" + j + "] = " + ola);
				j++;
			}
			System.out.println("====================================================");
			int k = 1;
			for (OWLLogicalAxiom ola : c_module.getLogicalAxioms()) {
				System.out.println("ola c_module[" + k + "] = " + ola);
				k++;
			}
			System.out.println("refined_onto = " + refined_onto.getLogicalAxiomCount());
			System.out.println("refined_onto = " + refined_onto.getLogicalAxioms());
			SyntacticLocalityModuleExtractor sub_extractor_1 = new SyntacticLocalityModuleExtractor(manager, c_module,
					ModuleType.TOP);

			AtomicConcept pivot = null;
			OWLOntology pivot_module = null;
			List<Formula> pivot_list = null;
			List<Formula> exact_list = null;
			Set<OWLEntity> pivot_module_sig = null;

			int i = 1;

			for (OWLEntity owlclass : c_sig) {
				System.out.println("Forgetting Concept [" + i + "] = " + owlclass.getIRI().getShortForm());
				i++;
				pivot_module_sig = new HashSet<>();
				pivot_module_sig.add(owlclass);
				pivot_module = sub_extractor_1.extractAsOntology(pivot_module_sig, IRI.generateDocumentIRI());
				// System.out.println("pivot_module size = " + pivot_module.getAxiomCount());
				manager.removeAxioms(c_module, pivot_module.getAxioms());
				pivot = ct.getConceptfromClass(owlclass);
				pivot_list = simp.getCNF(simp.getSimplifiedForm(simp.getClauses(ct.OntologyConverter(pivot_module))));
				// System.out.println("pivot_list size = " + pivot_list.size());
				exact_list = se.getConceptSubset(pivot, pivot_list);
				// System.out.println("exact_list size = " + exact_list.size());

				if (pivot_list.isEmpty()) {

				} else if (fc.negative(pivot, exact_list) == 0) {
					exact_list = simp.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(pivot, exact_list)));
					pivot_list.addAll(exact_list);
					manager.addAxioms(c_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));

				} else if (fc.positive(pivot, exact_list) == 0) {
					exact_list = simp.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(pivot, pivot_list)));
					pivot_list.addAll(exact_list);
					manager.addAxioms(c_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));

				} else if (rfc.isAReducedFormPositive(pivot, exact_list)) {
					exact_list = simp.getCNF(simp.getSimplifiedForm(inf.AckermannPositive(pivot, exact_list)));
					pivot_list.addAll(exact_list);
					manager.addAxioms(c_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));

				} else if (rfc.isAReducedFormNegative(pivot, exact_list)) {
					exact_list = simp.getCNF(simp.getSimplifiedForm(inf.AckermannNegative(pivot, exact_list)));
					pivot_list.addAll(exact_list);
					manager.addAxioms(c_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));

				} else {
					exact_list = simp.getCNF(simp.getSimplifiedForm(di.introduceDefiners(pivot, exact_list)));
					exact_list = simp.getCNF(simp.getSimplifiedForm(inf.combination_A(pivot, exact_list)));
					pivot_list.addAll(exact_list);
					manager.addAxioms(c_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
				}
			}

			manager.addAxioms(refined_onto, c_module.getAxioms());
		}
		
		SyntacticLocalityModuleExtractor extractor_2 = new SyntacticLocalityModuleExtractor(manager, refined_onto,
				ModuleType.BOT);

		if (!r_sig.isEmpty()) {
			OWLOntology r_module = extractor_2.extractAsOntology(r_sig, IRI.generateDocumentIRI());
			System.out.println("r_module size = " + r_module.getAxiomCount());
			manager.removeAxioms(refined_onto, r_module.getAxioms());
			SyntacticLocalityModuleExtractor sub_extractor_2 = new SyntacticLocalityModuleExtractor(manager, r_module,
					ModuleType.BOT);

			AtomicRole pivot = null;
			OWLOntology pivot_module = null;
			List<Formula> pivot_list = null;
			Set<OWLEntity> pivot_module_sig = null;

			int i = 1;

			for (OWLEntity owlobjectproperty : r_sig) {
				System.out.println("Forgetting Role [" + i + "] = " + owlobjectproperty.getIRI().getShortForm());
				i++;
				pivot_module_sig = new HashSet<>();
				pivot_module_sig.add(owlobjectproperty);
				pivot_module = sub_extractor_2.extractAsOntology(pivot_module_sig, IRI.generateDocumentIRI());
				System.out.println("pivot_module size = " + pivot_module.getAxiomCount());
				manager.removeAxioms(r_module, pivot_module.getAxioms());
				pivot_list = simp.getCNF(simp.getSimplifiedForm(simp.getClauses(ct.OntologyConverter(pivot_module))));
				pivot = ct.getRoleFromObjectProperty(owlobjectproperty);

				if (pivot_list.isEmpty()) {

				} else {
					pivot_list = di.introduceDefiners(pivot, pivot_list);
					pivot_list = simp.getCNF(simp.getSimplifiedForm(inf.Ackermann_R(pivot, pivot_list)));
					manager.addAxioms(r_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
				}
			}

			manager.addAxioms(refined_onto, r_module.getAxioms());
		}
		
		SyntacticLocalityModuleExtractor extractor_3 = new SyntacticLocalityModuleExtractor(manager, refined_onto,
				ModuleType.BOT);

		if (!DefinerIntroducer.owldefiner_set.isEmpty()) {
			OWLOntology d_module = extractor_3.extractAsOntology(DefinerIntroducer.owldefiner_set,
					IRI.generateDocumentIRI());
			manager.removeAxioms(refined_onto, d_module.getAxioms());
			SyntacticLocalityModuleExtractor sub_extractor_3 = new SyntacticLocalityModuleExtractor(manager, d_module,
					ModuleType.BOT);

			AtomicConcept pivot = null;
			OWLOntology pivot_module = null;
			List<Formula> pivot_list = null;
			List<Formula> exact_list = null;
			Set<OWLEntity> pivot_module_sig = null;
			Set<OWLEntity> d_sig = new HashSet<>();

			int k = 1;

			do {
				if (DefinerIntroducer.owldefiner_set.isEmpty()) {
					System.out.println("Forgetting Successful (D1)!");
					System.out.println("===================================================");
					manager.addAxioms(refined_onto, d_module.getAxioms());
					return refined_onto;
				}

				d_sig.clear();
				d_sig.addAll(DefinerIntroducer.owldefiner_set);

				for (OWLEntity owlclass : d_sig) {
					System.out.println("Forgetting Definer [" + k + "] = " + owlclass);
					k++;
					pivot_module_sig = new HashSet<>();
					pivot_module_sig.add(owlclass);
					pivot_module = sub_extractor_3.extractAsOntology(pivot_module_sig, IRI.generateDocumentIRI());
					// System.out.println("pivot_module size = " + pivot_module.getAxiomCount());
					manager.removeAxioms(d_module, pivot_module.getAxioms());
					pivot = ct.getConceptfromClass(owlclass);
					pivot_list = simp
							.getCNF(simp.getSimplifiedForm(simp.getClauses(ct.OntologyConverter(pivot_module))));
					// System.out.println("pivot_list size = " + pivot_list.size());
					exact_list = se.getConceptSubset(pivot, pivot_list);

					if (pivot_list.isEmpty()) {

					} else if (fc.negative(pivot, exact_list) == 0) {
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(pivot, exact_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);

					} else if (fc.positive(pivot, exact_list) == 0) {
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(pivot, pivot_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);

					} else if (rfc.isAReducedFormPositive(pivot, exact_list)) {
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.AckermannPositive(pivot, exact_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);

					} else if (rfc.isAReducedFormNegative(pivot, exact_list)) {
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.AckermannNegative(pivot, exact_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);

					} else {
						exact_list = simp.getCNF(simp.getSimplifiedForm(di.introduceDefiners(pivot, exact_list)));
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.combination_A(pivot, exact_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);
					}
				}

			} while (d_sig.size() > DefinerIntroducer.definer_set.size());

			do {
				if (DefinerIntroducer.owldefiner_set.isEmpty()) {
					System.out.println("Forgetting Successful (D2)!");
					System.out.println("===================================================");
					manager.addAxioms(refined_onto, d_module.getAxioms());
					return refined_onto;
				}

				d_sig.clear();
				d_sig.addAll(DefinerIntroducer.owldefiner_set);

				for (OWLEntity owlclass : d_sig) {
					System.out.println("Forgetting Definer [" + k + "] = " + owlclass);
					k++;
					pivot_module_sig = new HashSet<>();
					pivot_module_sig.add(owlclass);
					pivot_module = sub_extractor_3.extractAsOntology(pivot_module_sig, IRI.generateDocumentIRI());
					// System.out.println("pivot_module size = " + pivot_module.getAxiomCount());
					manager.removeAxioms(d_module, pivot_module.getAxioms());
					pivot = ct.getConceptfromClass(owlclass);
					pivot_list = simp
							.getCNF(simp.getSimplifiedForm(simp.getClauses(ct.OntologyConverter(pivot_module))));
					// System.out.println("pivot_list size = " + pivot_list.size());
					exact_list = se.getConceptSubset(pivot, pivot_list);

					if (pivot_list.isEmpty()) {

					} else if (fc.negative(pivot, exact_list) == 0) {
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(pivot, exact_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);

					} else if (fc.positive(pivot, exact_list) == 0) {
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(pivot, pivot_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);

					} else if (rfc.isAReducedFormPositive(pivot, exact_list)) {
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.AckermannPositive(pivot, exact_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);

					} else if (rfc.isAReducedFormNegative(pivot, exact_list)) {
						exact_list = simp.getCNF(simp.getSimplifiedForm(inf.AckermannNegative(pivot, exact_list)));
						pivot_list.addAll(exact_list);
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
						DefinerIntroducer.owldefiner_set.remove(owlclass);

					} else {			
						manager.addAxioms(d_module, bc.toOWLAxioms(bc.toAxioms(pivot_list)));
					}
				}

			} while (d_sig.size() > DefinerIntroducer.owldefiner_set.size());

		}*/
		//// this is the case of the cyclic cases, that's why the ACK_A is not re-used.
		// In case the results of contains this case. report
		System.out.println("Forgetting Unsuccessful!");
		manager.addAxioms(result, bc.toOWLAxioms(bc.toAxioms(clause_list_normalised)));
		return result;
	}
	public List<Formula> Forgetting(Set<AtomicConcept> c_sig, Set<AtomicRole> r_sig,
			List<Formula> clause_list_normalised) throws CloneNotSupportedException {

		System.out.println("The Forgetting Starts:");

		Simplifier simp = new Simplifier();
		SubsetExtractor se = new SubsetExtractor();
		DefinerIntroducer di = new DefinerIntroducer();
		Inferencer inf = new Inferencer();
		FChecker fc = new FChecker();
		RFChecker rfc = new RFChecker();

		if (!c_sig.isEmpty()) {
			List<Formula> c_sig_list_normalised = se.getConceptSubset(c_sig, clause_list_normalised);
			List<Formula> pivot_list_normalised = null;
			int j = 1;
			for (AtomicConcept concept : c_sig) {
				System.out.println("Forgetting Concept [" + j + "] = " + concept);
				j++;
				pivot_list_normalised = simp
						.getCNF(simp.getSimplifiedForm(se.getConceptSubset(concept, c_sig_list_normalised)));

				if (pivot_list_normalised.isEmpty()) {

				} else if (fc.negative(concept, pivot_list_normalised) == 0) {
					c_sig_list_normalised.addAll(
							simp.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(concept, pivot_list_normalised))));

				} else if (fc.positive(concept, pivot_list_normalised) == 0) {
					c_sig_list_normalised.addAll(
							simp.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(concept, pivot_list_normalised))));

				} else {
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(di.introduceDefiners(concept, pivot_list_normalised)));
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(inf.combination_A(concept, pivot_list_normalised)));
					c_sig_list_normalised.addAll(pivot_list_normalised);
				}
			}

			clause_list_normalised.addAll(c_sig_list_normalised);
		}

		/*
		 * if (!c_sig.isEmpty()) { List<Formula> c_sig_list_normalised =
		 * se.getConceptSubset(c_sig, formula_list_normalised); List<Formula>
		 * pivot_list_normalised = null; int j = 1; for (AtomicConcept concept : c_sig)
		 * { System.out.println("Forgetting Concept [" + j + "] = " + concept); j++;
		 * pivot_list_normalised = simp
		 * .getCNF(simp.getSimplifiedForm(se.getConceptSubset(concept,
		 * c_sig_list_normalised)));
		 * 
		 * if (pivot_list_normalised.isEmpty()) {
		 * 
		 * } else if (fc.negative(concept, pivot_list_normalised) == 0) {
		 * c_sig_list_normalised.addAll(
		 * simp.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(concept,
		 * pivot_list_normalised))));
		 * 
		 * } else if (fc.positive(concept, pivot_list_normalised) == 0) {
		 * c_sig_list_normalised.addAll(
		 * simp.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(concept,
		 * pivot_list_normalised))));
		 * 
		 * } else if (rfc.isAReducedFormPositive(concept, pivot_list_normalised)) {
		 * c_sig_list_normalised.addAll(
		 * simp.getCNF(simp.getSimplifiedForm(inf.AckermannPositive(concept,
		 * pivot_list_normalised))));
		 * 
		 * } else if (rfc.isAReducedFormNegative(concept, pivot_list_normalised)) {
		 * c_sig_list_normalised.addAll(
		 * simp.getCNF(simp.getSimplifiedForm(inf.AckermannNegative(concept,
		 * pivot_list_normalised))));
		 * 
		 * } else { pivot_list_normalised = simp
		 * .getCNF(simp.getSimplifiedForm(inf.introduceDefiners(concept,
		 * pivot_list_normalised)));
		 * 
		 * pivot_list_normalised = simp
		 * .getCNF(simp.getSimplifiedForm(inf.Ackermann_A(concept,
		 * pivot_list_normalised)));
		 * c_sig_list_normalised.addAll(pivot_list_normalised); } }
		 * 
		 * formula_list_normalised.addAll(c_sig_list_normalised); }
		 */

		if (!r_sig.isEmpty()) {
			List<Formula> r_sig_list_normalised = se.getRoleSubset(r_sig, clause_list_normalised);
			List<Formula> pivot_list_normalised = null;
			int i = 1;
			for (AtomicRole role : r_sig) {
				System.out.println("Forgetting Role [" + i + "] = " + role);
				i++;
				pivot_list_normalised = simp
						.getCNF(simp.getSimplifiedForm(se.getRoleSubset(role, r_sig_list_normalised)));
				if (pivot_list_normalised.isEmpty()) {

				} else {
					pivot_list_normalised = di.introduceDefiners(role, pivot_list_normalised);
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(inf.Ackermann_R(role, pivot_list_normalised)));
					r_sig_list_normalised.addAll(pivot_list_normalised);
				}
			}

			clause_list_normalised.addAll(r_sig_list_normalised);
		}

		if (!di.definer_set.isEmpty()) {
			List<Formula> d_sig_list_normalised = se.getConceptSubset(di.definer_set,
					clause_list_normalised);
			List<Formula> pivot_list_normalised = null;
			Set<AtomicConcept> definer_set = null;

			int k = 1;
			do {
				// System.out.println("d_sig_list_normalised = " + d_sig_list_normalised);
				if (di.definer_set.isEmpty()) {
					System.out.println("Forgetting Successful (D1)!");
					System.out.println("===================================================");
					clause_list_normalised.addAll(d_sig_list_normalised);
					return clause_list_normalised;
				}

				definer_set = new HashSet<>(di.definer_set);

				for (AtomicConcept concept : definer_set) {
					System.out.println("Forgetting Definer [" + k + "] = " + concept);
					k++;
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(se.getConceptSubset(concept, d_sig_list_normalised)));
					if (pivot_list_normalised.isEmpty()) {

					} else if (fc.negative(concept, pivot_list_normalised) == 0) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(concept, pivot_list_normalised))));
						di.definer_set.remove(concept);

					} else if (fc.positive(concept, pivot_list_normalised) == 0) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(concept, pivot_list_normalised))));
						di.definer_set.remove(concept);

					} /*
						 * else if (rfc.isAReducedFormPositive(concept, pivot_list_normalised)) {
						 * d_sig_list_normalised.addAll(simp.getCNF(
						 * simp.getSimplifiedForm(inf.AckermannPositive(concept,
						 * pivot_list_normalised)))); Inferencer.definer_set.remove(concept);
						 * 
						 * } else if (rfc.isAReducedFormNegative(concept, pivot_list_normalised)) {
						 * d_sig_list_normalised.addAll(simp.getCNF(
						 * simp.getSimplifiedForm(inf.AckermannNegative(concept,
						 * pivot_list_normalised)))); Inferencer.definer_set.remove(concept);
						 * 
						 * }
						 */ else {
						pivot_list_normalised = di.introduceDefiners(concept, pivot_list_normalised);
						pivot_list_normalised = simp
								.getCNF(simp.getSimplifiedForm(inf.combination_A(concept, pivot_list_normalised)));
						d_sig_list_normalised.addAll(pivot_list_normalised);
						di.definer_set.remove(concept);

					}
				}

			} while (definer_set.size() > di.definer_set.size());
			//// this is the case of the cyclic cases, that's why the ACK_A is not re-used.
			// In case the results of contains this case. report!
			do {
				if (di.definer_set.isEmpty()) {
					System.out.println("Forgetting Successful (D2)!");
					System.out.println("===================================================");
					clause_list_normalised.addAll(d_sig_list_normalised);
					return clause_list_normalised;
				}

				System.out.println("The formula might contain cylic case: " + d_sig_list_normalised);

				definer_set = new HashSet<>(di.definer_set);

				for (AtomicConcept concept : definer_set) {
					System.out.println("Forgetting Definer [" + k + "] = " + concept);
					k++;
					pivot_list_normalised = simp
							.getCNF(simp.getSimplifiedForm(se.getConceptSubset(concept, d_sig_list_normalised)));
					if (pivot_list_normalised.isEmpty()) {
						di.definer_set.remove(concept);

					} else if (fc.negative(concept, pivot_list_normalised) == 0) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.PurifyPositive(concept, pivot_list_normalised))));
						di.definer_set.remove(concept);

					} else if (fc.positive(concept, pivot_list_normalised) == 0) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.PurifyNegative(concept, pivot_list_normalised))));
						di.definer_set.remove(concept);

					} else if (rfc.isAReducedFormPositive(concept, pivot_list_normalised)) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.AckermannPositive(concept, pivot_list_normalised))));
						di.definer_set.remove(concept);

					} else if (rfc.isAReducedFormNegative(concept, pivot_list_normalised)) {
						d_sig_list_normalised.addAll(simp
								.getCNF(simp.getSimplifiedForm(inf.AckermannNegative(concept, pivot_list_normalised))));
						di.definer_set.remove(concept);

					} else {
						d_sig_list_normalised.addAll(pivot_list_normalised);
					}
				}

			} while (definer_set.size() > di.definer_set.size());

		}

		System.out.println("Forgetting Successful!");

		return clause_list_normalised;
	}

}
