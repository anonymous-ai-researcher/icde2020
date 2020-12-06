package forgetting;

import formula.Formula;
import roles.AtomicRole;
import simplification.Simplifier;
import concepts.AtomicConcept;
import convertion.BackConverter;
import convertion.Converter;

import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.IRIDocumentSource;
import org.semanticweb.owlapi.io.OWLXMLOntologyFormat;
import org.semanticweb.owlapi.model.AddAxiom;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyLoaderConfiguration;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLOntologyStorageException;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

import com.google.common.collect.Sets;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.OutputStream;
import java.util.HashSet;
import java.util.List;
import java.util.Scanner;
import java.util.Set;

/**
 *
 * @author Yizheng
 */
public class LDiff {

	public static OWLOntologyManager manager = OWLManager.createOWLOntologyManager();

	public void compute_LDiff(OWLOntology onto_1, OWLOntology onto_2, String path)
			throws OWLOntologyCreationException, CloneNotSupportedException {
		
		Converter ct = new Converter();
		BackConverter bc = new BackConverter();
		Simplifier pp = new Simplifier();
		Forgetter forget = new Forgetter();

		Set<OWLClass> c_sig_1 = onto_1.getClassesInSignature();
		Set<OWLClass> c_sig_2 = onto_2.getClassesInSignature();
		Set<AtomicConcept> concept_set_1 = ct.getConceptsfromClasses_ShortForm(c_sig_1);
		Set<AtomicConcept> concept_set_2 = ct.getConceptsfromClasses_ShortForm(c_sig_2);
		//Set<OWLClass> c_sig = new HashSet<>(Sets.difference(c_sig_1, c_sig_2));
		Set<OWLObjectProperty> r_sig_1 = onto_1.getObjectPropertiesInSignature();
		Set<OWLObjectProperty> r_sig_2 = onto_2.getObjectPropertiesInSignature();
		Set<AtomicRole> role_set_1 = ct.getRolesfromObjectProperties_ShortForm(r_sig_1);
		Set<AtomicRole> role_set_2 = ct.getRolesfromObjectProperties_ShortForm(r_sig_2);
		//Set<OWLObjectProperty> r_sig = new HashSet<>(Sets.difference(r_sig_1, r_sig_2));

		Set<AtomicRole> role_set = new HashSet<>(Sets.difference(role_set_1, role_set_2));
		Set<AtomicConcept> concept_set = new HashSet<>(Sets.difference(concept_set_1, concept_set_2));
		List<Formula> formula_list = pp.getCNF(pp.getSimplifiedForm(pp.getClauses(ct.OntologyConverter_ShortForm(onto_1))));

		System.out.println("The forgetting task is to eliminate [" + concept_set.size() + "] concept names and ["
				+ role_set.size() + "] role names from [" + formula_list.size() + "] normalized axioms");

		Set<OWLAxiom> axiomset_normalised = bc.toOWLAxioms(bc.toAxioms(formula_list));

		long startTime_1 = System.currentTimeMillis();
		Set<OWLAxiom> uniform_interpolant = bc.toOWLAxioms(
				bc.toAxioms(pp.getCNF(pp.getSimplifiedForm(forget.Forgetting(role_set, concept_set, formula_list)))));
		System.out.println("ui size = " + uniform_interpolant.size());
		long endTime_1 = System.currentTimeMillis();
		System.out.println("Forgetting Duration = " + (endTime_1 - startTime_1) + " millis");

		OWLOntology witness_complete_onto = manager.createOntology();
		OWLOntology witness_explicit_onto = manager.createOntology();
		OWLOntology witness_implicit_onto = manager.createOntology();

		// Set<OWLAxiom> axiom_set_2 = onto_2.getAxioms();
		// Set<OWLAxiom> axiom_set_2_normalised =
		// bc.toOWLAxioms(bc.toAxioms(pp.getCNF(pp.getSimplifiedForm(pp.getClauses(ct.AxiomsConverter(axiom_set_2))))));
		// OWLOntology onto_2_normalised =
		// manager.createOntology(axiom_set_2_normalised, IRI.generateDocumentIRI());
		OWLReasoner reasoner = new Reasoner.ReasonerFactory().createReasoner(onto_2);
		long startTime_2 = System.currentTimeMillis();
		for (OWLAxiom axiom : uniform_interpolant) {
			if (!reasoner.isEntailed(axiom)) {
				manager.applyChange(new AddAxiom(witness_complete_onto, axiom));
				System.out.println("witness_complete = " + axiom);
				if (axiomset_normalised.contains(axiom)) {
					manager.applyChange(new AddAxiom(witness_explicit_onto, axiom));
					System.out.println("witness_explicit = " + axiom);
				} else {
					manager.applyChange(new AddAxiom(witness_implicit_onto, axiom));
					System.out.println("witness_implicit = " + axiom);
				}
			}
		}
		long endTime_2 = System.currentTimeMillis();
		System.out.println("Entailment Duration = " + (endTime_2 - startTime_2) + " millis");
		reasoner.dispose();

		// Add rdf labels
		/*
		 * WLOntology witness_complete_onto_annotated = manager.createOntology();
		 * OWLOntology witness_explicit_onto_annotated = manager.createOntology();
		 * OWLOntology witness_implicit_onto_annotated = manager.createOntology();
		 * 
		 * OWLDataFactory factory = manager.getOWLDataFactory();
		 * 
		 * for (OWLEntity entity : witness_complete_onto.getSignature()) {
		 * Set<OWLAnnotation> annotations = entity.getAnnotations(onto_1); for
		 * (OWLAnnotation annotation : annotations) { OWLAxiom axiom =
		 * factory.getOWLAnnotationAssertionAxiom(entity.getIRI(), annotation);
		 * //System.out.println("witness_complete_annotated = " + axiom);
		 * manager.applyChange(new AddAxiom(witness_complete_onto_annotated, axiom)); }
		 * }
		 * 
		 * for (OWLEntity entity : witness_explicit_onto.getSignature()) {
		 * Set<OWLAnnotation> annotations = entity.getAnnotations(onto_1); for
		 * (OWLAnnotation annotation : annotations) { OWLAxiom axiom =
		 * factory.getOWLAnnotationAssertionAxiom(entity.getIRI(), annotation);
		 * //System.out.println("witness_explicit_annotated = " + axiom);
		 * manager.applyChange(new AddAxiom(witness_explicit_onto_annotated, axiom)); }
		 * }
		 * 
		 * for (OWLEntity entity : witness_implicit_onto.getSignature()) {
		 * Set<OWLAnnotation> annotations = entity.getAnnotations(onto_1); for
		 * (OWLAnnotation annotation : annotations) { OWLAxiom axiom =
		 * factory.getOWLAnnotationAssertionAxiom(entity.getIRI(), annotation);
		 * //System.out.println("witness_implicit_annotated = " + axiom);
		 * manager.applyChange(new AddAxiom(witness_implicit_onto_annotated, axiom)); }
		 * }
		 */

		OutputStream os_complete;
		OutputStream os_explicit;
		OutputStream os_implicit;

		try {
			os_complete = new FileOutputStream(new File(path + "\\witness_complete.owl"));
			manager.saveOntology(witness_complete_onto, new OWLXMLOntologyFormat(), os_complete);
			os_explicit = new FileOutputStream(new File(path + "\\witness_explicit.owl"));
			manager.saveOntology(witness_explicit_onto, new OWLXMLOntologyFormat(), os_explicit);
			os_implicit = new FileOutputStream(new File(path + "\\witness_implicit.owl"));
			manager.saveOntology(witness_implicit_onto, new OWLXMLOntologyFormat(), os_implicit);
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (OWLOntologyStorageException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	/*
	public static void main(String[] args)
			throws OWLOntologyCreationException, CloneNotSupportedException, OWLOntologyStorageException, IOException {

		OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();

		Scanner sc1 = new Scanner(System.in);
		System.out.println("Onto_1 Path: ");
		String filePath1 = sc1.next();
		IRI iri1 = IRI.create(filePath1);
		OWLOntology onto_1 = manager1.loadOntologyFromOntologyDocument(new IRIDocumentSource(iri1),
				new OWLOntologyLoaderConfiguration().setLoadAnnotationAxioms(false));
		System.out.println("onto_1 size = " + onto_1.getLogicalAxiomCount());
		System.out.println("c_sig_1 size = " + onto_1.getClassesInSignature().size());
		System.out.println("r_sig_1 size = " + onto_1.getObjectPropertiesInSignature().size());

		OWLOntologyManager manager2 = OWLManager.createOWLOntologyManager();

		Scanner sc2 = new Scanner(System.in);
		System.out.println("Onto_2 Path: ");
		String filePath2 = sc2.next();
		IRI iri2 = IRI.create(filePath2);
		OWLOntology onto_2 = manager2.loadOntologyFromOntologyDocument(new IRIDocumentSource(iri2),
				new OWLOntologyLoaderConfiguration().setLoadAnnotationAxioms(false));
		System.out.println("onto_2 size = " + onto_2.getLogicalAxiomCount());
		System.out.println("c_sig_2 size = " + onto_2.getClassesInSignature().size());
		System.out.println("r_sig_2 size = " + onto_2.getObjectPropertiesInSignature().size());
		
		Converter ct = new Converter();
		BackConverter bc = new BackConverter();
		PreProcessor pp = new PreProcessor();
		
		Set<Formula> formula_set_1 = bc.toAxioms(pp.getCNF(pp.getSimplifiedForm(pp.getClauses(ct.OntologyConverter_ShortForm(onto_1)))));
		Set<Formula> formula_set_2 = bc.toAxioms(pp.getCNF(pp.getSimplifiedForm(pp.getClauses(ct.OntologyConverter_ShortForm(onto_2)))));
		
		Set<Formula> formula_list_12 = Sets.difference(formula_set_1, formula_set_2);
		
			
		//Set<OWLLogicalAxiom> axiomset_2_1 = Sets.difference(onto_2.getLogicalAxioms(), onto_1.getLogicalAxioms());

		int i = 0;
		for (Formula formula : formula_list_12) {
			i++;
			System.out.println("formula diff [" + i + "] = " + formula);
		}
		
		sc1.close();
		sc2.close();
	}*/

	public static void main(String[] args)
			throws OWLOntologyCreationException, CloneNotSupportedException, OWLOntologyStorageException, IOException {

		OWLOntologyManager manager1 = OWLManager.createOWLOntologyManager();

		Scanner sc1 = new Scanner(System.in);
		System.out.println("Onto_1 Path: ");
		String filePath1 = sc1.next();
		IRI iri1 = IRI.create(filePath1);
		OWLOntology onto_1 = manager1.loadOntologyFromOntologyDocument(new IRIDocumentSource(iri1),
				new OWLOntologyLoaderConfiguration().setLoadAnnotationAxioms(false));
		System.out.println("onto_1 size = " + onto_1.getLogicalAxiomCount());
		System.out.println("c_sig_1 size = " + onto_1.getClassesInSignature().size());
		System.out.println("r_sig_1 size = " + onto_1.getObjectPropertiesInSignature().size());

		OWLOntologyManager manager2 = OWLManager.createOWLOntologyManager();

		Scanner sc2 = new Scanner(System.in);
		System.out.println("Onto_2 Path: ");
		String filePath2 = sc2.next();
		IRI iri2 = IRI.create(filePath2);
		OWLOntology onto_2 = manager2.loadOntologyFromOntologyDocument(new IRIDocumentSource(iri2),
				new OWLOntologyLoaderConfiguration().setLoadAnnotationAxioms(false));
		System.out.println("onto_2 size = " + onto_2.getLogicalAxiomCount());
		System.out.println("c_sig_2 size = " + onto_2.getClassesInSignature().size());
		System.out.println("r_sig_2 size = " + onto_2.getObjectPropertiesInSignature().size());

		Scanner sc3 = new Scanner(System.in);
		System.out.println("Save Path: ");
		String filePath3 = sc3.next();

		long startTime1 = System.currentTimeMillis();
		LDiff diff = new LDiff();
		diff.compute_LDiff(onto_1, onto_2, filePath3);
		long endTime1 = System.currentTimeMillis();

		System.out.println("Total Duration = " + (endTime1 - startTime1) + "millis");

		sc1.close();
		sc2.close();
		sc3.close();
	}

}
