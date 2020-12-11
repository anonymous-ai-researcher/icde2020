package forgetting;


import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.IRIDocumentSource;
import org.semanticweb.owlapi.io.OWLXMLOntologyFormat;
import org.semanticweb.owlapi.model.AddAxiom;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
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
import java.util.Scanner;
import java.util.Set;

/**
 *
 * @author Yizheng
 */
public class LDiff {

	//public static OWLOntologyManager manager = OWLManager.createOWLOntologyManager();

	public void compute_diff(OWLOntology onto_1, OWLOntology onto_2, String path)
			throws OWLOntologyCreationException, CloneNotSupportedException {
		
		//concept names to be forgotten
		Set<OWLClass> c_sig_1 = onto_1.getClassesInSignature();
		Set<OWLClass> c_sig_2 = onto_2.getClassesInSignature();
		Set<OWLClass> c_sig = Sets.difference(c_sig_2, c_sig_1);
		
		//role names to be forgotten
		Set<OWLObjectProperty> r_sig_1 = onto_1.getObjectPropertiesInSignature();
		Set<OWLObjectProperty> r_sig_2 = onto_2.getObjectPropertiesInSignature();
		Set<OWLObjectProperty> r_sig = Sets.difference(r_sig_2, r_sig_1);
		
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		//SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager, onto_2, ModuleType.BOT);
		//Set<OWLEntity> f_sig = Sets.union(c_sig, r_sig);
		//System.out.println("f_sig = " + f_sig.size());
		//OWLOntology f_module = extractor.extractAsOntology(f_sig, IRI.generateDocumentIRI());
		Set<OWLAxiom> onto_2_axioms = new HashSet<>(onto_2.getAxioms());
		//manager.removeAxioms(onto_2, f_module.getAxioms());

		//System.out.println("The forgetting task is to eliminate [" + c_sig.size() + "] concept names and ["
		//		+ r_sig.size() + "] role names from [" + f_module.getAxiomCount() + "] logical axioms");

		//file:///C:/Users/zhaoy/Desktop/snomed_ct/snomed_ct_intl_20170731.owl
		//file:///C:/Users/zhaoy/Desktop/snomed_ct/snomed_ct_australian.owl


		long startTime_1 = System.currentTimeMillis();
		Forgetter forgetter = new Forgetter();
		OWLOntology uniform_interpolant = forgetter.Forgetting(c_sig, r_sig, onto_2);
		System.out.println("Uniform Interpolant Size = " + uniform_interpolant.getAxiomCount());
		long endTime_1 = System.currentTimeMillis();
		System.out.println("Forgetting Duration = " + (endTime_1 - startTime_1) + " millis");

		OWLOntology witness_complete_onto = manager.createOntology(IRI.generateDocumentIRI());
		OWLOntology witness_explicit_onto = manager.createOntology(IRI.generateDocumentIRI());
		OWLOntology witness_implicit_onto = manager.createOntology(IRI.generateDocumentIRI());

		// Set<OWLAxiom> axiom_set_2 = onto_2.getAxioms();
		// Set<OWLAxiom> axiom_set_2_normalised =
		// bc.toOWLAxioms(bc.toAxioms(pp.getCNF(pp.getSimplifiedForm(pp.getClauses(ct.AxiomsConverter(axiom_set_2))))));
		// OWLOntology onto_2_normalised =
		// manager.createOntology(axiom_set_2_normalised, IRI.generateDocumentIRI());
		OWLReasoner reasoner = new Reasoner.ReasonerFactory().createReasoner(onto_1);
		long startTime_2 = System.currentTimeMillis();
		Set<OWLLogicalAxiom> ui_axioms = uniform_interpolant.getLogicalAxioms();
		for (OWLAxiom axiom : ui_axioms) {
			if (!reasoner.isEntailed(axiom)) {
				manager.applyChange(new AddAxiom(witness_complete_onto, axiom));
				System.out.println("witness_complete = " + axiom);
				if (onto_2_axioms.contains(axiom)) {
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
		diff.compute_diff(onto_1, onto_2, filePath3);
		long endTime1 = System.currentTimeMillis();

		System.out.println("Total Duration = " + (endTime1 - startTime1) + "millis");

		sc1.close();
		sc2.close();
		sc3.close();
	}

}
