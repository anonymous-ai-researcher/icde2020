package swing;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.File;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import javax.swing.JList;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.io.IRIDocumentSource;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyLoaderConfiguration;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import concepts.AtomicConcept;
import forgetting.Forgetter;
import roles.AtomicRole;

public class ForgetButtonListener implements ActionListener {
	
	private JList<AtomicRole> Jrole_list;
	private JList<AtomicConcept> Jconcept_list;
	// private JList<Formula> Jformula_list;
	private JList<OWLLogicalAxiom> Jresult_list;

	@SuppressWarnings("unchecked")
	public ForgetButtonListener() {
		Jrole_list = (JList<AtomicRole>) Register.getInstance().getObject("role_list");
		Jconcept_list = (JList<AtomicConcept>) Register.getInstance().getObject("concept_list");
		// Jformula_list = (JList<Formula>) R.getInstance().getObject("formula_list");
		Jresult_list = (JList<OWLLogicalAxiom>) Register.getInstance().getObject("result_list");
	}

	@SuppressWarnings({ "rawtypes", "unchecked" })
	public void actionPerformed(ActionEvent arg0) {
		
		int indices_1[] = Jrole_list.getSelectedIndices();

		int indices_2[] = Jconcept_list.getSelectedIndices();
		
		SentenceListModel role_model = (SentenceListModel) Jrole_list.getModel();

		SentenceListModel concept_model = (SentenceListModel) Jconcept_list.getModel();

		List<OWLObjectProperty> role_list = role_model.getListData();
		
		List<OWLClass> concept_list = concept_model.getListData();

		// SentenceListModel formula_model = (SentenceListModel)
		// Jformula_list.getModel();

		// List<Formula> formula_list = formula_model.getListData();

		SentenceListModel result_model = (SentenceListModel) Jresult_list.getModel();

		List<OWLLogicalAxiom> result_list = result_model.getListData();
		
		Set<OWLClass> c_sig = new HashSet<>();

		int i = indices_2.length;

		while (i-- > 0) {
			c_sig.add(concept_list.get(indices_2[i]));
		}

		Set<OWLObjectProperty> r_sig = new HashSet<>();

		int j = indices_1.length;

		while (j-- > 0) {
			r_sig.add(role_list.get(indices_1[j]));
		}

		Forgetter fame = new Forgetter();

		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();

		IRI iri = IRI.create(new File(LoadButtonListener.ontologyPath));

		OWLOntology ontology = null;
		//Set<OWLLogicalAxiom> formula_list = null;

		//Converter ct = new Converter();

		try {
			long startTime = System.currentTimeMillis();
			ontology = manager.loadOntologyFromOntologyDocument(new IRIDocumentSource(iri),
					new OWLOntologyLoaderConfiguration().setLoadAnnotationAxioms(true));
//			formula_list = ct.OntologyConverter_ShortForm(ontology);
//			formula_list = ontology.getLogicalAxioms();
			OWLOntology res_ontology = fame.Forgetting(c_sig, r_sig, ontology);
			result_list = new ArrayList<>(res_ontology.getLogicalAxioms());
//			result_list = fame.FameCR(c_sig, r_sig, formula_list);
			long endTime = System.currentTimeMillis();
			System.out.println("Duration = " + (endTime - startTime) + "millis");
		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

		result_model.setListData(result_list);
	}

}
