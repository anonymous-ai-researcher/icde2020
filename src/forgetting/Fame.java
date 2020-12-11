package forgetting;

import formula.Formula;
import roles.AtomicRole;
import simplification.Simplifier;
import uk.ac.manchester.cs.owlapi.modularity.ModuleType;
import uk.ac.manchester.cs.owlapi.modularity.SyntacticLocalityModuleExtractor;
import concepts.AtomicConcept;
import convertion.BackConverter;
import convertion.Converter;

import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import com.google.common.collect.Sets;

import java.util.List;
import java.util.Set;


/**
 *
 * @author Yizheng
 */
public class Fame {

	public static OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
	
	public Fame() {

	}
	
	public OWLOntology FameCR(Set<OWLClass> c_set, Set<OWLObjectProperty> op_set, OWLOntology onto)
			throws OWLOntologyCreationException, CloneNotSupportedException {
		
		if (op_set.isEmpty() && c_set.isEmpty()) {
			return onto;
		}
		
		
		Converter ct = new Converter();
		Simplifier sp = new Simplifier();
		
		//List<Formula> filtered_list = ct.OntologyConverter(onto);
		
		
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
		SyntacticLocalityModuleExtractor extractor = new SyntacticLocalityModuleExtractor(manager, onto, ModuleType.BOT);
		Set<OWLEntity> f_sig = Sets.union(c_set, op_set);
		Set<OWLAxiom> f_module = extractor.extract(f_sig);
		manager.removeAxioms(onto, f_module);	
		
		Set<AtomicConcept> c_sig = ct.getConceptsfromClasses(c_set);
		Set<AtomicRole> r_sig = ct.getRolesfromObjectProperties(op_set);
		List<Formula> clause_list = sp.getCNF(sp.getSimplifiedForm(sp.getClauses(ct.AxiomsConverter(f_module))));
		
		//System.out.println("formula_list = " + formula_list.get(0));
		
		Forgetter ft = new Forgetter();
		List<Formula> forgetting_solution = ft.Forgetting(c_sig, r_sig, clause_list);
		
		BackConverter bc = new BackConverter();
		OWLOntology view = bc.toOWLOntology(forgetting_solution);
				
		return view;
	}
		
	public List<Formula> FameCR(Set<AtomicConcept> c_sig, Set<AtomicRole> r_sig, List<Formula> formula_list) throws OWLOntologyCreationException, CloneNotSupportedException {

		if (r_sig.isEmpty() && c_sig.isEmpty()) {
			return formula_list;
		}
		
		Simplifier pp = new Simplifier();
		List<Formula> clause_list = pp.getCNF(pp.getSimplifiedForm(pp.getClauses(formula_list)));
		
		//System.out.println("formula_list = " + formula_list.get(0));
		
		Forgetter ft = new Forgetter(); 
		BackConverter bc = new BackConverter();
		List<Formula> forgetting_solution = bc.toAxiomsList(ft.Forgetting(c_sig, r_sig, clause_list));
		
	
		return forgetting_solution;
	}
	


	
}