/*
1 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package converter;

import concepts.AtomicConcept;
import concepts.BottomConcept;
import concepts.TopConcept;
import connectives.And;
import connectives.Exists;
import connectives.Forall;
import connectives.Inclusion;
import connectives.Negation;
import connectives.Or;
import formula.Formula;
import individual.Individual;
import roles.AtomicRole;
import roles.BottomRole;
import roles.RoleExpression;
import roles.TopRole;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLObjectAllValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectIntersectionOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyExpression;
import org.semanticweb.owlapi.model.OWLObjectSomeValuesFrom;
import org.semanticweb.owlapi.model.OWLObjectUnionOf;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLLogicalAxiom;

/**
 *
 * @author Yizheng
 */
public class Converter {
		
	public AtomicConcept getConceptfromClass(OWLClass owlClass) {
		return new AtomicConcept(owlClass.getIRI().toString());
	}
	
	public AtomicRole getRoleFromObjectProperty(OWLObjectProperty owlObjectProperty) {		
		return new AtomicRole(owlObjectProperty.getIRI().toString());
	}
	
	public Individual getIndividualFromNamedIndividual(OWLNamedIndividual owlNamedIndividual) {		
		return new Individual(owlNamedIndividual.getIRI().toString());
	}
	
	public AtomicConcept getConceptfromClass_ShortForm(OWLClass owlClass) {
		return new AtomicConcept(owlClass.getIRI().getShortForm());
	}
	
	public AtomicRole getRoleFromObjectProperty_ShortForm(OWLObjectProperty owlObjectProperty) {		
		return new AtomicRole(owlObjectProperty.getIRI().getShortForm());
	}
	
	public Individual getIndividualFromNamedIndividual_ShortForm(OWLNamedIndividual owlNamedIndividual) {		
		return new Individual(owlNamedIndividual.getIRI().getShortForm());
	}
	
	public Set<AtomicConcept> getConceptsfromClasses(Set<OWLClass> class_set) {

		Set<AtomicConcept> concept_set = new HashSet<>();

		for (OWLClass owlClass : class_set) {
			concept_set.add(getConceptfromClass(owlClass));
		}

		return concept_set;
	}
		
	public Set<AtomicRole> getRolesfromObjectProperties(Set<OWLObjectProperty> op_set) {

		Set<AtomicRole> role_set = new HashSet<>();

		for (OWLObjectProperty owlObjectProperty : op_set) {
			role_set.add(getRoleFromObjectProperty(owlObjectProperty));
		}

		return role_set;
	}
	
	public Set<Individual> getIndividualsfromNamedIndividuals(Set<OWLNamedIndividual> ni_set) {

		Set<Individual> indi_set = new HashSet<>();

		for (OWLNamedIndividual owlNamedIndividual : ni_set) {
			indi_set.add(getIndividualFromNamedIndividual(owlNamedIndividual));
		}

		return indi_set;
	}
	
	public Set<AtomicConcept> getConceptsfromClasses_ShortForm(Set<OWLClass> class_set) {

		Set<AtomicConcept> concept_set = new HashSet<>();

		for (OWLClass owlClass : class_set) {
			concept_set.add(getConceptfromClass_ShortForm(owlClass));
		}

		return concept_set;
	}
		
	public Set<AtomicRole> getRolesfromObjectProperties_ShortForm(Set<OWLObjectProperty> op_set) {

		Set<AtomicRole> role_set = new HashSet<>();

		for (OWLObjectProperty owlObjectProperty : op_set) {
			role_set.add(getRoleFromObjectProperty_ShortForm(owlObjectProperty));
		}

		return role_set;
	}
	
	public Set<Individual> getIndividualsfromNamedIndividuals_ShortForm(Set<OWLNamedIndividual> ni_set) {

		Set<Individual> indi_set = new HashSet<>();

		for (OWLNamedIndividual owlNamedIndividual : ni_set) {
			indi_set.add(getIndividualFromNamedIndividual_ShortForm(owlNamedIndividual));
		}

		return indi_set;
	}
				
	public List<AtomicConcept> getConceptsInSignature(OWLOntology ontology) {

		List<AtomicConcept> concept_list = new ArrayList<>();
		Set<OWLClass> class_set = ontology.getClassesInSignature();

		for (OWLClass owlClass : class_set) {
			concept_list.add(getConceptfromClass(owlClass));
		}

		return concept_list;
	}
	
	public List<AtomicRole> getRolesInSignature(OWLOntology ontology) {

		List<AtomicRole> role_list = new ArrayList<>();
		Set<OWLObjectProperty> op_set = ontology.getObjectPropertiesInSignature();

		for (OWLObjectProperty owlObjectProperty : op_set) {
			role_list.add(getRoleFromObjectProperty(owlObjectProperty));
		}

		return role_list;
	}
	
	public List<Individual> getIndividualsInSignature(OWLOntology ontology) {

		List<Individual> indi_list = new ArrayList<>();
		Set<OWLNamedIndividual> individual_set = ontology.getIndividualsInSignature();

		for (OWLNamedIndividual owlIndividual : individual_set) {
			indi_list.add(getIndividualFromNamedIndividual(owlIndividual));
		}

		return indi_list;
	}
	
	public List<AtomicConcept> getConceptsInSignature_ShortForm(OWLOntology ontology) {

		List<AtomicConcept> concept_list = new ArrayList<>();
		Set<OWLClass> class_set = ontology.getClassesInSignature();

		for (OWLClass owlClass : class_set) {
			concept_list.add(getConceptfromClass_ShortForm(owlClass));
		}

		return concept_list;
	}
	
	public List<AtomicRole> getRolesInSignature_ShortForm(OWLOntology ontology) {

		List<AtomicRole> role_list = new ArrayList<>();
		Set<OWLObjectProperty> op_set = ontology.getObjectPropertiesInSignature();

		for (OWLObjectProperty owlObjectProperty : op_set) {
			role_list.add(getRoleFromObjectProperty_ShortForm(owlObjectProperty));
		}

		return role_list;
	}
	
	public List<Individual> getIndividualsInSignature_ShortForm(OWLOntology ontology) {

		List<Individual> indi_list = new ArrayList<>();
		Set<OWLNamedIndividual> individual_set = ontology.getIndividualsInSignature();

		for (OWLNamedIndividual owlIndividual : individual_set) {
			indi_list.add(getIndividualFromNamedIndividual_ShortForm(owlIndividual));
		}

		return indi_list;
	}

	public List<Formula> OntologyConverter(OWLOntology ontology) {

		List<Formula> formula_list = new ArrayList<>();		
		Set<OWLLogicalAxiom> owlAxiom_set = ontology.getLogicalAxioms();

		for (OWLAxiom owlAxiom : owlAxiom_set) {
			formula_list.addAll(AxiomConverter(owlAxiom));
		}

		return formula_list;
	}
	
	public List<Formula> OntologyConverter_ShortForm(OWLOntology ontology) {

		List<Formula> formula_list = new ArrayList<>();		
		Set<OWLLogicalAxiom> owlAxiom_set = ontology.getLogicalAxioms();

		for (OWLAxiom owlAxiom : owlAxiom_set) {
			formula_list.addAll(AxiomConverter_ShortForm(owlAxiom));
		}

		return formula_list;
	}
	
	public List<Formula> AxiomsConverter(Set<OWLAxiom> owlAxiom_set) {

		List<Formula> formula_list = new ArrayList<>();

		for (OWLAxiom owlAxiom : owlAxiom_set) {
			formula_list.addAll(AxiomConverter(owlAxiom));
		}

		return formula_list;
	}
	
	public List<Formula> AxiomsConverter_ShortForm(Set<OWLAxiom> owlAxiom_set) {

		List<Formula> formula_list = new ArrayList<>();

		for (OWLAxiom owlAxiom : owlAxiom_set) {
			formula_list.addAll(AxiomConverter_ShortForm(owlAxiom));
		}

		return formula_list;
	}
		
	public List<Formula> AxiomConverter(OWLAxiom axiom) {

		if (axiom instanceof OWLSubClassOfAxiom) {
			OWLSubClassOfAxiom owlSCOA = (OWLSubClassOfAxiom) axiom;
			Formula converted = new Inclusion(ClassExpressionConverter(owlSCOA.getSubClass()),
					ClassExpressionConverter(owlSCOA.getSuperClass()));
			return Collections.singletonList(converted);

		} else if (axiom instanceof OWLEquivalentClassesAxiom) {
			OWLEquivalentClassesAxiom owlECA = (OWLEquivalentClassesAxiom) axiom;
			Set<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlECA.asOWLSubClassOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
				converted.addAll(AxiomConverter(owlSCOA));
			}
			return converted;

		} else if (axiom instanceof OWLDisjointClassesAxiom) {
			OWLDisjointClassesAxiom owlDCA = (OWLDisjointClassesAxiom) axiom;
			Set<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlDCA.asOWLSubClassOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
				converted.addAll(AxiomConverter(owlSCOA));
			}
			return converted;

		} 
		
	 /*
		else if (axiom instanceof OWLDisjointUnionAxiom) {
			OWLDisjointUnionAxiom owlDUA = (OWLDisjointUnionAxiom) axiom;
			OWLEquivalentClassesAxiom owlECA = owlDUA.getOWLEquivalentClassesAxiom();
			OWLDisjointClassesAxiom owlDCA = owlDUA.getOWLDisjointClassesAxiom();
			List<Formula> converted = new ArrayList<>();
			converted.addAll(AxiomConverter(owlECA));
			converted.addAll(AxiomConverter(owlDCA));
			return converted;

		} else if (axiom instanceof OWLObjectPropertyDomainAxiom) {
			OWLObjectPropertyDomainAxiom owlOPDA = (OWLObjectPropertyDomainAxiom) axiom;
			OWLSubClassOfAxiom owlSCOA = owlOPDA.asOWLSubClassOfAxiom();
			return AxiomConverter(owlSCOA);

		} else if (axiom instanceof OWLObjectPropertyRangeAxiom) {
			OWLObjectPropertyRangeAxiom owlOPRA = (OWLObjectPropertyRangeAxiom) axiom;
			OWLSubClassOfAxiom owlSCOA = owlOPRA.asOWLSubClassOfAxiom();
			return AxiomConverter(owlSCOA);

		} 
		
		else if (axiom instanceof OWLSubObjectPropertyOfAxiom) {
			OWLSubObjectPropertyOfAxiom owlSOPOA = (OWLSubObjectPropertyOfAxiom) axiom;
			Formula converted = new Inclusion(RoleExpressionConverter(owlSOPOA.getSubProperty()),
					RoleExpressionConverter(owlSOPOA.getSuperProperty()));
			return Collections.singletonList(converted);

		} else if (axiom instanceof OWLEquivalentObjectPropertiesAxiom) {
			OWLEquivalentObjectPropertiesAxiom owlEOPA = (OWLEquivalentObjectPropertiesAxiom) axiom;
			Set<OWLSubObjectPropertyOfAxiom> owlSOPOAs = owlEOPA.asSubObjectPropertyOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubObjectPropertyOfAxiom owlSOPOA : owlSOPOAs) {
				converted.addAll(AxiomConverter(owlSOPOA));
			}
			return converted;
			
		} else if (axiom instanceof OWLClassAssertionAxiom) {
			OWLClassAssertionAxiom owlCAA = (OWLClassAssertionAxiom) axiom;
			Formula converted = new Inclusion(IndividualConverter(owlCAA.getIndividual()),
					ClassExpressionConverter(owlCAA.getClassExpression()));
			return Collections.singletonList(converted);

		} else if (axiom instanceof OWLObjectPropertyAssertionAxiom) {
			OWLObjectPropertyAssertionAxiom owlOPAA = (OWLObjectPropertyAssertionAxiom) axiom;
			Formula converted = new Inclusion(IndividualConverter(owlOPAA.getSubject()), new Exists(
					RoleExpressionConverter(owlOPAA.getProperty()), IndividualConverter(owlOPAA.getObject())));
			return Collections.singletonList(converted);
		}*/

		return Collections.emptyList();
	}
	
	public List<Formula> AxiomConverter_ShortForm(OWLAxiom axiom) {

		if (axiom instanceof OWLSubClassOfAxiom) {
			OWLSubClassOfAxiom owlSCOA = (OWLSubClassOfAxiom) axiom;
			Formula converted = new Inclusion(ClassExpressionConverter_ShortForm(owlSCOA.getSubClass()),
					ClassExpressionConverter_ShortForm(owlSCOA.getSuperClass()));
			return Collections.singletonList(converted);

		} else if (axiom instanceof OWLEquivalentClassesAxiom) {
			OWLEquivalentClassesAxiom owlECA = (OWLEquivalentClassesAxiom) axiom;
			Set<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlECA.asOWLSubClassOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
				converted.addAll(AxiomConverter_ShortForm(owlSCOA));
			}
			return converted;

		} else if (axiom instanceof OWLDisjointClassesAxiom) {
			OWLDisjointClassesAxiom owlDCA = (OWLDisjointClassesAxiom) axiom;
			Set<OWLSubClassOfAxiom> owlSubClassOfAxioms = owlDCA.asOWLSubClassOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubClassOfAxiom owlSCOA : owlSubClassOfAxioms) {
				converted.addAll(AxiomConverter_ShortForm(owlSCOA));
			}
			return converted;

		} 
		
		/*
		else if (axiom instanceof OWLDisjointUnionAxiom) {
			OWLDisjointUnionAxiom owlDUA = (OWLDisjointUnionAxiom) axiom;
			OWLEquivalentClassesAxiom owlECA = owlDUA.getOWLEquivalentClassesAxiom();
			OWLDisjointClassesAxiom owlDCA = owlDUA.getOWLDisjointClassesAxiom();
			List<Formula> converted = new ArrayList<>();
			converted.addAll(AxiomConverter_ShortForm(owlECA));
			converted.addAll(AxiomConverter_ShortForm(owlDCA));
			return converted;

		} else if (axiom instanceof OWLObjectPropertyDomainAxiom) {
			OWLObjectPropertyDomainAxiom owlOPDA = (OWLObjectPropertyDomainAxiom) axiom;
			OWLSubClassOfAxiom owlSCOA = owlOPDA.asOWLSubClassOfAxiom();
			return AxiomConverter_ShortForm(owlSCOA);

		} else if (axiom instanceof OWLObjectPropertyRangeAxiom) {
			OWLObjectPropertyRangeAxiom owlOPRA = (OWLObjectPropertyRangeAxiom) axiom;
			OWLSubClassOfAxiom owlSCOA = owlOPRA.asOWLSubClassOfAxiom();
			return AxiomConverter_ShortForm(owlSCOA);

		} 
		
		else if (axiom instanceof OWLSubObjectPropertyOfAxiom) {
			OWLSubObjectPropertyOfAxiom owlSOPOA = (OWLSubObjectPropertyOfAxiom) axiom;
			Formula converted = new Inclusion(RoleExpressionConverter_ShortForm(owlSOPOA.getSubProperty()),
					RoleExpressionConverter_ShortForm(owlSOPOA.getSuperProperty()));
			return Collections.singletonList(converted);

		} else if (axiom instanceof OWLEquivalentObjectPropertiesAxiom) {
			OWLEquivalentObjectPropertiesAxiom owlEOPA = (OWLEquivalentObjectPropertiesAxiom) axiom;
			Set<OWLSubObjectPropertyOfAxiom> owlSOPOAs = owlEOPA.asSubObjectPropertyOfAxioms();
			List<Formula> converted = new ArrayList<>();
			for (OWLSubObjectPropertyOfAxiom owlSOPOA : owlSOPOAs) {
				converted.addAll(AxiomConverter_ShortForm(owlSOPOA));
			}
			return converted;
			
		} else if (axiom instanceof OWLClassAssertionAxiom) {
			OWLClassAssertionAxiom owlCAA = (OWLClassAssertionAxiom) axiom;
			Formula converted = new Inclusion(IndividualConverter_ShortForm(owlCAA.getIndividual()),
					ClassExpressionConverter_ShortForm(owlCAA.getClassExpression()));
			return Collections.singletonList(converted);

		} else if (axiom instanceof OWLObjectPropertyAssertionAxiom) {
			OWLObjectPropertyAssertionAxiom owlOPAA = (OWLObjectPropertyAssertionAxiom) axiom;
			Formula converted = new Inclusion(IndividualConverter_ShortForm(owlOPAA.getSubject()),
					new Exists(RoleExpressionConverter_ShortForm(owlOPAA.getProperty()),
							IndividualConverter_ShortForm(owlOPAA.getObject())));
			return Collections.singletonList(converted);
		}*/

		return Collections.emptyList();
	}

	private Formula ClassExpressionConverter(OWLClassExpression concept) {
	
		if (concept.isTopEntity()) {
			return TopConcept.getInstance();

		} else if (concept.isBottomEntity()) {
			return BottomConcept.getInstance();

		} else if (concept instanceof OWLClass) {
			OWLClass owlClass = (OWLClass) concept;
			return new AtomicConcept(owlClass.getIRI().toString());

		} else if (concept instanceof OWLObjectComplementOf) {
			OWLObjectComplementOf owlOCO = (OWLObjectComplementOf) concept;
			return new Negation(ClassExpressionConverter(owlOCO.getOperand()));

		} else if (concept instanceof OWLObjectSomeValuesFrom) {
			OWLObjectSomeValuesFrom owlOSVF = (OWLObjectSomeValuesFrom) concept;
			return new Exists(RoleExpressionConverter(owlOSVF.getProperty()),
					ClassExpressionConverter(owlOSVF.getFiller()));

		} else if (concept instanceof OWLObjectAllValuesFrom) {
			OWLObjectAllValuesFrom owlOAVF = (OWLObjectAllValuesFrom) concept;
			return new Forall(RoleExpressionConverter(owlOAVF.getProperty()),
					ClassExpressionConverter(owlOAVF.getFiller()));

		} else if (concept instanceof OWLObjectIntersectionOf) {
			OWLObjectIntersectionOf owlOIO = (OWLObjectIntersectionOf) concept;
			List<Formula> conjunct_list = new ArrayList<>();
			for (OWLClassExpression conjunct : owlOIO.getOperands()) {
				conjunct_list.add(ClassExpressionConverter(conjunct));
			}
			return new And(conjunct_list);

		} else if (concept instanceof OWLObjectUnionOf) {
			OWLObjectUnionOf owlOUO = (OWLObjectUnionOf) concept;
			List<Formula> disjunct_list = new ArrayList<>();
			for (OWLClassExpression disjunct : owlOUO.getOperands()) {
				disjunct_list.add(ClassExpressionConverter(disjunct));
			}
			return new Or(disjunct_list);
		}

		return TopConcept.getInstance();
	}
	
	private Formula ClassExpressionConverter_ShortForm(OWLClassExpression concept) {
		
		if (concept.isTopEntity()) {
			return TopConcept.getInstance();

		} else if (concept.isBottomEntity()) {
			return BottomConcept.getInstance();

		} else if (concept instanceof OWLClass) {
			OWLClass owlClass = (OWLClass) concept;
			return new AtomicConcept(owlClass.getIRI().getShortForm());

		} else if (concept instanceof OWLObjectComplementOf) {
			OWLObjectComplementOf owlOCO = (OWLObjectComplementOf) concept;
			return new Negation(ClassExpressionConverter_ShortForm(owlOCO.getOperand()));

		} else if (concept instanceof OWLObjectSomeValuesFrom) {
			OWLObjectSomeValuesFrom owlOSVF = (OWLObjectSomeValuesFrom) concept;
			return new Exists(RoleExpressionConverter_ShortForm(owlOSVF.getProperty()),
					ClassExpressionConverter_ShortForm(owlOSVF.getFiller()));

		} else if (concept instanceof OWLObjectAllValuesFrom) {
			OWLObjectAllValuesFrom owlOAVF = (OWLObjectAllValuesFrom) concept;
			return new Forall(RoleExpressionConverter_ShortForm(owlOAVF.getProperty()),
					ClassExpressionConverter_ShortForm(owlOAVF.getFiller()));

		} else if (concept instanceof OWLObjectIntersectionOf) {
			OWLObjectIntersectionOf owlOIO = (OWLObjectIntersectionOf) concept;
			List<Formula> conjunct_list = new ArrayList<>();
			for (OWLClassExpression conjunct : owlOIO.getOperands()) {
				conjunct_list.add(ClassExpressionConverter_ShortForm(conjunct));
			}
			return new And(conjunct_list);

		} else if (concept instanceof OWLObjectUnionOf) {
			OWLObjectUnionOf owlOUO = (OWLObjectUnionOf) concept;
			List<Formula> disjunct_list = new ArrayList<>();
			for (OWLClassExpression disjunct : owlOUO.getOperands()) {
				disjunct_list.add(ClassExpressionConverter_ShortForm(disjunct));
			}
			return new Or(disjunct_list);
		} 

		return TopConcept.getInstance();
	}
	
	private RoleExpression RoleExpressionConverter(OWLObjectPropertyExpression role) {

		if (role.isTopEntity()) {
			return TopRole.getInstance();
			
		} else if (role.isBottomEntity()) {
			return BottomRole.getInstance();
			
		} else if (role instanceof OWLObjectProperty) {
			OWLObjectProperty owlOP = (OWLObjectProperty) role;
			return new AtomicRole(owlOP.getIRI().toString());
			
		}

		return TopRole.getInstance();
	}
	
	private RoleExpression RoleExpressionConverter_ShortForm(OWLObjectPropertyExpression role) {

		if (role.isTopEntity()) {
			return TopRole.getInstance();
			
		} else if (role.isBottomEntity()) {
			return BottomRole.getInstance();
			
		} else if (role instanceof OWLObjectProperty) {
			OWLObjectProperty owlOP = (OWLObjectProperty) role;
			return new AtomicRole(owlOP.getIRI().getShortForm());
			
		}

		return TopRole.getInstance();
	}
	
	/*private ConceptExpression IndividualConverter(OWLIndividual indi) {

		if (indi instanceof OWLNamedIndividual) {
			OWLNamedIndividual owlIndi = (OWLNamedIndividual) indi;
			return new Individual(owlIndi.getIRI().toString());
			
		}

		return TopConcept.getInstance();
	}
	
	private ConceptExpression IndividualConverter_ShortForm(OWLIndividual indi) {

		if (indi instanceof OWLNamedIndividual) {
			OWLNamedIndividual owlIndi = (OWLNamedIndividual) indi;
			return new Individual(owlIndi.getIRI().getShortForm());
			
		}

		return TopConcept.getInstance();
	}*/

}
