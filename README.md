### Overview of the Prototype

The Prototype is a uniform interpolation tool for creating views of OWL ontologies using expressive description logics. The current version comes with functionality for computing uniform interpolants and logical differences, and can be used as a Java library and as a standalone tool.

At the core of the Prototype is the computation of so-called uniform interpolants. A uniform interpolant is a restricted view of an ontology that only uses a specified set of concept and role names, while preserving all logical entailments over this set. Currently, the description logics ALC, ALCH, ALCI, ALCO, ALCHI, ALCHO, ALCOI and ALCHOI are supported. If an input ontology contains axioms that are not expressible in the respective description logic, they will be removed before the uniform interpolation algorithm is applied.

If the input ontology is cyclic, the uniform interpolant cannot always be represented finitely without fixpoint operators. Since fixpoint operators are not supported by OWL, the Prototype introduce additional concept names (aka definers) to the output ontology that simulate the behaviour of fixpoint operators.

### Usage of the Prototype
The input to the prototype are an ontology and a set of concept and role names to be forgotten, which must be specified in OWL format. We provide users with a GUI for easy try-out of the prototype. The main() method for invoking the GUI is situated in the "FameGUI.java" under the "swing" folder. The GUI can be called out by running it there, ideally with an Java IDE such as Eclipse. <br><br>
### Test Data
The above test_data folder includes the 396 ontologies used for the evaluation of our prototype, described in detail in our submission. Due to the file upload size limits of GitHub, we have partitioned them into 6 zip files. 

### For Developer
Requirements:
1. Gradle 6 or above
2. JDK 1.8 
```
git clone https://github.com/anonymous-ai-researcher/www.git
cd www
gradlew.bat run (for Linux run: ./gradlew run)
```
