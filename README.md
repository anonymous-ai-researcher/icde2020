### Overview of the Prototype

The Prototype is a uniform interpolation tool for creating views of OWL ontologies using expressive description logics. The current version comes with functionality for computing uniform interpolants and logical difference, and can be used as a Java library and as a standalone tool.

At the core of the Prototype is the computation of so-called uniform interpolants. A uniform interpolant is a restricted view of an ontology that only uses a specified set of concept and role names (the interpolation signature), while preserving all logical entailments over the interpolation signature. Uniform interpolants can be computed by forgetting the names not in the interpolation signature (the forgetting signature). 

If the input ontology is cyclic, the uniform interpolant cannot always be represented finitely without fixpoint operators. Since fixpoint operators are not supported by OWL, the Prototype introduce additional concept names (aka definers) to the output ontology that simulate the behaviour of fixpoint operators.

### Set-Up of the Prototype:

1. To get the prototype work, first make sure you have Java Runtime Environment installed on your machine, though we suggest you using an Java IDE such as Eclipse to run the program.

2. Download the source code, together with other dependencies, and import them as a Java project into your IDE.

### Usage of the Prototype

- Computing Uniform Interpolants using the Graphical User Interface (GUI)

The Prototype comes with a simple graphical tool for computing uniform interpolants of OWL ontologies. To start it, just go to the directory "Swing" and run the main method in GUI.java.

![GUI](https://github.com/anonymous-ai-researcher/www/blob/master/GUI.jpg?raw=true)

Via this GUI, users can load an OWL ontology by clicking the "Load Ontology" button and compute uniform interpolants for a selected signature by clicking the "Forget" button, as shown in the screenshot. The concept names (bottom frames) and role names (up frames) selected from the screen are those to be forgotten. The uniform interpolant is then displayed in DL syntax, and can be saved as an .owl file for later use.


### For Developer
Requirements:
1. Gradle 6 or above
2. JDK 1.8 
```
git clone https://github.com/anonymous-ai-researcher/www.git
cd www
gradlew.bat run (for Linux run: ./gradlew run)
```
