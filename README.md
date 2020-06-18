### Long Version of Our Submission
In the above, we provide a long version of our submission, namely SIGIR2020_Long_Version.pdf, where we include all formal proofs of the theorems and lemmas, and more illustrative examples that give insights into the ideas and usage of the inference rules presented in our submission. We highly recommend the readers to refer to this version for a better understanding of the materials and our contributions of this work. The long version can be downloaded by right clicking on it and saving it somewhere locally on your computer, or by clicking the green button "Clone or download" as a zip file, together with the source code for our forgetting prototype. <br><br>
### Usage of the Prototype
The input to the prototype are an ontology and a set of concept and role names to be forgotten, which must be specified in OWL format. We provide users with a GUI for easy try-out of the prototype. The main() method for invoking the GUI is situated in the "FameGUI.java" under the "swing" folder. The GUI can be called out by running it there, ideally with an Java IDE such as Eclipse. <br><br>
### Test Data
The above test_data folder includes the 396 ontologies used for the evaluation of our prototype, described in detail in our submission. Due to the file upload size limits of GitHub, we have partitioned them into 6 zip files. 

### For Developer
Requirements:
1. Gradle 6 or above
2. JDK 1.8 
```
git clone https://github.com/anonymous-ai-researcher/prototype.git
cd prototype
gradlew.bat run (for Linux run: ./gradlew run)
```
