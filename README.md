### Usage of the Prototype
The input to the prototype are an ontology and a set of concept and role names to be forgotten, which must be specified in OWL format. We provide users with a GUI for easy try-out of the prototype. The main() method for invoking the GUI is situated in the "FameGUI.java" under the "swing" folder. The GUI can be called out by running it there, ideally with an Java IDE such as Eclipse. <br><br>
### Test Data
The above test_data folder includes the 396 ontologies used for the evaluation of our prototype, described in detail in our submission. Due to the file upload size limits of GitHub, we have partitioned them into 6 zip files. 

### For Developer
Requirements:
1. Gradle 6 or above
2. JDK 1.8 
```
git clone https://github.com/anonymous-ai-researcher/icde2020.git
cd icde2020
gradlew.bat run (for Linux run: ./gradlew run)
```
