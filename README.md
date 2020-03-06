# How to run
OntoLDiff is implemented in Java, so before running it, please make sure that you have Java Runtime Environment (JRE) installed on your computer. Please add all dependencies (the above .jar files) in your program when running OntoLDiff.

We provide the source code for OntoLDiff, which can be downloaded from here, and compiled and run by typing in command line or with a Java IDE such as Eclipse. The main() method is situated in LDiff.java under the forgetting folder.

The input are O1, O2 and a path specifying the location where you want the output to be saved. The output are a set of witnesses, a set of explicit witnesses and a set of implicit witnesses, saved as .owl files; see the following example (please adjust it to your own operating environment, i.e., windows, linux or Mac).

O1: file:///C:/Users/XXX/Desktop/snomed_ct/snomed_ct_australian.owl

O2: file:///C:/Users/XXX/Desktop/snomed_ct/snomed_ct_intl_20170731.owl

Path: C:\Users\XXX\Desktop\snomed_ct

We also provide an executable .jar file in the "executable" folder. One can run it by typing in command line: java -jar LDiff.jar
