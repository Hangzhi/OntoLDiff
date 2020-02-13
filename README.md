# How to run
OntoLDiff is implemented in Java, so before running it, please make sure that you have Java Runtime Environment (JRE) installed on your computer.

We provide the source code for OntoLDiff, which can be downloaded from here, and compiled and run by typing in command line or with a Java IDE such as Eclipse. The main() method is situated in LDiff.java under the forgetting repository.

The input are O1, O2 and a path specifying the location where you want the output to be saved. The output are a set of witnesses, a set of explicit witnesses and a set of implicit witnesses, saved as owl.xml files. see the following example (please adjust to your own operating environment, i.e., windows or linux).

O1: file:///C:/Users/XXX/Desktop/snomed_ct/snomed_ct_australian.owl  

O2: file:///C:/Users/XXX/Desktop/snomed_ct/snomed_ct_intl_20170731.owl           

Path: C:\\Users\\XXX\\Desktop\\snomed_ct 

We also provide an executable .jar file in the "executable" folder.
