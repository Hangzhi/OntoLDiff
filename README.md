# Thanks for your interest in OntoLDiff.

We provide an executable jar file, namely, LDiff.jar. 

LDiff.jar is a command-line tool that allows one to compute the logical difference Diff(O1, O2) between two ontologies O1 and O2. The input are O1, O2 and a path specifying the location where you want the output to be saved; see the following example.

O1: 
file:///C:/Users/XXX/Desktop/snomed_ct/snomed_ct_australian.owl
O2:
file:///C:/Users/XXX/Desktop/snomed_ct/snomed_ct_intl_20170731.owl
Path: 
C:\\Users\\XXX\\Desktop\\snomed_ct 

The output are a set of witnesses, a set of explicit witnesses and a set of implicit witnesses, represented as owl.xml files.

We include the test data used in the IJCAR2020 submission (snomed_ct.zip) in the folder. We also include another test data (ncit.zip) for play-around. 

Thank you very much!
