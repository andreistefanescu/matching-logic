First, set up CIL:
	- unzip CIL to ./cil.  (We have tested using version 1.3.7)
	- Configure and compile it as per its INSTALL file.  
	
Second, install the K-Framework:
	- http://code.google.com/p/k-framework/
	
Now, configure the Makefile:
	- set GCC
	- set CIL_PLATFORM to match with your cil/obj/<CIL_PLATFORM> directory
	- set K-MAUDE to line up with your K-framework installation 
	- check any other directories to match your system

Finally, build the tool:
	- run "make"
	- run "make semantics"