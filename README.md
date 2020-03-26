# YASSi Nextgen



YASSi implements symbolic execution based on the LLVM intermediate representation ("bitcode"). 

To this end, YASSi is able to execute code written in C/C++ which can be converted into the LLVM IR format. YASSi allows it to explore functions in order to:

	- Check assertions and generate counter examples
	- Generate test cases (stimuli) for testing



In order to build YASSi some third party libraries/tools have to be downloaded. The build process is based on Cmake and, tools which are not assumed to be in the distributions repositories are getting downloaded automatically.  For building YASSi please have to look to the INSTALL document located in the 10_doc folder.



First steps for using YASSi including it's intrinsic functions are shown in 10_doc/first_steps.



YASSi is developed using Arch Linux. However, in order to check its compatibility to other Distributions like  CentOS the build process and the unit test are getting checked from time to time. 



The development of YASSi is based at the Johannes Kepler University Linz in cooperation with Mr. Pablo Gonzales de Aledo which first started the development of YASSi.



