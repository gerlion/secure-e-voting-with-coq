# compile coqprime file
prime : 
	make -C Coqprime

#all .vo file dependes on .v file
%.vo : %.v
	coqc -R Coqprime/src/Coqprime Coqprime $*.v

#compile primeQ
primeQ.vo : prime primeQ.v

primeP.vo : prime primeP.v 

#compile groups.v
groups.vo : groups.v

#compile singmaprotocol.v
sigmaprotocol.vo : groups.vo sigmaprotocol.v 

matrices.vo : matrices.v 

cryptoprim.vo : matrices.vo cryptoprim.v 

basicSigmas.vo : cryptoprim.vo basicSigmas.v

#compile HeliosIACR2018.v and other dependencies
HeliosIACR2018.vo : prime groups.vo primeQ.vo primeP.vo HeliosIACR2018.v

#compile helios.v
helios.vo : groups.vo cryptoprim.vo sigmaprotocol.vo basicSigmas.vo HeliosIACR2018.vo helios.v

#code extraction
Extraction.vo : helios.vo Extraction.v


#run clean
clean :
	rm -rf *.vo *.glob && cd Coqprime && make clean
