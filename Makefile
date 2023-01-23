#all .vo file dependes on .v file
%.vo : %.v
	coqc -R Groups Groups $*.v

# compile coqprime file
VectorUtil.vo : VectorUtil.v

makeGroups : VectorUtil.vo 
	make -C Groups

makeElectionGuard : basicSigmas.vo
	make -C ElectionGuard

#compile primeQ
primeQ.vo : primeQ.v

primeP.vo : primeP.v 

#compile singmaprotocol.v
sigmaprotocol.vo : makeGroups sigmaprotocol.v 

cryptoprim.vo : makeGroups cryptoprim.v 

basicSigmas.vo : cryptoprim.vo sigmaprotocol.vo basicSigmas.v

sigmaprotocolPlus.vo : basicSigmas.vo sigmaprotocolPlus.v

wikstromMatrix.vo : basicSigmas.vo wikstromMatrix.v

PPATC.vo : wikstromMatrix.vo PPATC.v

#compile HeliosIACR2018.v and other dependencies
HeliosIACR2018.vo : primeQ.vo primeP.vo HeliosIACR2018.v

mixnetTest.vo : HeliosIACR2018.vo wikstromMatrix.vo mixnetTest.v

#compile helios.v
helios.vo : cryptoprim.vo sigmaprotocol.vo basicSigmas.vo HeliosIACR2018.vo helios.v

#code extraction
ExtractionHelios.vo : helios.vo ExtractionHelios.v
ExtractionMixnet.vo : mixnetTest.vo ExtractionMixnet.v

BayerGroth : cryptoprim.vo
	make -C BayerGroth
	
Extraction : cryptoprim.vo HeliosIACR2018.vo
	make -C BayerGroth extract.vo

#run clean
clean :
	rm -rf *.vo *.vos *.vok *.glob .*.aux .*.cache && cd Groups && make clean && cd .. && cd ElectionGuard && make clean && cd .. && cd BayerGroth && make clean 
