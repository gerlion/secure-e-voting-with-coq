all : BGShuffleArg.vo WikiMix.vo

#all .vo file dependes on .v file
%.vo : %.v
	coqc -R ../ "" $*.v

sigmaprotocolPlus.vo : sigmaprotocolPlus.v

sigmaprotocolPlus5.vo : sigmaprotocolPlus.vo sigmaprotocolPlus5.v

sigmaprotocolPlus9.vo : sigmaprotocolPlus5.vo sigmaprotocolPlus9.v

BayerGrothSupport.vo : BayerGrothSupport.v 

BGMultiexpArg.vo : sigmaprotocolPlus.vo BayerGrothSupport.vo BGMultiexpArg.v

BGSingleProd.vo : sigmaprotocolPlus.vo BGSingleProd.v

BGZero.vo : BayerGrothSupport.vo sigmaprotocolPlus.vo BGZero.v

BGMultiexpArg.vo : BGMultiexpArg.v

BGHadProduct.vo : BGZero.vo sigmaprotocolPlus5.vo BGHadProduct.v

BGProdArg.vo : BGHadProduct.vo BGSingleProd.vo BGProdArg.v

BGShuffleArg.vo : sigmaprotocolPlus9.vo BGProdArg.vo BGMultiexpArg.vo BGShuffleArg.v

WikiSigma.vo : sigmaprotocolPlus.vo WikiSigma.v

basicSigmasPlus.vo : sigmaprotocolPlus.vo basicSigmasPlus.v

WikiMix.vo : sigmaprotocolPlus5.vo basicSigmasPlus.vo WikiSigma.vo WikiMix.v

extract.vo : BGShuffleArg.vo extract.v

#run clean
clean :
	rm -rf *.vo *.vos *.vok *.glob .*.aux *.crashcoqide
