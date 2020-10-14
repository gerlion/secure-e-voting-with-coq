all :  ElectionGuard.vo

prime : 
	make -C Primes -j 8 all

#all .vo file dependes on .v file
%.vo : %.v
	coqc -R ../ "" -R ../Groups Groups $*.v

EGmodules.vo : prime EGmodules.v

ElectionGuard.vo : ElectionGuard.v

Extraction.vo : EGmodules.vo ElectionGuard.vo Extraction.v

#run clean
clean :
	rm -rf *.vo *.vos *.vok *.glob .*.aux .*.cache && cd Primes && make clean
