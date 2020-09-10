all : matrices.vo dualvectorspaces.vo modulevectorspace.vo  nthvectorspaces.vo groupfromring.vo genprodvectorspaces.vo 

#all .vo file dependes on .v file
%.vo : %.v
	coqc -R ../ "" $*.v

#compile groups.v
groups.vo : groups.v

module.vo : groups.vo module.v

vectorspace.vo : module.vo vectorspace.v

modulevectorspace.vo : vectorspace.vo modulevectorspace.v

CoLoRmatrix.vo : CoLoRmatrix.v

matricesF.vo : module.vo CoLoRmatrix.vo matricesF.v

matrices.vo : module.vo CoLoRmatrix.vo matricesF.vo matrices.v

groupfromring.vo : groupfromring.v

dualvectorspaces.vo: vectorspace.vo dualvectorspaces.v

nthvectorspaces.vo : vectorspace.vo matrices.vo modulevectorspace.vo nthvectorspaces.v

genprodvectorspaces.vo : genprodvectorspaces.v

#run clean
clean :
	rm -rf *.vo *.vos *.vok *.glob .*.aux

