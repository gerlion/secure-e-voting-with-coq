all : matrices.vo dualvectorspaces.vo modulevectorspace.vo  nthvectorspaces.vo groupfromring.vo genprodvectorspaces.vo CommonSSR.vo Gaussian.vo LinIndep.vo Vandermonde.vo Matrix.vo matricesField.vo

#all .vo file dependes on .v file
%.vo : %.v
	coqc -R ../ "" $*.v

CommonSSR.vo : CommonSSR.v

Gaussian.vo : CommonSSR.vo Gaussian.v

LinIndep.vo : CommonSSR.vo Gaussian.vo LinIndep.v

Vandermonde.vo : LinIndep.vo Vandermonde.v

Matrix.vo : vectorspace.vo  Vandermonde.vo Matrix.v

#compile groups.v
groups.vo : groups.v

module.vo : groups.vo module.v

vectorspace.vo : module.vo vectorspace.v

modulevectorspace.vo : vectorspace.vo modulevectorspace.v

CoLoRmatrix.vo : CoLoRmatrix.v

VectorUtil.vo : 
	make -C ../ VectorUtil.vo

matricesF.vo : VectorUtil.vo module.vo CoLoRmatrix.vo matricesF.v

matricesField.vo : Matrix.vo vectorspace.vo CoLoRmatrix.vo matricesF.vo matricesField.v

matrices.vo : module.vo CoLoRmatrix.vo matricesF.vo matrices.v

groupfromring.vo : groupfromring.v

dualvectorspaces.vo: vectorspace.vo dualvectorspaces.v

nthvectorspaces.vo : vectorspace.vo matrices.vo modulevectorspace.vo nthvectorspaces.v

genprodvectorspaces.vo : genprodvectorspaces.v

#run clean
clean :
	rm -rf *.vo *.vos *.vok .*.cache *.glob .*.aux

