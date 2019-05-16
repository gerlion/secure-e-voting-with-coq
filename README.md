# Verified code for verifiable elections
Both the Coq and OCaml code come with makefiles 
# Dependencies 
The Coq Proof Assistant, version 8.8.2
OCaml, version 4.03.0
unix,zarith,batteries,yojson,atdgen,ppx_deriving
# Coq code
Running make helios.vo will prompt Coq to check the proofs
Running make Extraction.vo will prompt Coq to extract the libaries
# OCaml Code
Running make compile will prompt OCaml to compile
Running make run will will verify the election data for Helios IACR 2018
### Note this code is being made avaliable as part of CCS 2019 submission
the authors' names will be posted at a later date
