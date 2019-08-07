# Secure E-Voting with Coq
This repository contains the code associated with the CCS 2019 submission
"Verified code for verifying elections" by Thomas Haines, Rajeev 
Gore and Mukesh Tiwari.

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

## Note: 
This is not the development repo for the ongoing work.  Place contact 
Thomas Haines (thomas.haines@ntnu.no) with any questions or for
the latest version.

