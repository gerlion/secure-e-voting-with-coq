# Secure E-Voting with Coq
This repository contains the code associated with ongoing working by Haines et al. on machine checked verifiers for evoting.

The following papers are associated with the code here:
* the CCS 2019 paper "Verified verifiers for verifying elections" by Thomas Haines, Rajeev Gore and Mukesh Tiwari 
* the S&P 2021 paper "Did you mix me? Formally Verifying Verifiable Mix Nets in Electronic Voting" by Thomas Haines, Rajeev Gore and Bhavesh Sharma.
* the NordSec 2020 paper "Machine-checking the universal verifiability of ElectionGuard" by Thomas Haines, Rajeev Gore and Jack Stodart
* the NordSec 2020 paper "Efficient mixing of arbitrary ballots with everlasting privacy: How to verifiably mix the PPATC scheme" by Kristian Gjøsteen, Thomas Haines and Morten Solberg 
* the USENIX Security 2023 paper "Machine-checking Multi-Round Proofs of Shuffle: Terelius-Wikstrom and Bayer-Groth" by Thomas Haines, Rajeev Gore and Mukesh Tiwari.

# Summary

This repo contains the first steps in ongoing work to have machine checked
code for the cryptographic primitives that are used in e-voting.  In addition,
the work extends to proving that using the primitives in a certain way suffices
for the integrity of the tallying process up to some specific limitations (which is commonly called universal verifiability).

This tool is useful for getting confidence in the validity of the verification
specification but is no substitute for extensive and open critique.  
Please read the corresponding papers for discussion of the limitations.

Both the Coq and OCaml code come with makefiles 

## Note: 
This is not the development repo for the ongoing work; we also do not comprehensively maintain some of the older works contained here.  Please contact 
Thomas Haines (thomas.haines@anu.edu.au) with any questions or for
the latest version.



# Dependencies 
The Coq Proof Assistant, version 8.16.1  
OCaml, version 4.13.0  
coq-color
coq-prime
coq-mathcomp
zarith,batteries,yojson,atdgen,ppx_deriving

# Installation instructions
(These instructions were tested on a clean Ubuntu-22.04 (64 bit) install inside VirtualBox)
## Installing opam 2
sudo add-apt-repository ppa:avsm/ppa
sudo apt update
sudo apt install opam
## Init opam
sudo apt-get install m4
sudo apt install libgmp-dev
opam init --comp 4.13.0
eval $(opam env)
opam update
## Install coq
opam pin add coq 8.16.1
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-color
opam install coq-coqprime
opam install coq-mathcomp-ssreflect
opam install coq-mathcomp-algebra
## Install other dep
opam install zarith
opam install batteries 
opam pin add atdgen 2.4.1 
opam install ppx_deriving 

# Coq code
## Mix nets
Running "make BayerGroth" in the main folder will prompt Coq to check the proofs for Terelius-Wikstrom and Bayer-Groth

We have currently admitted the Theorem 1 from 
Proofs of Restricted Shuffles, which encodes sufficent
conditions for a Matrix to be a permutation,
this proof is very short in standard mathematics 
but a constructive proof is more involved.

## Helios
Running make helios.vo will prompt coq to check the proofs for helios
Running make ExtractionHelios.vo will prompt Coq to extract the libraries
(Both checking and extracting check the proofs of primality which is time consuming)

## ElectionGuard
Running make makeElectionGuard will prompt Coq to check the proofs
## Runtime optimisations
We suggest the following modification from what is 
directly extracted from Coq.
1. Replace the extracted implementation of modulo for integers with Big_int.mod_big_int.
    On line ~380 (depending on which libary was extracted)
    replace "let (_, r) = div_eucl a b in r" with "Big_int.mod_big_int a b"
2. Optionally the defintion of inv0 can be replaced by Fermat's little theorem 
    but this is less essenital.

# OCaml Code

## Mix nets
Running "make compile" in BayerGroth/Code will prompt OCaml to compile
Running "make run" will verify the text vector from SwissPost
## Helios
Copy lib.ml into the OCaml folder
Running make compile will prompt OCaml to compile  
Running make run will will verify the election data for Helios IACR 2018  
## ElectionGuard
Go to ElectionGuard/OCaml
Running make compile will prompt OCaml to compile  
Running make run will will verify the test election data 

## External Contributors :

Stéphane Glondu 


