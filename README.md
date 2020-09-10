# Secure E-Voting with Coq
This repository contains the code associated with the CCS 2019 paper
"Verified verifiers for verifying elections" by Thomas Haines, Rajeev 
Gore and Mukesh Tiwari which was subsequently expanded upon by
"Did you mix me? Formally Verifying Verifiable Mix Nets in Electronic Voting" 
by Thomas Haines, Rajeev Gore and Bhavesh Sharma.

# Summary

This repo contains the first steps in ongoing work to have machine checked
code for the cryptographic primitives that are used in e-voting.  In addition,
the work extends to proving that using the primitives in a certain way suffices
for the integrity of the tallying process up to some specific limitations (which is commonly called universal verifiability).

This tool is useful for getting confidence in the validity of the verification
specification but is no substitute for extensive and open critique.  
Please read the corresponding papers for discussion of the limitations.

Both the Coq and OCaml code come with makefiles 

# Dependencies 
The Coq Proof Assistant, version 8.11.2  
OCaml, version 4.10.0  
coq-color
coq-prime
zarith,batteries,yojson,atdgen,ppx_deriving
# Installation instructions
(These instructions were tested on a clean Ubuntu-20.04.1 (64 bit) install inside VirtualBox)
## Installing opam 2
sudo add-apt-repository ppa:avsm/ppa
sudo apt update
sudo apt install opam
## Init opam
sudo apt-get install m4
sudo apt install libgmp-dev
opam init --comp 4.10.0
eval $(opam env)
opam update
## Install coq
opam pin add coq 8.11.2
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-color
opam install coq-coqprime
## Install other dep
opam install zarith
opam install batteries
opam install yojson
opam install atdgen
opam install ppx_deriving

# Coq code
## Helios
Running make helios.vo will prompt coq to check the proofs for helios
Running make ExtractionHelios.vo will prompt Coq to extract the libraries
(Both checking and extracting check the proofs of primality which is time consuming)
## Mix nets
Running make wikstromMatrix.vo will prompt Coq to check the proofs
Running make ExtractionMixnet.vo will prompt Coq to extract the libraries
(Note, again, that extraction checks the proof of primality for the numbers used in the implementation and is therefore time consuming (1hr). The reader may wish to simply look at the already extracted code)
## Runtime optimisations
We suggest the following modification from what is 
directly extracted from Coq.
1. Replace the extracted implementation of modulo for integers with Big_int.mod_big_int.
    On line ~380 (depending on which libary was extracted)
    replace "let (_, r) = div_eucl a b in r" with "Big_int.mod_big_int a b"
2. Optionally the defintion of inv0 can be replaced by Fermat's little theorem 
    but this is less essenital.

# OCaml Code
This repository comes preloaded with three transcripts.  
One from Helios, one from CHVote mixnet, and one from Verificatum mixnet.
Anyone can also download these open source projects and generate additional transcripts.
The transcripts are embedded in the main.ml files in the respective folders.  

The folders are setup with the appropriate extracted code already included but this can 
be substituted with freshly extracted code by following the instructions provided.
## CHVote
Copy lib.ml into the OCamlVerificatum folder.
Change the primes as follows
1. replace "let p = ..." with "let p = Big.of_string "11""
2. replace "let q = ..." with "let q =  Big.of_string "5""

To compile 
    make
To run 
    make run
## Verificatum
Copy lib.ml into the OCamlVerificatum folder.
Change the primes as follows
1. replace "let p = ..." with "let p = Big.of_string "8095455969267383450536091939011431888343052744233774808515030596297626946131583007491317242326621464546135030140184007406503191036604066436734360427237223""
2. replace "let q = ..." with "let q =  Big.of_string "4047727984633691725268045969505715944171526372116887404257515298148813473065791503745658621163310732273067515070092003703251595518302033218367180213618611""
Change the number of expected ciphertexts as follows
3. add the helper function intToNat "let rec intToNat = (fun i ->
  match i with
  | 0 -> O
  | x -> S (intToNat (x-1))
)
"
4. replace "let coq_N = S O" with "let coq_N = intToNat 99"

To compile 
    make
To run 
    make run
## Helios
Copy lib.ml into the OCaml folder
Running make compile will prompt OCaml to compile  
Running make run will will verify the election data for Helios IACR 2018  


## Note: 
This is not the development repo for the ongoing work.  Place contact 
Thomas Haines (thomas.haines@ntnu.no) with any questions or for
the latest version.

## External Contributors :

Stéphane Glondu 


