
compile : big.ml lib.ml voter_t.ml voter_t.mli voter_j.ml voter_j.mli ballot_t.ml ballot_t.mli ballot_j.ml ballot_j.mli authority_t.ml authority_t.mli authority_j.ml authority_j.mli voterlist_t.ml voterlist_t.mli voterlist_j.ml voterAudit_t.ml voterAudit_t.mli voterAudit_j.ml voterAudit_j.mli main.ml
	ocamlfind ocamlopt -o a.out -linkpkg -package zarith,batteries,yojson,atdgen,ppx_deriving.std big.ml lib.ml voter_t.mli voter_t.ml voter_j.mli voter_j.ml ballot_t.mli ballot_t.ml ballot_j.mli ballot_j.ml voterlist_t.mli voterlist_t.ml voterlist_j.mli voterlist_j.ml authority_t.mli authority_t.ml authority_j.mli authority_j.ml voterAudit_t.mli voterAudit_t.ml voterAudit_j.mli voterAudit_j.ml  main.ml

clean : 
	rm -rf *.cmx *.cmi *.o a.out
run : 
	./a.out
