(* Auto-generated from "voterAudit.atd" *)
              [@@@ocaml.warning "-27-32-35-39"]

type commitment = { a: string; b: string }

type proof = { challenge: string; commitment: commitment; response: string }

type choice = {
  choice_alpha (*atd alpha *): string;
  choice_beta (*atd beta *): string
}

type answer = {
  choices: choice list;
  individual_proofs: proof list list;
  overall_proof: string option;
  answer: string list;
  randomness: string list
}

type voterAudit = {
  answers: answer list;
  election_hash: string;
  election_uuid: string
}
