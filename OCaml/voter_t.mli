(* Auto-generated from "voter.atd" *)
              [@@@ocaml.warning "-27-32-35-39"]

type commitment = { a: string; b: string }[@@deriving show]

type proof = { challenge: string; commitment: commitment; response: string }[@@deriving show]

type choice = {
  choice_alpha (*atd alpha *): string;
  choice_beta (*atd beta *): string
}[@@deriving show]

type answer = {
  choices: choice list;
  individual_proofs: proof list list;
  overall_proof: string option
}[@@deriving show]

type voter = {
  answers: answer list;
  election_hash: string;
  election_uuid: string
}[@@deriving show]
