(* Auto-generated from "authority.atd" *)
              [@@@ocaml.warning "-27-32-35-39"]

type public_key = { g: string; p: string; q: string; y: string }[@@deriving show]

type proofDLog = { challenge: string; commitment: string; response: string }[@@deriving show]

type commitment = { a: string; b: string }[@@deriving show]

type proof = { challenge: string; commitment: commitment; response: string }[@@deriving show]

type authority = {
  decryption_factors: string list list;
  decryption_proofs: proof list list;
  email: string;
  pok: proofDLog;
  public_key: public_key;
  public_key_hash: string;
  uuid: string
}[@@deriving show]
