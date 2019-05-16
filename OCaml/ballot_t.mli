open Voter_t
(* Auto-generated from "ballot.atd" *)
              [@@@ocaml.warning "-27-32-35-39"]

type ballot = {
  cast_at: string option;
  vote: voter option;
  vote_hash: string option;
  voter_hash: string;
  voter_uuid: string
}
