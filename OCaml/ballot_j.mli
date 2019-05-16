open Voter_t
open Voter_j
(* Auto-generated from "ballot.atd" *)
[@@@ocaml.warning "-27-32-35-39"]

type ballot = Ballot_t.ballot = {
  cast_at: string option;
  vote: voter option;
  vote_hash: string option;
  voter_hash: string;
  voter_uuid: string
}

val write_ballot :
  Bi_outbuf.t -> ballot -> unit
  (** Output a JSON value of type {!ballot}. *)

val string_of_ballot :
  ?len:int -> ballot -> string
  (** Serialize a value of type {!ballot}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_ballot :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> ballot
  (** Input JSON data of type {!ballot}. *)

val ballot_of_string :
  string -> ballot
  (** Deserialize JSON data of type {!ballot}. *)

