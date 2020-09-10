(* Auto-generated from "voterAudit.atd" *)
[@@@ocaml.warning "-27-32-35-39"]

type commitment = VoterAudit_t.commitment = { a: string; b: string }

type proof = VoterAudit_t.proof = {
  challenge: string;
  commitment: commitment;
  response: string
}

type choice = VoterAudit_t.choice = {
  choice_alpha (*atd alpha *): string;
  choice_beta (*atd beta *): string
}

type answer = VoterAudit_t.answer = {
  choices: choice list;
  individual_proofs: proof list list;
  overall_proof: string option;
  answer: string list;
  randomness: string list
}

type voterAudit = VoterAudit_t.voterAudit = {
  answers: answer list;
  election_hash: string;
  election_uuid: string
}

val write_commitment :
  Bi_outbuf.t -> commitment -> unit
  (** Output a JSON value of type {!commitment}. *)

val string_of_commitment :
  ?len:int -> commitment -> string
  (** Serialize a value of type {!commitment}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_commitment :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> commitment
  (** Input JSON data of type {!commitment}. *)

val commitment_of_string :
  string -> commitment
  (** Deserialize JSON data of type {!commitment}. *)

val write_proof :
  Bi_outbuf.t -> proof -> unit
  (** Output a JSON value of type {!proof}. *)

val string_of_proof :
  ?len:int -> proof -> string
  (** Serialize a value of type {!proof}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_proof :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> proof
  (** Input JSON data of type {!proof}. *)

val proof_of_string :
  string -> proof
  (** Deserialize JSON data of type {!proof}. *)

val write_choice :
  Bi_outbuf.t -> choice -> unit
  (** Output a JSON value of type {!choice}. *)

val string_of_choice :
  ?len:int -> choice -> string
  (** Serialize a value of type {!choice}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_choice :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> choice
  (** Input JSON data of type {!choice}. *)

val choice_of_string :
  string -> choice
  (** Deserialize JSON data of type {!choice}. *)

val write_answer :
  Bi_outbuf.t -> answer -> unit
  (** Output a JSON value of type {!answer}. *)

val string_of_answer :
  ?len:int -> answer -> string
  (** Serialize a value of type {!answer}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_answer :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> answer
  (** Input JSON data of type {!answer}. *)

val answer_of_string :
  string -> answer
  (** Deserialize JSON data of type {!answer}. *)

val write_voterAudit :
  Bi_outbuf.t -> voterAudit -> unit
  (** Output a JSON value of type {!voterAudit}. *)

val string_of_voterAudit :
  ?len:int -> voterAudit -> string
  (** Serialize a value of type {!voterAudit}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_voterAudit :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> voterAudit
  (** Input JSON data of type {!voterAudit}. *)

val voterAudit_of_string :
  string -> voterAudit
  (** Deserialize JSON data of type {!voterAudit}. *)

