(* Auto-generated from "voter.atd" *)


type commitment = Voter_t.commitment = { a: string; b: string }

type proof = Voter_t.proof = {
  challenge: string;
  commitment: commitment;
  response: string
}

type choice = Voter_t.choice = {
  choice_alpha (*atd alpha *): string;
  choice_beta (*atd beta *): string
}

type answer = Voter_t.answer = {
  choices: choice list;
  individual_proofs: proof list list;
  overall_proof: string
}

type voter = Voter_t.voter = {
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

val write_voter :
  Bi_outbuf.t -> voter -> unit
  (** Output a JSON value of type {!voter}. *)

val string_of_voter :
  ?len:int -> voter -> string
  (** Serialize a value of type {!voter}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_voter :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> voter
  (** Input JSON data of type {!voter}. *)

val voter_of_string :
  string -> voter
  (** Deserialize JSON data of type {!voter}. *)

