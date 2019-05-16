(* Auto-generated from "authority.atd" *)
[@@@ocaml.warning "-27-32-35-39"]

type public_key = Authority_t.public_key = {
  g: string;
  p: string;
  q: string;
  y: string
}

type proofDLog = Authority_t.proofDLog = {
  challenge: string;
  commitment: string;
  response: string
}

type commitment = Authority_t.commitment = { a: string; b: string }

type proof = Authority_t.proof = {
  challenge: string;
  commitment: commitment;
  response: string
}

type authority = Authority_t.authority = {
  decryption_factors: string list list;
  decryption_proofs: proof list list;
  email: string;
  pok: proofDLog;
  public_key: public_key;
  public_key_hash: string;
  uuid: string
}

val write_public_key :
  Bi_outbuf.t -> public_key -> unit
  (** Output a JSON value of type {!public_key}. *)

val string_of_public_key :
  ?len:int -> public_key -> string
  (** Serialize a value of type {!public_key}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_public_key :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> public_key
  (** Input JSON data of type {!public_key}. *)

val public_key_of_string :
  string -> public_key
  (** Deserialize JSON data of type {!public_key}. *)

val write_proofDLog :
  Bi_outbuf.t -> proofDLog -> unit
  (** Output a JSON value of type {!proofDLog}. *)

val string_of_proofDLog :
  ?len:int -> proofDLog -> string
  (** Serialize a value of type {!proofDLog}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_proofDLog :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> proofDLog
  (** Input JSON data of type {!proofDLog}. *)

val proofDLog_of_string :
  string -> proofDLog
  (** Deserialize JSON data of type {!proofDLog}. *)

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

val write_authority :
  Bi_outbuf.t -> authority -> unit
  (** Output a JSON value of type {!authority}. *)

val string_of_authority :
  ?len:int -> authority -> string
  (** Serialize a value of type {!authority}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_authority :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> authority
  (** Input JSON data of type {!authority}. *)

val authority_of_string :
  string -> authority
  (** Deserialize JSON data of type {!authority}. *)

