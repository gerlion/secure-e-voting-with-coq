(* Auto-generated from "ElectionGuard.atd" *)
[@@@ocaml.warning "-27-32-35-39"]

type pkproof = ElectionGuard_t.pkproof = {
  commitment: string;
  challenge: string;
  response: string
}

type trustee_public_key = ElectionGuard_t.trustee_public_key = {
  public_key: string;
  proof: pkproof
}

type commitment = ElectionGuard_t.commitment = {
  public_key: string;
  ciphertext: string
}

type proof = ElectionGuard_t.proof = {
  commitment: commitment;
  challenge: string;
  response: string
}

type decproof = ElectionGuard_t.decproof = {
  recovery: string option;
  proof: proof;
  share: string
}

type ciphertext = ElectionGuard_t.ciphertext = {
  public_key: string;
  ciphertext: string
}

type spoil = ElectionGuard_t.spoil = {
  cleartext: string;
  decrypted_message: string;
  encrypted_message: ciphertext;
  shares: decproof list
}

type parameters = ElectionGuard_t.parameters = {
  date: string;
  location: string;
  num_trustees: string;
  threshold: string;
  prime: string;
  generator: string
}

type message = ElectionGuard_t.message = {
  message: ciphertext;
  zero_proof: proof;
  one_proof: proof
}

type decrypt = ElectionGuard_t.decrypt = {
  cleartext: string;
  decrypted_tally: string;
  encrypted_tally: ciphertext;
  shares: decproof list
}

type contest = ElectionGuard_t.contest = {
  selections: message list;
  max_selections: string;
  num_selections_proof: proof
}

type ballot_info = ElectionGuard_t.ballot_info = {
  date: string;
  device_info: string;
  time: string;
  tracker: string
}

type ballotspoiled = ElectionGuard_t.ballotspoiled = {
  ballot_info: ballot_info;
  contests: spoil list list
}

type ballot = ElectionGuard_t.ballot = {
  ballot_info: ballot_info;
  contests: contest list
}

type election = ElectionGuard_t.election = {
  parameters: parameters;
  base_hash: string;
  trustee_public_keys: trustee_public_key list list;
  joint_public_key: string;
  extended_base_hash: string;
  cast_ballots: ballot list;
  contest_tallies: decrypt list list;
  spoiled_ballots: ballotspoiled list
}

val write_pkproof :
  Bi_outbuf.t -> pkproof -> unit
  (** Output a JSON value of type {!pkproof}. *)

val string_of_pkproof :
  ?len:int -> pkproof -> string
  (** Serialize a value of type {!pkproof}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_pkproof :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> pkproof
  (** Input JSON data of type {!pkproof}. *)

val pkproof_of_string :
  string -> pkproof
  (** Deserialize JSON data of type {!pkproof}. *)

val write_trustee_public_key :
  Bi_outbuf.t -> trustee_public_key -> unit
  (** Output a JSON value of type {!trustee_public_key}. *)

val string_of_trustee_public_key :
  ?len:int -> trustee_public_key -> string
  (** Serialize a value of type {!trustee_public_key}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_trustee_public_key :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> trustee_public_key
  (** Input JSON data of type {!trustee_public_key}. *)

val trustee_public_key_of_string :
  string -> trustee_public_key
  (** Deserialize JSON data of type {!trustee_public_key}. *)

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

val write_decproof :
  Bi_outbuf.t -> decproof -> unit
  (** Output a JSON value of type {!decproof}. *)

val string_of_decproof :
  ?len:int -> decproof -> string
  (** Serialize a value of type {!decproof}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_decproof :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> decproof
  (** Input JSON data of type {!decproof}. *)

val decproof_of_string :
  string -> decproof
  (** Deserialize JSON data of type {!decproof}. *)

val write_ciphertext :
  Bi_outbuf.t -> ciphertext -> unit
  (** Output a JSON value of type {!ciphertext}. *)

val string_of_ciphertext :
  ?len:int -> ciphertext -> string
  (** Serialize a value of type {!ciphertext}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_ciphertext :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> ciphertext
  (** Input JSON data of type {!ciphertext}. *)

val ciphertext_of_string :
  string -> ciphertext
  (** Deserialize JSON data of type {!ciphertext}. *)

val write_spoil :
  Bi_outbuf.t -> spoil -> unit
  (** Output a JSON value of type {!spoil}. *)

val string_of_spoil :
  ?len:int -> spoil -> string
  (** Serialize a value of type {!spoil}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_spoil :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> spoil
  (** Input JSON data of type {!spoil}. *)

val spoil_of_string :
  string -> spoil
  (** Deserialize JSON data of type {!spoil}. *)

val write_parameters :
  Bi_outbuf.t -> parameters -> unit
  (** Output a JSON value of type {!parameters}. *)

val string_of_parameters :
  ?len:int -> parameters -> string
  (** Serialize a value of type {!parameters}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_parameters :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> parameters
  (** Input JSON data of type {!parameters}. *)

val parameters_of_string :
  string -> parameters
  (** Deserialize JSON data of type {!parameters}. *)

val write_message :
  Bi_outbuf.t -> message -> unit
  (** Output a JSON value of type {!message}. *)

val string_of_message :
  ?len:int -> message -> string
  (** Serialize a value of type {!message}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_message :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> message
  (** Input JSON data of type {!message}. *)

val message_of_string :
  string -> message
  (** Deserialize JSON data of type {!message}. *)

val write_decrypt :
  Bi_outbuf.t -> decrypt -> unit
  (** Output a JSON value of type {!decrypt}. *)

val string_of_decrypt :
  ?len:int -> decrypt -> string
  (** Serialize a value of type {!decrypt}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_decrypt :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> decrypt
  (** Input JSON data of type {!decrypt}. *)

val decrypt_of_string :
  string -> decrypt
  (** Deserialize JSON data of type {!decrypt}. *)

val write_contest :
  Bi_outbuf.t -> contest -> unit
  (** Output a JSON value of type {!contest}. *)

val string_of_contest :
  ?len:int -> contest -> string
  (** Serialize a value of type {!contest}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_contest :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> contest
  (** Input JSON data of type {!contest}. *)

val contest_of_string :
  string -> contest
  (** Deserialize JSON data of type {!contest}. *)

val write_ballot_info :
  Bi_outbuf.t -> ballot_info -> unit
  (** Output a JSON value of type {!ballot_info}. *)

val string_of_ballot_info :
  ?len:int -> ballot_info -> string
  (** Serialize a value of type {!ballot_info}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_ballot_info :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> ballot_info
  (** Input JSON data of type {!ballot_info}. *)

val ballot_info_of_string :
  string -> ballot_info
  (** Deserialize JSON data of type {!ballot_info}. *)

val write_ballotspoiled :
  Bi_outbuf.t -> ballotspoiled -> unit
  (** Output a JSON value of type {!ballotspoiled}. *)

val string_of_ballotspoiled :
  ?len:int -> ballotspoiled -> string
  (** Serialize a value of type {!ballotspoiled}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_ballotspoiled :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> ballotspoiled
  (** Input JSON data of type {!ballotspoiled}. *)

val ballotspoiled_of_string :
  string -> ballotspoiled
  (** Deserialize JSON data of type {!ballotspoiled}. *)

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

val write_election :
  Bi_outbuf.t -> election -> unit
  (** Output a JSON value of type {!election}. *)

val string_of_election :
  ?len:int -> election -> string
  (** Serialize a value of type {!election}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_election :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> election
  (** Input JSON data of type {!election}. *)

val election_of_string :
  string -> election
  (** Deserialize JSON data of type {!election}. *)

