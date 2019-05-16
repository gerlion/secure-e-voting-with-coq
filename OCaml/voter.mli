(* Auto-generated from "voter.atd" *)


type commitment = { a: string; b: string }

type proof = { challenge: string; commitment: commitment; response: string }

type choice = {
  choice_alpha (*atd alpha *): string;
  choice_beta (*atd beta *): string
}

type answer = {
  choices: choice list;
  individual_proofs: proof list list;
  overall_proof: string
}

type voter = {
  answers: answer list;
  election_hash: string;
  election_uuid: string
}

(* Writers for type commitment *)

val commitment_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!commitment}.
      Readers may support more than just this tag. *)

val write_untagged_commitment :
  Bi_outbuf.t -> commitment -> unit
  (** Output an untagged biniou value of type {!commitment}. *)

val write_commitment :
  Bi_outbuf.t -> commitment -> unit
  (** Output a biniou value of type {!commitment}. *)

val string_of_commitment :
  ?len:int -> commitment -> string
  (** Serialize a value of type {!commitment} into
      a biniou string. *)

(* Readers for type commitment *)

val get_commitment_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> commitment)
  (** Return a function that reads an untagged
      biniou value of type {!commitment}. *)

val read_commitment :
  Bi_inbuf.t -> commitment
  (** Input a tagged biniou value of type {!commitment}. *)

val commitment_of_string :
  ?pos:int -> string -> commitment
  (** Deserialize a biniou value of type {!commitment}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

val create_commitment :
  a: string ->
  b: string ->
  unit -> commitment
  (** Create a record of type {!commitment}. *)


(* Writers for type proof *)

val proof_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!proof}.
      Readers may support more than just this tag. *)

val write_untagged_proof :
  Bi_outbuf.t -> proof -> unit
  (** Output an untagged biniou value of type {!proof}. *)

val write_proof :
  Bi_outbuf.t -> proof -> unit
  (** Output a biniou value of type {!proof}. *)

val string_of_proof :
  ?len:int -> proof -> string
  (** Serialize a value of type {!proof} into
      a biniou string. *)

(* Readers for type proof *)

val get_proof_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> proof)
  (** Return a function that reads an untagged
      biniou value of type {!proof}. *)

val read_proof :
  Bi_inbuf.t -> proof
  (** Input a tagged biniou value of type {!proof}. *)

val proof_of_string :
  ?pos:int -> string -> proof
  (** Deserialize a biniou value of type {!proof}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

val create_proof :
  challenge: string ->
  commitment: commitment ->
  response: string ->
  unit -> proof
  (** Create a record of type {!proof}. *)


(* Writers for type choice *)

val choice_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!choice}.
      Readers may support more than just this tag. *)

val write_untagged_choice :
  Bi_outbuf.t -> choice -> unit
  (** Output an untagged biniou value of type {!choice}. *)

val write_choice :
  Bi_outbuf.t -> choice -> unit
  (** Output a biniou value of type {!choice}. *)

val string_of_choice :
  ?len:int -> choice -> string
  (** Serialize a value of type {!choice} into
      a biniou string. *)

(* Readers for type choice *)

val get_choice_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> choice)
  (** Return a function that reads an untagged
      biniou value of type {!choice}. *)

val read_choice :
  Bi_inbuf.t -> choice
  (** Input a tagged biniou value of type {!choice}. *)

val choice_of_string :
  ?pos:int -> string -> choice
  (** Deserialize a biniou value of type {!choice}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

val create_choice :
  choice_alpha: string ->
  choice_beta: string ->
  unit -> choice
  (** Create a record of type {!choice}. *)


(* Writers for type answer *)

val answer_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!answer}.
      Readers may support more than just this tag. *)

val write_untagged_answer :
  Bi_outbuf.t -> answer -> unit
  (** Output an untagged biniou value of type {!answer}. *)

val write_answer :
  Bi_outbuf.t -> answer -> unit
  (** Output a biniou value of type {!answer}. *)

val string_of_answer :
  ?len:int -> answer -> string
  (** Serialize a value of type {!answer} into
      a biniou string. *)

(* Readers for type answer *)

val get_answer_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> answer)
  (** Return a function that reads an untagged
      biniou value of type {!answer}. *)

val read_answer :
  Bi_inbuf.t -> answer
  (** Input a tagged biniou value of type {!answer}. *)

val answer_of_string :
  ?pos:int -> string -> answer
  (** Deserialize a biniou value of type {!answer}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

val create_answer :
  choices: choice list ->
  individual_proofs: proof list list ->
  overall_proof: string ->
  unit -> answer
  (** Create a record of type {!answer}. *)


(* Writers for type voter *)

val voter_tag : Bi_io.node_tag
  (** Tag used by the writers for type {!voter}.
      Readers may support more than just this tag. *)

val write_untagged_voter :
  Bi_outbuf.t -> voter -> unit
  (** Output an untagged biniou value of type {!voter}. *)

val write_voter :
  Bi_outbuf.t -> voter -> unit
  (** Output a biniou value of type {!voter}. *)

val string_of_voter :
  ?len:int -> voter -> string
  (** Serialize a value of type {!voter} into
      a biniou string. *)

(* Readers for type voter *)

val get_voter_reader :
  Bi_io.node_tag -> (Bi_inbuf.t -> voter)
  (** Return a function that reads an untagged
      biniou value of type {!voter}. *)

val read_voter :
  Bi_inbuf.t -> voter
  (** Input a tagged biniou value of type {!voter}. *)

val voter_of_string :
  ?pos:int -> string -> voter
  (** Deserialize a biniou value of type {!voter}.
      @param pos specifies the position where
                 reading starts. Default: 0. *)

val create_voter :
  answers: answer list ->
  election_hash: string ->
  election_uuid: string ->
  unit -> voter
  (** Create a record of type {!voter}. *)


