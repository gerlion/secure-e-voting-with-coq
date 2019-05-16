(* Auto-generated from "voterlist.atd" *)
[@@@ocaml.warning "-27-32-35-39"]

type voterid = Voterlist_t.voterid = {
  alias: string;
  election_uuid: string;
  uuid: string
}

val write_voterid :
  Bi_outbuf.t -> voterid -> unit
  (** Output a JSON value of type {!voterid}. *)

val string_of_voterid :
  ?len:int -> voterid -> string
  (** Serialize a value of type {!voterid}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_voterid :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> voterid
  (** Input JSON data of type {!voterid}. *)

val voterid_of_string :
  string -> voterid
  (** Deserialize JSON data of type {!voterid}. *)

