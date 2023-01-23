(* Auto-generated from "proof.atd" *)
[@@@ocaml.warning "-27-32-33-35-39"]

type zero_argument = Proof_t.zero_argument = {
  c_a0: string;
  c_bm: string;
  c_d: string list;
  a: string list;
  b: string list;
  r: string;
  s: string;
  t: string
}

type ciphertext = Proof_t.ciphertext = { gamma: string; phis: string list }

type statement = Proof_t.statement = {
  ciphertexts: ciphertext list;
  shuffled_ciphertexts: ciphertext list
}

type singe_vpa = Proof_t.singe_vpa = {
  c_d: string;
  c_lower_delta: string;
  c_upper_delta: string;
  a_tilde: string list;
  b_tilde: string list;
  r_tilde: string;
  s_tilde: string
}

type hadamard_argument = Proof_t.hadamard_argument = {
  cUpperB: string list;
  zero_argument: zero_argument
}

type prod_arg = Proof_t.prod_arg = {
  c_b: string option;
  hadamard_argument: hadamard_argument option;
  single_vpa: singe_vpa
}

type multi_exp_arg = Proof_t.multi_exp_arg = {
  c_a_0: string;
  c_b: string list;
  e: ciphertext list;
  a: string list;
  r: string;
  b: string;
  s: string;
  tau: string
}

type argument = Proof_t.argument = {
  ca: string list;
  cb: string list;
  product_argument: prod_arg;
  multi_exp_argument: multi_exp_arg
}

type input = Proof_t.input = { statement: statement; argument: argument }

type comkey = Proof_t.comkey = { h: string; g: string list }

type context = Proof_t.context = {
  p: string;
  q: string;
  g: string;
  pk: string list;
  ck: comkey
}

type proof = Proof_t.proof = {
  description: string;
  context: context;
  input: input;
  output: bool
}

val write_zero_argument :
  Bi_outbuf.t -> zero_argument -> unit
  (** Output a JSON value of type {!zero_argument}. *)

val string_of_zero_argument :
  ?len:int -> zero_argument -> string
  (** Serialize a value of type {!zero_argument}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_zero_argument :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> zero_argument
  (** Input JSON data of type {!zero_argument}. *)

val zero_argument_of_string :
  string -> zero_argument
  (** Deserialize JSON data of type {!zero_argument}. *)

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

val write_statement :
  Bi_outbuf.t -> statement -> unit
  (** Output a JSON value of type {!statement}. *)

val string_of_statement :
  ?len:int -> statement -> string
  (** Serialize a value of type {!statement}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_statement :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> statement
  (** Input JSON data of type {!statement}. *)

val statement_of_string :
  string -> statement
  (** Deserialize JSON data of type {!statement}. *)

val write_singe_vpa :
  Bi_outbuf.t -> singe_vpa -> unit
  (** Output a JSON value of type {!singe_vpa}. *)

val string_of_singe_vpa :
  ?len:int -> singe_vpa -> string
  (** Serialize a value of type {!singe_vpa}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_singe_vpa :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> singe_vpa
  (** Input JSON data of type {!singe_vpa}. *)

val singe_vpa_of_string :
  string -> singe_vpa
  (** Deserialize JSON data of type {!singe_vpa}. *)

val write_hadamard_argument :
  Bi_outbuf.t -> hadamard_argument -> unit
  (** Output a JSON value of type {!hadamard_argument}. *)

val string_of_hadamard_argument :
  ?len:int -> hadamard_argument -> string
  (** Serialize a value of type {!hadamard_argument}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_hadamard_argument :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> hadamard_argument
  (** Input JSON data of type {!hadamard_argument}. *)

val hadamard_argument_of_string :
  string -> hadamard_argument
  (** Deserialize JSON data of type {!hadamard_argument}. *)

val write_prod_arg :
  Bi_outbuf.t -> prod_arg -> unit
  (** Output a JSON value of type {!prod_arg}. *)

val string_of_prod_arg :
  ?len:int -> prod_arg -> string
  (** Serialize a value of type {!prod_arg}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_prod_arg :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> prod_arg
  (** Input JSON data of type {!prod_arg}. *)

val prod_arg_of_string :
  string -> prod_arg
  (** Deserialize JSON data of type {!prod_arg}. *)

val write_multi_exp_arg :
  Bi_outbuf.t -> multi_exp_arg -> unit
  (** Output a JSON value of type {!multi_exp_arg}. *)

val string_of_multi_exp_arg :
  ?len:int -> multi_exp_arg -> string
  (** Serialize a value of type {!multi_exp_arg}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_multi_exp_arg :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> multi_exp_arg
  (** Input JSON data of type {!multi_exp_arg}. *)

val multi_exp_arg_of_string :
  string -> multi_exp_arg
  (** Deserialize JSON data of type {!multi_exp_arg}. *)

val write_argument :
  Bi_outbuf.t -> argument -> unit
  (** Output a JSON value of type {!argument}. *)

val string_of_argument :
  ?len:int -> argument -> string
  (** Serialize a value of type {!argument}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_argument :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> argument
  (** Input JSON data of type {!argument}. *)

val argument_of_string :
  string -> argument
  (** Deserialize JSON data of type {!argument}. *)

val write_input :
  Bi_outbuf.t -> input -> unit
  (** Output a JSON value of type {!input}. *)

val string_of_input :
  ?len:int -> input -> string
  (** Serialize a value of type {!input}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_input :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> input
  (** Input JSON data of type {!input}. *)

val input_of_string :
  string -> input
  (** Deserialize JSON data of type {!input}. *)

val write_comkey :
  Bi_outbuf.t -> comkey -> unit
  (** Output a JSON value of type {!comkey}. *)

val string_of_comkey :
  ?len:int -> comkey -> string
  (** Serialize a value of type {!comkey}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_comkey :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> comkey
  (** Input JSON data of type {!comkey}. *)

val comkey_of_string :
  string -> comkey
  (** Deserialize JSON data of type {!comkey}. *)

val write_context :
  Bi_outbuf.t -> context -> unit
  (** Output a JSON value of type {!context}. *)

val string_of_context :
  ?len:int -> context -> string
  (** Serialize a value of type {!context}
      into a JSON string.
      @param len specifies the initial length
                 of the buffer used internally.
                 Default: 1024. *)

val read_context :
  Yojson.Safe.lexer_state -> Lexing.lexbuf -> context
  (** Input JSON data of type {!context}. *)

val context_of_string :
  string -> context
  (** Deserialize JSON data of type {!context}. *)

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

