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

let write__1 = (
  Atdgen_runtime.Oj_run.write_list (
    Yojson.Safe.write_string
  )
)
let string_of__1 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__1 ob x;
  Bi_outbuf.contents ob
let read__1 = (
  Atdgen_runtime.Oj_run.read_list (
    Atdgen_runtime.Oj_run.read_string
  )
)
let _1_of_string s =
  read__1 (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_zero_argument : _ -> zero_argument -> _ = (
  fun ob (x : zero_argument) ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"c_a0\":";
    (
      Yojson.Safe.write_string
    )
      ob x.c_a0;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"c_bm\":";
    (
      Yojson.Safe.write_string
    )
      ob x.c_bm;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"c_d\":";
    (
      write__1
    )
      ob x.c_d;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"a\":";
    (
      write__1
    )
      ob x.a;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"b\":";
    (
      write__1
    )
      ob x.b;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"r\":";
    (
      Yojson.Safe.write_string
    )
      ob x.r;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"s\":";
    (
      Yojson.Safe.write_string
    )
      ob x.s;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"t\":";
    (
      Yojson.Safe.write_string
    )
      ob x.t;
    Bi_outbuf.add_char ob '}';
)
let string_of_zero_argument ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_zero_argument ob x;
  Bi_outbuf.contents ob
let read_zero_argument = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_c_a0 = ref (None) in
    let field_c_bm = ref (None) in
    let field_c_d = ref (None) in
    let field_a = ref (None) in
    let field_b = ref (None) in
    let field_r = ref (None) in
    let field_s = ref (None) in
    let field_t = ref (None) in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 1 -> (
                match String.unsafe_get s pos with
                  | 'a' -> (
                      3
                    )
                  | 'b' -> (
                      4
                    )
                  | 'r' -> (
                      5
                    )
                  | 's' -> (
                      6
                    )
                  | 't' -> (
                      7
                    )
                  | _ -> (
                      -1
                    )
              )
            | 3 -> (
                if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 'd' then (
                  2
                )
                else (
                  -1
                )
              )
            | 4 -> (
                if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = '_' then (
                  match String.unsafe_get s (pos+2) with
                    | 'a' -> (
                        if String.unsafe_get s (pos+3) = '0' then (
                          0
                        )
                        else (
                          -1
                        )
                      )
                    | 'b' -> (
                        if String.unsafe_get s (pos+3) = 'm' then (
                          1
                        )
                        else (
                          -1
                        )
                      )
                    | _ -> (
                        -1
                      )
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Atdgen_runtime.Oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_c_a0 := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 1 ->
            field_c_bm := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 2 ->
            field_c_d := (
              Some (
                (
                  read__1
                ) p lb
              )
            );
          | 3 ->
            field_a := (
              Some (
                (
                  read__1
                ) p lb
              )
            );
          | 4 ->
            field_b := (
              Some (
                (
                  read__1
                ) p lb
              )
            );
          | 5 ->
            field_r := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 6 ->
            field_s := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 7 ->
            field_t := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 1 -> (
                  match String.unsafe_get s pos with
                    | 'a' -> (
                        3
                      )
                    | 'b' -> (
                        4
                      )
                    | 'r' -> (
                        5
                      )
                    | 's' -> (
                        6
                      )
                    | 't' -> (
                        7
                      )
                    | _ -> (
                        -1
                      )
                )
              | 3 -> (
                  if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 'd' then (
                    2
                  )
                  else (
                    -1
                  )
                )
              | 4 -> (
                  if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = '_' then (
                    match String.unsafe_get s (pos+2) with
                      | 'a' -> (
                          if String.unsafe_get s (pos+3) = '0' then (
                            0
                          )
                          else (
                            -1
                          )
                        )
                      | 'b' -> (
                          if String.unsafe_get s (pos+3) = 'm' then (
                            1
                          )
                          else (
                            -1
                          )
                        )
                      | _ -> (
                          -1
                        )
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Atdgen_runtime.Oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_c_a0 := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 1 ->
              field_c_bm := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 2 ->
              field_c_d := (
                Some (
                  (
                    read__1
                  ) p lb
                )
              );
            | 3 ->
              field_a := (
                Some (
                  (
                    read__1
                  ) p lb
                )
              );
            | 4 ->
              field_b := (
                Some (
                  (
                    read__1
                  ) p lb
                )
              );
            | 5 ->
              field_r := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 6 ->
              field_s := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 7 ->
              field_t := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        (
          {
            c_a0 = (match !field_c_a0 with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "c_a0");
            c_bm = (match !field_c_bm with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "c_bm");
            c_d = (match !field_c_d with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "c_d");
            a = (match !field_a with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "a");
            b = (match !field_b with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "b");
            r = (match !field_r with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "r");
            s = (match !field_s with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "s");
            t = (match !field_t with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "t");
          }
         : zero_argument)
      )
)
let zero_argument_of_string s =
  read_zero_argument (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_ciphertext : _ -> ciphertext -> _ = (
  fun ob (x : ciphertext) ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"gamma\":";
    (
      Yojson.Safe.write_string
    )
      ob x.gamma;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"phis\":";
    (
      write__1
    )
      ob x.phis;
    Bi_outbuf.add_char ob '}';
)
let string_of_ciphertext ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_ciphertext ob x;
  Bi_outbuf.contents ob
let read_ciphertext = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_gamma = ref (None) in
    let field_phis = ref (None) in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 4 -> (
                if String.unsafe_get s pos = 'p' && String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 'i' && String.unsafe_get s (pos+3) = 's' then (
                  1
                )
                else (
                  -1
                )
              )
            | 5 -> (
                if String.unsafe_get s pos = 'g' && String.unsafe_get s (pos+1) = 'a' && String.unsafe_get s (pos+2) = 'm' && String.unsafe_get s (pos+3) = 'm' && String.unsafe_get s (pos+4) = 'a' then (
                  0
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Atdgen_runtime.Oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_gamma := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 1 ->
            field_phis := (
              Some (
                (
                  read__1
                ) p lb
              )
            );
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 4 -> (
                  if String.unsafe_get s pos = 'p' && String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 'i' && String.unsafe_get s (pos+3) = 's' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | 5 -> (
                  if String.unsafe_get s pos = 'g' && String.unsafe_get s (pos+1) = 'a' && String.unsafe_get s (pos+2) = 'm' && String.unsafe_get s (pos+3) = 'm' && String.unsafe_get s (pos+4) = 'a' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Atdgen_runtime.Oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_gamma := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 1 ->
              field_phis := (
                Some (
                  (
                    read__1
                  ) p lb
                )
              );
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        (
          {
            gamma = (match !field_gamma with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "gamma");
            phis = (match !field_phis with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "phis");
          }
         : ciphertext)
      )
)
let ciphertext_of_string s =
  read_ciphertext (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write__2 = (
  Atdgen_runtime.Oj_run.write_list (
    write_ciphertext
  )
)
let string_of__2 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__2 ob x;
  Bi_outbuf.contents ob
let read__2 = (
  Atdgen_runtime.Oj_run.read_list (
    read_ciphertext
  )
)
let _2_of_string s =
  read__2 (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_statement : _ -> statement -> _ = (
  fun ob (x : statement) ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"ciphertexts\":";
    (
      write__2
    )
      ob x.ciphertexts;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"shuffled_ciphertexts\":";
    (
      write__2
    )
      ob x.shuffled_ciphertexts;
    Bi_outbuf.add_char ob '}';
)
let string_of_statement ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_statement ob x;
  Bi_outbuf.contents ob
let read_statement = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_ciphertexts = ref (None) in
    let field_shuffled_ciphertexts = ref (None) in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 11 -> (
                if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = 'i' && String.unsafe_get s (pos+2) = 'p' && String.unsafe_get s (pos+3) = 'h' && String.unsafe_get s (pos+4) = 'e' && String.unsafe_get s (pos+5) = 'r' && String.unsafe_get s (pos+6) = 't' && String.unsafe_get s (pos+7) = 'e' && String.unsafe_get s (pos+8) = 'x' && String.unsafe_get s (pos+9) = 't' && String.unsafe_get s (pos+10) = 's' then (
                  0
                )
                else (
                  -1
                )
              )
            | 20 -> (
                if String.unsafe_get s pos = 's' && String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 'u' && String.unsafe_get s (pos+3) = 'f' && String.unsafe_get s (pos+4) = 'f' && String.unsafe_get s (pos+5) = 'l' && String.unsafe_get s (pos+6) = 'e' && String.unsafe_get s (pos+7) = 'd' && String.unsafe_get s (pos+8) = '_' && String.unsafe_get s (pos+9) = 'c' && String.unsafe_get s (pos+10) = 'i' && String.unsafe_get s (pos+11) = 'p' && String.unsafe_get s (pos+12) = 'h' && String.unsafe_get s (pos+13) = 'e' && String.unsafe_get s (pos+14) = 'r' && String.unsafe_get s (pos+15) = 't' && String.unsafe_get s (pos+16) = 'e' && String.unsafe_get s (pos+17) = 'x' && String.unsafe_get s (pos+18) = 't' && String.unsafe_get s (pos+19) = 's' then (
                  1
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Atdgen_runtime.Oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_ciphertexts := (
              Some (
                (
                  read__2
                ) p lb
              )
            );
          | 1 ->
            field_shuffled_ciphertexts := (
              Some (
                (
                  read__2
                ) p lb
              )
            );
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 11 -> (
                  if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = 'i' && String.unsafe_get s (pos+2) = 'p' && String.unsafe_get s (pos+3) = 'h' && String.unsafe_get s (pos+4) = 'e' && String.unsafe_get s (pos+5) = 'r' && String.unsafe_get s (pos+6) = 't' && String.unsafe_get s (pos+7) = 'e' && String.unsafe_get s (pos+8) = 'x' && String.unsafe_get s (pos+9) = 't' && String.unsafe_get s (pos+10) = 's' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | 20 -> (
                  if String.unsafe_get s pos = 's' && String.unsafe_get s (pos+1) = 'h' && String.unsafe_get s (pos+2) = 'u' && String.unsafe_get s (pos+3) = 'f' && String.unsafe_get s (pos+4) = 'f' && String.unsafe_get s (pos+5) = 'l' && String.unsafe_get s (pos+6) = 'e' && String.unsafe_get s (pos+7) = 'd' && String.unsafe_get s (pos+8) = '_' && String.unsafe_get s (pos+9) = 'c' && String.unsafe_get s (pos+10) = 'i' && String.unsafe_get s (pos+11) = 'p' && String.unsafe_get s (pos+12) = 'h' && String.unsafe_get s (pos+13) = 'e' && String.unsafe_get s (pos+14) = 'r' && String.unsafe_get s (pos+15) = 't' && String.unsafe_get s (pos+16) = 'e' && String.unsafe_get s (pos+17) = 'x' && String.unsafe_get s (pos+18) = 't' && String.unsafe_get s (pos+19) = 's' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Atdgen_runtime.Oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_ciphertexts := (
                Some (
                  (
                    read__2
                  ) p lb
                )
              );
            | 1 ->
              field_shuffled_ciphertexts := (
                Some (
                  (
                    read__2
                  ) p lb
                )
              );
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        (
          {
            ciphertexts = (match !field_ciphertexts with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "ciphertexts");
            shuffled_ciphertexts = (match !field_shuffled_ciphertexts with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "shuffled_ciphertexts");
          }
         : statement)
      )
)
let statement_of_string s =
  read_statement (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_singe_vpa : _ -> singe_vpa -> _ = (
  fun ob (x : singe_vpa) ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"c_d\":";
    (
      Yojson.Safe.write_string
    )
      ob x.c_d;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"c_lower_delta\":";
    (
      Yojson.Safe.write_string
    )
      ob x.c_lower_delta;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"c_upper_delta\":";
    (
      Yojson.Safe.write_string
    )
      ob x.c_upper_delta;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"a_tilde\":";
    (
      write__1
    )
      ob x.a_tilde;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"b_tilde\":";
    (
      write__1
    )
      ob x.b_tilde;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"r_tilde\":";
    (
      Yojson.Safe.write_string
    )
      ob x.r_tilde;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"s_tilde\":";
    (
      Yojson.Safe.write_string
    )
      ob x.s_tilde;
    Bi_outbuf.add_char ob '}';
)
let string_of_singe_vpa ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_singe_vpa ob x;
  Bi_outbuf.contents ob
let read_singe_vpa = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_c_d = ref (None) in
    let field_c_lower_delta = ref (None) in
    let field_c_upper_delta = ref (None) in
    let field_a_tilde = ref (None) in
    let field_b_tilde = ref (None) in
    let field_r_tilde = ref (None) in
    let field_s_tilde = ref (None) in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 3 -> (
                if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 'd' then (
                  0
                )
                else (
                  -1
                )
              )
            | 7 -> (
                match String.unsafe_get s pos with
                  | 'a' -> (
                      if String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'd' && String.unsafe_get s (pos+6) = 'e' then (
                        3
                      )
                      else (
                        -1
                      )
                    )
                  | 'b' -> (
                      if String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'd' && String.unsafe_get s (pos+6) = 'e' then (
                        4
                      )
                      else (
                        -1
                      )
                    )
                  | 'r' -> (
                      if String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'd' && String.unsafe_get s (pos+6) = 'e' then (
                        5
                      )
                      else (
                        -1
                      )
                    )
                  | 's' -> (
                      if String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'd' && String.unsafe_get s (pos+6) = 'e' then (
                        6
                      )
                      else (
                        -1
                      )
                    )
                  | _ -> (
                      -1
                    )
              )
            | 13 -> (
                if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = '_' then (
                  match String.unsafe_get s (pos+2) with
                    | 'l' -> (
                        if String.unsafe_get s (pos+3) = 'o' && String.unsafe_get s (pos+4) = 'w' && String.unsafe_get s (pos+5) = 'e' && String.unsafe_get s (pos+6) = 'r' && String.unsafe_get s (pos+7) = '_' && String.unsafe_get s (pos+8) = 'd' && String.unsafe_get s (pos+9) = 'e' && String.unsafe_get s (pos+10) = 'l' && String.unsafe_get s (pos+11) = 't' && String.unsafe_get s (pos+12) = 'a' then (
                          1
                        )
                        else (
                          -1
                        )
                      )
                    | 'u' -> (
                        if String.unsafe_get s (pos+3) = 'p' && String.unsafe_get s (pos+4) = 'p' && String.unsafe_get s (pos+5) = 'e' && String.unsafe_get s (pos+6) = 'r' && String.unsafe_get s (pos+7) = '_' && String.unsafe_get s (pos+8) = 'd' && String.unsafe_get s (pos+9) = 'e' && String.unsafe_get s (pos+10) = 'l' && String.unsafe_get s (pos+11) = 't' && String.unsafe_get s (pos+12) = 'a' then (
                          2
                        )
                        else (
                          -1
                        )
                      )
                    | _ -> (
                        -1
                      )
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Atdgen_runtime.Oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_c_d := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 1 ->
            field_c_lower_delta := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 2 ->
            field_c_upper_delta := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 3 ->
            field_a_tilde := (
              Some (
                (
                  read__1
                ) p lb
              )
            );
          | 4 ->
            field_b_tilde := (
              Some (
                (
                  read__1
                ) p lb
              )
            );
          | 5 ->
            field_r_tilde := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 6 ->
            field_s_tilde := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 3 -> (
                  if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 'd' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | 7 -> (
                  match String.unsafe_get s pos with
                    | 'a' -> (
                        if String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'd' && String.unsafe_get s (pos+6) = 'e' then (
                          3
                        )
                        else (
                          -1
                        )
                      )
                    | 'b' -> (
                        if String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'd' && String.unsafe_get s (pos+6) = 'e' then (
                          4
                        )
                        else (
                          -1
                        )
                      )
                    | 'r' -> (
                        if String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'd' && String.unsafe_get s (pos+6) = 'e' then (
                          5
                        )
                        else (
                          -1
                        )
                      )
                    | 's' -> (
                        if String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'i' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'd' && String.unsafe_get s (pos+6) = 'e' then (
                          6
                        )
                        else (
                          -1
                        )
                      )
                    | _ -> (
                        -1
                      )
                )
              | 13 -> (
                  if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = '_' then (
                    match String.unsafe_get s (pos+2) with
                      | 'l' -> (
                          if String.unsafe_get s (pos+3) = 'o' && String.unsafe_get s (pos+4) = 'w' && String.unsafe_get s (pos+5) = 'e' && String.unsafe_get s (pos+6) = 'r' && String.unsafe_get s (pos+7) = '_' && String.unsafe_get s (pos+8) = 'd' && String.unsafe_get s (pos+9) = 'e' && String.unsafe_get s (pos+10) = 'l' && String.unsafe_get s (pos+11) = 't' && String.unsafe_get s (pos+12) = 'a' then (
                            1
                          )
                          else (
                            -1
                          )
                        )
                      | 'u' -> (
                          if String.unsafe_get s (pos+3) = 'p' && String.unsafe_get s (pos+4) = 'p' && String.unsafe_get s (pos+5) = 'e' && String.unsafe_get s (pos+6) = 'r' && String.unsafe_get s (pos+7) = '_' && String.unsafe_get s (pos+8) = 'd' && String.unsafe_get s (pos+9) = 'e' && String.unsafe_get s (pos+10) = 'l' && String.unsafe_get s (pos+11) = 't' && String.unsafe_get s (pos+12) = 'a' then (
                            2
                          )
                          else (
                            -1
                          )
                        )
                      | _ -> (
                          -1
                        )
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Atdgen_runtime.Oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_c_d := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 1 ->
              field_c_lower_delta := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 2 ->
              field_c_upper_delta := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 3 ->
              field_a_tilde := (
                Some (
                  (
                    read__1
                  ) p lb
                )
              );
            | 4 ->
              field_b_tilde := (
                Some (
                  (
                    read__1
                  ) p lb
                )
              );
            | 5 ->
              field_r_tilde := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 6 ->
              field_s_tilde := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        (
          {
            c_d = (match !field_c_d with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "c_d");
            c_lower_delta = (match !field_c_lower_delta with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "c_lower_delta");
            c_upper_delta = (match !field_c_upper_delta with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "c_upper_delta");
            a_tilde = (match !field_a_tilde with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "a_tilde");
            b_tilde = (match !field_b_tilde with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "b_tilde");
            r_tilde = (match !field_r_tilde with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "r_tilde");
            s_tilde = (match !field_s_tilde with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "s_tilde");
          }
         : singe_vpa)
      )
)
let singe_vpa_of_string s =
  read_singe_vpa (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_hadamard_argument : _ -> hadamard_argument -> _ = (
  fun ob (x : hadamard_argument) ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"cUpperB\":";
    (
      write__1
    )
      ob x.cUpperB;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"zero_argument\":";
    (
      write_zero_argument
    )
      ob x.zero_argument;
    Bi_outbuf.add_char ob '}';
)
let string_of_hadamard_argument ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_hadamard_argument ob x;
  Bi_outbuf.contents ob
let read_hadamard_argument = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_cUpperB = ref (None) in
    let field_zero_argument = ref (None) in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 7 -> (
                if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = 'U' && String.unsafe_get s (pos+2) = 'p' && String.unsafe_get s (pos+3) = 'p' && String.unsafe_get s (pos+4) = 'e' && String.unsafe_get s (pos+5) = 'r' && String.unsafe_get s (pos+6) = 'B' then (
                  0
                )
                else (
                  -1
                )
              )
            | 13 -> (
                if String.unsafe_get s pos = 'z' && String.unsafe_get s (pos+1) = 'e' && String.unsafe_get s (pos+2) = 'r' && String.unsafe_get s (pos+3) = 'o' && String.unsafe_get s (pos+4) = '_' && String.unsafe_get s (pos+5) = 'a' && String.unsafe_get s (pos+6) = 'r' && String.unsafe_get s (pos+7) = 'g' && String.unsafe_get s (pos+8) = 'u' && String.unsafe_get s (pos+9) = 'm' && String.unsafe_get s (pos+10) = 'e' && String.unsafe_get s (pos+11) = 'n' && String.unsafe_get s (pos+12) = 't' then (
                  1
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Atdgen_runtime.Oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_cUpperB := (
              Some (
                (
                  read__1
                ) p lb
              )
            );
          | 1 ->
            field_zero_argument := (
              Some (
                (
                  read_zero_argument
                ) p lb
              )
            );
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 7 -> (
                  if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = 'U' && String.unsafe_get s (pos+2) = 'p' && String.unsafe_get s (pos+3) = 'p' && String.unsafe_get s (pos+4) = 'e' && String.unsafe_get s (pos+5) = 'r' && String.unsafe_get s (pos+6) = 'B' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | 13 -> (
                  if String.unsafe_get s pos = 'z' && String.unsafe_get s (pos+1) = 'e' && String.unsafe_get s (pos+2) = 'r' && String.unsafe_get s (pos+3) = 'o' && String.unsafe_get s (pos+4) = '_' && String.unsafe_get s (pos+5) = 'a' && String.unsafe_get s (pos+6) = 'r' && String.unsafe_get s (pos+7) = 'g' && String.unsafe_get s (pos+8) = 'u' && String.unsafe_get s (pos+9) = 'm' && String.unsafe_get s (pos+10) = 'e' && String.unsafe_get s (pos+11) = 'n' && String.unsafe_get s (pos+12) = 't' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Atdgen_runtime.Oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_cUpperB := (
                Some (
                  (
                    read__1
                  ) p lb
                )
              );
            | 1 ->
              field_zero_argument := (
                Some (
                  (
                    read_zero_argument
                  ) p lb
                )
              );
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        (
          {
            cUpperB = (match !field_cUpperB with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "cUpperB");
            zero_argument = (match !field_zero_argument with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "zero_argument");
          }
         : hadamard_argument)
      )
)
let hadamard_argument_of_string s =
  read_hadamard_argument (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write__4 = (
  Atdgen_runtime.Oj_run.write_option (
    write_hadamard_argument
  )
)
let string_of__4 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__4 ob x;
  Bi_outbuf.contents ob
let read__4 = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    match Yojson.Safe.start_any_variant p lb with
      | `Edgy_bracket -> (
          match Yojson.Safe.read_ident p lb with
            | "None" ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (None : _ option)
            | "Some" ->
              Atdgen_runtime.Oj_run.read_until_field_value p lb;
              let x = (
                  read_hadamard_argument
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (Some x : _ option)
            | x ->
              Atdgen_runtime.Oj_run.invalid_variant_tag p x
        )
      | `Double_quote -> (
          match Yojson.Safe.finish_string p lb with
            | "None" ->
              (None : _ option)
            | x ->
              Atdgen_runtime.Oj_run.invalid_variant_tag p x
        )
      | `Square_bracket -> (
          match Atdgen_runtime.Oj_run.read_string p lb with
            | "Some" ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_comma p lb;
              Yojson.Safe.read_space p lb;
              let x = (
                  read_hadamard_argument
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_rbr p lb;
              (Some x : _ option)
            | x ->
              Atdgen_runtime.Oj_run.invalid_variant_tag p x
        )
)
let _4_of_string s =
  read__4 (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write__3 = (
  Atdgen_runtime.Oj_run.write_option (
    Yojson.Safe.write_string
  )
)
let string_of__3 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__3 ob x;
  Bi_outbuf.contents ob
let read__3 = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    match Yojson.Safe.start_any_variant p lb with
      | `Edgy_bracket -> (
          match Yojson.Safe.read_ident p lb with
            | "None" ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (None : _ option)
            | "Some" ->
              Atdgen_runtime.Oj_run.read_until_field_value p lb;
              let x = (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_gt p lb;
              (Some x : _ option)
            | x ->
              Atdgen_runtime.Oj_run.invalid_variant_tag p x
        )
      | `Double_quote -> (
          match Yojson.Safe.finish_string p lb with
            | "None" ->
              (None : _ option)
            | x ->
              Atdgen_runtime.Oj_run.invalid_variant_tag p x
        )
      | `Square_bracket -> (
          match Atdgen_runtime.Oj_run.read_string p lb with
            | "Some" ->
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_comma p lb;
              Yojson.Safe.read_space p lb;
              let x = (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              in
              Yojson.Safe.read_space p lb;
              Yojson.Safe.read_rbr p lb;
              (Some x : _ option)
            | x ->
              Atdgen_runtime.Oj_run.invalid_variant_tag p x
        )
)
let _3_of_string s =
  read__3 (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_prod_arg : _ -> prod_arg -> _ = (
  fun ob (x : prod_arg) ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    (match x.c_b with None -> () | Some x ->
      if !is_first then
        is_first := false
      else
        Bi_outbuf.add_char ob ',';
      Bi_outbuf.add_string ob "\"c_b\":";
      (
        Yojson.Safe.write_string
      )
        ob x;
    );
    (match x.hadamard_argument with None -> () | Some x ->
      if !is_first then
        is_first := false
      else
        Bi_outbuf.add_char ob ',';
      Bi_outbuf.add_string ob "\"hadamard_argument\":";
      (
        write_hadamard_argument
      )
        ob x;
    );
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"single_vpa\":";
    (
      write_singe_vpa
    )
      ob x.single_vpa;
    Bi_outbuf.add_char ob '}';
)
let string_of_prod_arg ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_prod_arg ob x;
  Bi_outbuf.contents ob
let read_prod_arg = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_c_b = ref (None) in
    let field_hadamard_argument = ref (None) in
    let field_single_vpa = ref (None) in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 3 -> (
                if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 'b' then (
                  0
                )
                else (
                  -1
                )
              )
            | 10 -> (
                if String.unsafe_get s pos = 's' && String.unsafe_get s (pos+1) = 'i' && String.unsafe_get s (pos+2) = 'n' && String.unsafe_get s (pos+3) = 'g' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'e' && String.unsafe_get s (pos+6) = '_' && String.unsafe_get s (pos+7) = 'v' && String.unsafe_get s (pos+8) = 'p' && String.unsafe_get s (pos+9) = 'a' then (
                  2
                )
                else (
                  -1
                )
              )
            | 17 -> (
                if String.unsafe_get s pos = 'h' && String.unsafe_get s (pos+1) = 'a' && String.unsafe_get s (pos+2) = 'd' && String.unsafe_get s (pos+3) = 'a' && String.unsafe_get s (pos+4) = 'm' && String.unsafe_get s (pos+5) = 'a' && String.unsafe_get s (pos+6) = 'r' && String.unsafe_get s (pos+7) = 'd' && String.unsafe_get s (pos+8) = '_' && String.unsafe_get s (pos+9) = 'a' && String.unsafe_get s (pos+10) = 'r' && String.unsafe_get s (pos+11) = 'g' && String.unsafe_get s (pos+12) = 'u' && String.unsafe_get s (pos+13) = 'm' && String.unsafe_get s (pos+14) = 'e' && String.unsafe_get s (pos+15) = 'n' && String.unsafe_get s (pos+16) = 't' then (
                  1
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Atdgen_runtime.Oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            if not (Yojson.Safe.read_null_if_possible p lb) then (
              field_c_b := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            )
          | 1 ->
            if not (Yojson.Safe.read_null_if_possible p lb) then (
              field_hadamard_argument := (
                Some (
                  (
                    read_hadamard_argument
                  ) p lb
                )
              );
            )
          | 2 ->
            field_single_vpa := (
              Some (
                (
                  read_singe_vpa
                ) p lb
              )
            );
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 3 -> (
                  if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 'b' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | 10 -> (
                  if String.unsafe_get s pos = 's' && String.unsafe_get s (pos+1) = 'i' && String.unsafe_get s (pos+2) = 'n' && String.unsafe_get s (pos+3) = 'g' && String.unsafe_get s (pos+4) = 'l' && String.unsafe_get s (pos+5) = 'e' && String.unsafe_get s (pos+6) = '_' && String.unsafe_get s (pos+7) = 'v' && String.unsafe_get s (pos+8) = 'p' && String.unsafe_get s (pos+9) = 'a' then (
                    2
                  )
                  else (
                    -1
                  )
                )
              | 17 -> (
                  if String.unsafe_get s pos = 'h' && String.unsafe_get s (pos+1) = 'a' && String.unsafe_get s (pos+2) = 'd' && String.unsafe_get s (pos+3) = 'a' && String.unsafe_get s (pos+4) = 'm' && String.unsafe_get s (pos+5) = 'a' && String.unsafe_get s (pos+6) = 'r' && String.unsafe_get s (pos+7) = 'd' && String.unsafe_get s (pos+8) = '_' && String.unsafe_get s (pos+9) = 'a' && String.unsafe_get s (pos+10) = 'r' && String.unsafe_get s (pos+11) = 'g' && String.unsafe_get s (pos+12) = 'u' && String.unsafe_get s (pos+13) = 'm' && String.unsafe_get s (pos+14) = 'e' && String.unsafe_get s (pos+15) = 'n' && String.unsafe_get s (pos+16) = 't' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Atdgen_runtime.Oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              if not (Yojson.Safe.read_null_if_possible p lb) then (
                field_c_b := (
                  Some (
                    (
                      Atdgen_runtime.Oj_run.read_string
                    ) p lb
                  )
                );
              )
            | 1 ->
              if not (Yojson.Safe.read_null_if_possible p lb) then (
                field_hadamard_argument := (
                  Some (
                    (
                      read_hadamard_argument
                    ) p lb
                  )
                );
              )
            | 2 ->
              field_single_vpa := (
                Some (
                  (
                    read_singe_vpa
                  ) p lb
                )
              );
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        (
          {
            c_b = !field_c_b;
            hadamard_argument = !field_hadamard_argument;
            single_vpa = (match !field_single_vpa with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "single_vpa");
          }
         : prod_arg)
      )
)
let prod_arg_of_string s =
  read_prod_arg (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_multi_exp_arg : _ -> multi_exp_arg -> _ = (
  fun ob (x : multi_exp_arg) ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"c_a_0\":";
    (
      Yojson.Safe.write_string
    )
      ob x.c_a_0;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"c_b\":";
    (
      write__1
    )
      ob x.c_b;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"e\":";
    (
      write__2
    )
      ob x.e;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"a\":";
    (
      write__1
    )
      ob x.a;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"r\":";
    (
      Yojson.Safe.write_string
    )
      ob x.r;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"b\":";
    (
      Yojson.Safe.write_string
    )
      ob x.b;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"s\":";
    (
      Yojson.Safe.write_string
    )
      ob x.s;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"tau\":";
    (
      Yojson.Safe.write_string
    )
      ob x.tau;
    Bi_outbuf.add_char ob '}';
)
let string_of_multi_exp_arg ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_multi_exp_arg ob x;
  Bi_outbuf.contents ob
let read_multi_exp_arg = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_c_a_0 = ref (None) in
    let field_c_b = ref (None) in
    let field_e = ref (None) in
    let field_a = ref (None) in
    let field_r = ref (None) in
    let field_b = ref (None) in
    let field_s = ref (None) in
    let field_tau = ref (None) in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 1 -> (
                match String.unsafe_get s pos with
                  | 'a' -> (
                      3
                    )
                  | 'b' -> (
                      5
                    )
                  | 'e' -> (
                      2
                    )
                  | 'r' -> (
                      4
                    )
                  | 's' -> (
                      6
                    )
                  | _ -> (
                      -1
                    )
              )
            | 3 -> (
                match String.unsafe_get s pos with
                  | 'c' -> (
                      if String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 'b' then (
                        1
                      )
                      else (
                        -1
                      )
                    )
                  | 't' -> (
                      if String.unsafe_get s (pos+1) = 'a' && String.unsafe_get s (pos+2) = 'u' then (
                        7
                      )
                      else (
                        -1
                      )
                    )
                  | _ -> (
                      -1
                    )
              )
            | 5 -> (
                if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 'a' && String.unsafe_get s (pos+3) = '_' && String.unsafe_get s (pos+4) = '0' then (
                  0
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Atdgen_runtime.Oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_c_a_0 := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 1 ->
            field_c_b := (
              Some (
                (
                  read__1
                ) p lb
              )
            );
          | 2 ->
            field_e := (
              Some (
                (
                  read__2
                ) p lb
              )
            );
          | 3 ->
            field_a := (
              Some (
                (
                  read__1
                ) p lb
              )
            );
          | 4 ->
            field_r := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 5 ->
            field_b := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 6 ->
            field_s := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 7 ->
            field_tau := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 1 -> (
                  match String.unsafe_get s pos with
                    | 'a' -> (
                        3
                      )
                    | 'b' -> (
                        5
                      )
                    | 'e' -> (
                        2
                      )
                    | 'r' -> (
                        4
                      )
                    | 's' -> (
                        6
                      )
                    | _ -> (
                        -1
                      )
                )
              | 3 -> (
                  match String.unsafe_get s pos with
                    | 'c' -> (
                        if String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 'b' then (
                          1
                        )
                        else (
                          -1
                        )
                      )
                    | 't' -> (
                        if String.unsafe_get s (pos+1) = 'a' && String.unsafe_get s (pos+2) = 'u' then (
                          7
                        )
                        else (
                          -1
                        )
                      )
                    | _ -> (
                        -1
                      )
                )
              | 5 -> (
                  if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = '_' && String.unsafe_get s (pos+2) = 'a' && String.unsafe_get s (pos+3) = '_' && String.unsafe_get s (pos+4) = '0' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Atdgen_runtime.Oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_c_a_0 := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 1 ->
              field_c_b := (
                Some (
                  (
                    read__1
                  ) p lb
                )
              );
            | 2 ->
              field_e := (
                Some (
                  (
                    read__2
                  ) p lb
                )
              );
            | 3 ->
              field_a := (
                Some (
                  (
                    read__1
                  ) p lb
                )
              );
            | 4 ->
              field_r := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 5 ->
              field_b := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 6 ->
              field_s := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 7 ->
              field_tau := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        (
          {
            c_a_0 = (match !field_c_a_0 with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "c_a_0");
            c_b = (match !field_c_b with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "c_b");
            e = (match !field_e with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "e");
            a = (match !field_a with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "a");
            r = (match !field_r with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "r");
            b = (match !field_b with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "b");
            s = (match !field_s with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "s");
            tau = (match !field_tau with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "tau");
          }
         : multi_exp_arg)
      )
)
let multi_exp_arg_of_string s =
  read_multi_exp_arg (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_argument : _ -> argument -> _ = (
  fun ob (x : argument) ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"ca\":";
    (
      write__1
    )
      ob x.ca;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"cb\":";
    (
      write__1
    )
      ob x.cb;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"product_argument\":";
    (
      write_prod_arg
    )
      ob x.product_argument;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"multi_exp_argument\":";
    (
      write_multi_exp_arg
    )
      ob x.multi_exp_argument;
    Bi_outbuf.add_char ob '}';
)
let string_of_argument ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_argument ob x;
  Bi_outbuf.contents ob
let read_argument = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_ca = ref (None) in
    let field_cb = ref (None) in
    let field_product_argument = ref (None) in
    let field_multi_exp_argument = ref (None) in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 2 -> (
                if String.unsafe_get s pos = 'c' then (
                  match String.unsafe_get s (pos+1) with
                    | 'a' -> (
                        0
                      )
                    | 'b' -> (
                        1
                      )
                    | _ -> (
                        -1
                      )
                )
                else (
                  -1
                )
              )
            | 16 -> (
                if String.unsafe_get s pos = 'p' && String.unsafe_get s (pos+1) = 'r' && String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'd' && String.unsafe_get s (pos+4) = 'u' && String.unsafe_get s (pos+5) = 'c' && String.unsafe_get s (pos+6) = 't' && String.unsafe_get s (pos+7) = '_' && String.unsafe_get s (pos+8) = 'a' && String.unsafe_get s (pos+9) = 'r' && String.unsafe_get s (pos+10) = 'g' && String.unsafe_get s (pos+11) = 'u' && String.unsafe_get s (pos+12) = 'm' && String.unsafe_get s (pos+13) = 'e' && String.unsafe_get s (pos+14) = 'n' && String.unsafe_get s (pos+15) = 't' then (
                  2
                )
                else (
                  -1
                )
              )
            | 18 -> (
                if String.unsafe_get s pos = 'm' && String.unsafe_get s (pos+1) = 'u' && String.unsafe_get s (pos+2) = 'l' && String.unsafe_get s (pos+3) = 't' && String.unsafe_get s (pos+4) = 'i' && String.unsafe_get s (pos+5) = '_' && String.unsafe_get s (pos+6) = 'e' && String.unsafe_get s (pos+7) = 'x' && String.unsafe_get s (pos+8) = 'p' && String.unsafe_get s (pos+9) = '_' && String.unsafe_get s (pos+10) = 'a' && String.unsafe_get s (pos+11) = 'r' && String.unsafe_get s (pos+12) = 'g' && String.unsafe_get s (pos+13) = 'u' && String.unsafe_get s (pos+14) = 'm' && String.unsafe_get s (pos+15) = 'e' && String.unsafe_get s (pos+16) = 'n' && String.unsafe_get s (pos+17) = 't' then (
                  3
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Atdgen_runtime.Oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_ca := (
              Some (
                (
                  read__1
                ) p lb
              )
            );
          | 1 ->
            field_cb := (
              Some (
                (
                  read__1
                ) p lb
              )
            );
          | 2 ->
            field_product_argument := (
              Some (
                (
                  read_prod_arg
                ) p lb
              )
            );
          | 3 ->
            field_multi_exp_argument := (
              Some (
                (
                  read_multi_exp_arg
                ) p lb
              )
            );
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 2 -> (
                  if String.unsafe_get s pos = 'c' then (
                    match String.unsafe_get s (pos+1) with
                      | 'a' -> (
                          0
                        )
                      | 'b' -> (
                          1
                        )
                      | _ -> (
                          -1
                        )
                  )
                  else (
                    -1
                  )
                )
              | 16 -> (
                  if String.unsafe_get s pos = 'p' && String.unsafe_get s (pos+1) = 'r' && String.unsafe_get s (pos+2) = 'o' && String.unsafe_get s (pos+3) = 'd' && String.unsafe_get s (pos+4) = 'u' && String.unsafe_get s (pos+5) = 'c' && String.unsafe_get s (pos+6) = 't' && String.unsafe_get s (pos+7) = '_' && String.unsafe_get s (pos+8) = 'a' && String.unsafe_get s (pos+9) = 'r' && String.unsafe_get s (pos+10) = 'g' && String.unsafe_get s (pos+11) = 'u' && String.unsafe_get s (pos+12) = 'm' && String.unsafe_get s (pos+13) = 'e' && String.unsafe_get s (pos+14) = 'n' && String.unsafe_get s (pos+15) = 't' then (
                    2
                  )
                  else (
                    -1
                  )
                )
              | 18 -> (
                  if String.unsafe_get s pos = 'm' && String.unsafe_get s (pos+1) = 'u' && String.unsafe_get s (pos+2) = 'l' && String.unsafe_get s (pos+3) = 't' && String.unsafe_get s (pos+4) = 'i' && String.unsafe_get s (pos+5) = '_' && String.unsafe_get s (pos+6) = 'e' && String.unsafe_get s (pos+7) = 'x' && String.unsafe_get s (pos+8) = 'p' && String.unsafe_get s (pos+9) = '_' && String.unsafe_get s (pos+10) = 'a' && String.unsafe_get s (pos+11) = 'r' && String.unsafe_get s (pos+12) = 'g' && String.unsafe_get s (pos+13) = 'u' && String.unsafe_get s (pos+14) = 'm' && String.unsafe_get s (pos+15) = 'e' && String.unsafe_get s (pos+16) = 'n' && String.unsafe_get s (pos+17) = 't' then (
                    3
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Atdgen_runtime.Oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_ca := (
                Some (
                  (
                    read__1
                  ) p lb
                )
              );
            | 1 ->
              field_cb := (
                Some (
                  (
                    read__1
                  ) p lb
                )
              );
            | 2 ->
              field_product_argument := (
                Some (
                  (
                    read_prod_arg
                  ) p lb
                )
              );
            | 3 ->
              field_multi_exp_argument := (
                Some (
                  (
                    read_multi_exp_arg
                  ) p lb
                )
              );
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        (
          {
            ca = (match !field_ca with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "ca");
            cb = (match !field_cb with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "cb");
            product_argument = (match !field_product_argument with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "product_argument");
            multi_exp_argument = (match !field_multi_exp_argument with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "multi_exp_argument");
          }
         : argument)
      )
)
let argument_of_string s =
  read_argument (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_input : _ -> input -> _ = (
  fun ob (x : input) ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"statement\":";
    (
      write_statement
    )
      ob x.statement;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"argument\":";
    (
      write_argument
    )
      ob x.argument;
    Bi_outbuf.add_char ob '}';
)
let string_of_input ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_input ob x;
  Bi_outbuf.contents ob
let read_input = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_statement = ref (None) in
    let field_argument = ref (None) in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 8 -> (
                if String.unsafe_get s pos = 'a' && String.unsafe_get s (pos+1) = 'r' && String.unsafe_get s (pos+2) = 'g' && String.unsafe_get s (pos+3) = 'u' && String.unsafe_get s (pos+4) = 'm' && String.unsafe_get s (pos+5) = 'e' && String.unsafe_get s (pos+6) = 'n' && String.unsafe_get s (pos+7) = 't' then (
                  1
                )
                else (
                  -1
                )
              )
            | 9 -> (
                if String.unsafe_get s pos = 's' && String.unsafe_get s (pos+1) = 't' && String.unsafe_get s (pos+2) = 'a' && String.unsafe_get s (pos+3) = 't' && String.unsafe_get s (pos+4) = 'e' && String.unsafe_get s (pos+5) = 'm' && String.unsafe_get s (pos+6) = 'e' && String.unsafe_get s (pos+7) = 'n' && String.unsafe_get s (pos+8) = 't' then (
                  0
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Atdgen_runtime.Oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_statement := (
              Some (
                (
                  read_statement
                ) p lb
              )
            );
          | 1 ->
            field_argument := (
              Some (
                (
                  read_argument
                ) p lb
              )
            );
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 8 -> (
                  if String.unsafe_get s pos = 'a' && String.unsafe_get s (pos+1) = 'r' && String.unsafe_get s (pos+2) = 'g' && String.unsafe_get s (pos+3) = 'u' && String.unsafe_get s (pos+4) = 'm' && String.unsafe_get s (pos+5) = 'e' && String.unsafe_get s (pos+6) = 'n' && String.unsafe_get s (pos+7) = 't' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | 9 -> (
                  if String.unsafe_get s pos = 's' && String.unsafe_get s (pos+1) = 't' && String.unsafe_get s (pos+2) = 'a' && String.unsafe_get s (pos+3) = 't' && String.unsafe_get s (pos+4) = 'e' && String.unsafe_get s (pos+5) = 'm' && String.unsafe_get s (pos+6) = 'e' && String.unsafe_get s (pos+7) = 'n' && String.unsafe_get s (pos+8) = 't' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Atdgen_runtime.Oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_statement := (
                Some (
                  (
                    read_statement
                  ) p lb
                )
              );
            | 1 ->
              field_argument := (
                Some (
                  (
                    read_argument
                  ) p lb
                )
              );
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        (
          {
            statement = (match !field_statement with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "statement");
            argument = (match !field_argument with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "argument");
          }
         : input)
      )
)
let input_of_string s =
  read_input (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_comkey : _ -> comkey -> _ = (
  fun ob (x : comkey) ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"h\":";
    (
      Yojson.Safe.write_string
    )
      ob x.h;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"g\":";
    (
      write__1
    )
      ob x.g;
    Bi_outbuf.add_char ob '}';
)
let string_of_comkey ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_comkey ob x;
  Bi_outbuf.contents ob
let read_comkey = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_h = ref (None) in
    let field_g = ref (None) in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          if len = 1 then (
            match String.unsafe_get s pos with
              | 'g' -> (
                  1
                )
              | 'h' -> (
                  0
                )
              | _ -> (
                  -1
                )
          )
          else (
            -1
          )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Atdgen_runtime.Oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_h := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 1 ->
            field_g := (
              Some (
                (
                  read__1
                ) p lb
              )
            );
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            if len = 1 then (
              match String.unsafe_get s pos with
                | 'g' -> (
                    1
                  )
                | 'h' -> (
                    0
                  )
                | _ -> (
                    -1
                  )
            )
            else (
              -1
            )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Atdgen_runtime.Oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_h := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 1 ->
              field_g := (
                Some (
                  (
                    read__1
                  ) p lb
                )
              );
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        (
          {
            h = (match !field_h with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "h");
            g = (match !field_g with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "g");
          }
         : comkey)
      )
)
let comkey_of_string s =
  read_comkey (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_context : _ -> context -> _ = (
  fun ob (x : context) ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"p\":";
    (
      Yojson.Safe.write_string
    )
      ob x.p;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"q\":";
    (
      Yojson.Safe.write_string
    )
      ob x.q;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"g\":";
    (
      Yojson.Safe.write_string
    )
      ob x.g;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"pk\":";
    (
      write__1
    )
      ob x.pk;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"ck\":";
    (
      write_comkey
    )
      ob x.ck;
    Bi_outbuf.add_char ob '}';
)
let string_of_context ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_context ob x;
  Bi_outbuf.contents ob
let read_context = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_p = ref (None) in
    let field_q = ref (None) in
    let field_g = ref (None) in
    let field_pk = ref (None) in
    let field_ck = ref (None) in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 1 -> (
                match String.unsafe_get s pos with
                  | 'g' -> (
                      2
                    )
                  | 'p' -> (
                      0
                    )
                  | 'q' -> (
                      1
                    )
                  | _ -> (
                      -1
                    )
              )
            | 2 -> (
                match String.unsafe_get s pos with
                  | 'c' -> (
                      if String.unsafe_get s (pos+1) = 'k' then (
                        4
                      )
                      else (
                        -1
                      )
                    )
                  | 'p' -> (
                      if String.unsafe_get s (pos+1) = 'k' then (
                        3
                      )
                      else (
                        -1
                      )
                    )
                  | _ -> (
                      -1
                    )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Atdgen_runtime.Oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_p := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 1 ->
            field_q := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 2 ->
            field_g := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 3 ->
            field_pk := (
              Some (
                (
                  read__1
                ) p lb
              )
            );
          | 4 ->
            field_ck := (
              Some (
                (
                  read_comkey
                ) p lb
              )
            );
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 1 -> (
                  match String.unsafe_get s pos with
                    | 'g' -> (
                        2
                      )
                    | 'p' -> (
                        0
                      )
                    | 'q' -> (
                        1
                      )
                    | _ -> (
                        -1
                      )
                )
              | 2 -> (
                  match String.unsafe_get s pos with
                    | 'c' -> (
                        if String.unsafe_get s (pos+1) = 'k' then (
                          4
                        )
                        else (
                          -1
                        )
                      )
                    | 'p' -> (
                        if String.unsafe_get s (pos+1) = 'k' then (
                          3
                        )
                        else (
                          -1
                        )
                      )
                    | _ -> (
                        -1
                      )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Atdgen_runtime.Oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_p := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 1 ->
              field_q := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 2 ->
              field_g := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 3 ->
              field_pk := (
                Some (
                  (
                    read__1
                  ) p lb
                )
              );
            | 4 ->
              field_ck := (
                Some (
                  (
                    read_comkey
                  ) p lb
                )
              );
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        (
          {
            p = (match !field_p with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "p");
            q = (match !field_q with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "q");
            g = (match !field_g with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "g");
            pk = (match !field_pk with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "pk");
            ck = (match !field_ck with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "ck");
          }
         : context)
      )
)
let context_of_string s =
  read_context (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
let write_proof : _ -> proof -> _ = (
  fun ob (x : proof) ->
    Bi_outbuf.add_char ob '{';
    let is_first = ref true in
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"description\":";
    (
      Yojson.Safe.write_string
    )
      ob x.description;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"context\":";
    (
      write_context
    )
      ob x.context;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"input\":";
    (
      write_input
    )
      ob x.input;
    if !is_first then
      is_first := false
    else
      Bi_outbuf.add_char ob ',';
    Bi_outbuf.add_string ob "\"output\":";
    (
      Yojson.Safe.write_bool
    )
      ob x.output;
    Bi_outbuf.add_char ob '}';
)
let string_of_proof ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_proof ob x;
  Bi_outbuf.contents ob
let read_proof = (
  fun p lb ->
    Yojson.Safe.read_space p lb;
    Yojson.Safe.read_lcurl p lb;
    let field_description = ref (None) in
    let field_context = ref (None) in
    let field_input = ref (None) in
    let field_output = ref (None) in
    try
      Yojson.Safe.read_space p lb;
      Yojson.Safe.read_object_end lb;
      Yojson.Safe.read_space p lb;
      let f =
        fun s pos len ->
          if pos < 0 || len < 0 || pos + len > String.length s then
            invalid_arg "out-of-bounds substring position or length";
          match len with
            | 5 -> (
                if String.unsafe_get s pos = 'i' && String.unsafe_get s (pos+1) = 'n' && String.unsafe_get s (pos+2) = 'p' && String.unsafe_get s (pos+3) = 'u' && String.unsafe_get s (pos+4) = 't' then (
                  2
                )
                else (
                  -1
                )
              )
            | 6 -> (
                if String.unsafe_get s pos = 'o' && String.unsafe_get s (pos+1) = 'u' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'p' && String.unsafe_get s (pos+4) = 'u' && String.unsafe_get s (pos+5) = 't' then (
                  3
                )
                else (
                  -1
                )
              )
            | 7 -> (
                if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'n' && String.unsafe_get s (pos+3) = 't' && String.unsafe_get s (pos+4) = 'e' && String.unsafe_get s (pos+5) = 'x' && String.unsafe_get s (pos+6) = 't' then (
                  1
                )
                else (
                  -1
                )
              )
            | 11 -> (
                if String.unsafe_get s pos = 'd' && String.unsafe_get s (pos+1) = 'e' && String.unsafe_get s (pos+2) = 's' && String.unsafe_get s (pos+3) = 'c' && String.unsafe_get s (pos+4) = 'r' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'p' && String.unsafe_get s (pos+7) = 't' && String.unsafe_get s (pos+8) = 'i' && String.unsafe_get s (pos+9) = 'o' && String.unsafe_get s (pos+10) = 'n' then (
                  0
                )
                else (
                  -1
                )
              )
            | _ -> (
                -1
              )
      in
      let i = Yojson.Safe.map_ident p f lb in
      Atdgen_runtime.Oj_run.read_until_field_value p lb;
      (
        match i with
          | 0 ->
            field_description := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_string
                ) p lb
              )
            );
          | 1 ->
            field_context := (
              Some (
                (
                  read_context
                ) p lb
              )
            );
          | 2 ->
            field_input := (
              Some (
                (
                  read_input
                ) p lb
              )
            );
          | 3 ->
            field_output := (
              Some (
                (
                  Atdgen_runtime.Oj_run.read_bool
                ) p lb
              )
            );
          | _ -> (
              Yojson.Safe.skip_json p lb
            )
      );
      while true do
        Yojson.Safe.read_space p lb;
        Yojson.Safe.read_object_sep p lb;
        Yojson.Safe.read_space p lb;
        let f =
          fun s pos len ->
            if pos < 0 || len < 0 || pos + len > String.length s then
              invalid_arg "out-of-bounds substring position or length";
            match len with
              | 5 -> (
                  if String.unsafe_get s pos = 'i' && String.unsafe_get s (pos+1) = 'n' && String.unsafe_get s (pos+2) = 'p' && String.unsafe_get s (pos+3) = 'u' && String.unsafe_get s (pos+4) = 't' then (
                    2
                  )
                  else (
                    -1
                  )
                )
              | 6 -> (
                  if String.unsafe_get s pos = 'o' && String.unsafe_get s (pos+1) = 'u' && String.unsafe_get s (pos+2) = 't' && String.unsafe_get s (pos+3) = 'p' && String.unsafe_get s (pos+4) = 'u' && String.unsafe_get s (pos+5) = 't' then (
                    3
                  )
                  else (
                    -1
                  )
                )
              | 7 -> (
                  if String.unsafe_get s pos = 'c' && String.unsafe_get s (pos+1) = 'o' && String.unsafe_get s (pos+2) = 'n' && String.unsafe_get s (pos+3) = 't' && String.unsafe_get s (pos+4) = 'e' && String.unsafe_get s (pos+5) = 'x' && String.unsafe_get s (pos+6) = 't' then (
                    1
                  )
                  else (
                    -1
                  )
                )
              | 11 -> (
                  if String.unsafe_get s pos = 'd' && String.unsafe_get s (pos+1) = 'e' && String.unsafe_get s (pos+2) = 's' && String.unsafe_get s (pos+3) = 'c' && String.unsafe_get s (pos+4) = 'r' && String.unsafe_get s (pos+5) = 'i' && String.unsafe_get s (pos+6) = 'p' && String.unsafe_get s (pos+7) = 't' && String.unsafe_get s (pos+8) = 'i' && String.unsafe_get s (pos+9) = 'o' && String.unsafe_get s (pos+10) = 'n' then (
                    0
                  )
                  else (
                    -1
                  )
                )
              | _ -> (
                  -1
                )
        in
        let i = Yojson.Safe.map_ident p f lb in
        Atdgen_runtime.Oj_run.read_until_field_value p lb;
        (
          match i with
            | 0 ->
              field_description := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_string
                  ) p lb
                )
              );
            | 1 ->
              field_context := (
                Some (
                  (
                    read_context
                  ) p lb
                )
              );
            | 2 ->
              field_input := (
                Some (
                  (
                    read_input
                  ) p lb
                )
              );
            | 3 ->
              field_output := (
                Some (
                  (
                    Atdgen_runtime.Oj_run.read_bool
                  ) p lb
                )
              );
            | _ -> (
                Yojson.Safe.skip_json p lb
              )
        );
      done;
      assert false;
    with Yojson.End_of_object -> (
        (
          {
            description = (match !field_description with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "description");
            context = (match !field_context with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "context");
            input = (match !field_input with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "input");
            output = (match !field_output with Some x -> x | None -> Atdgen_runtime.Oj_run.missing_field p "output");
          }
         : proof)
      )
)
let proof_of_string s =
  read_proof (Yojson.Safe.init_lexer ()) (Lexing.from_string s)
