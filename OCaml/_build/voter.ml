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

let commitment_tag = Bi_io.record_tag
let write_untagged_commitment : Bi_outbuf.t -> commitment -> unit = (
  fun ob x ->
    Bi_vint.write_uvint ob 2;
    Bi_outbuf.add_char4 ob '\128' '\000' '\000' 'a';
    (
      Bi_io.write_string
    ) ob x.a;
    Bi_outbuf.add_char4 ob '\128' '\000' '\000' 'b';
    (
      Bi_io.write_string
    ) ob x.b;
)
let write_commitment ob x =
  Bi_io.write_tag ob Bi_io.record_tag;
  write_untagged_commitment ob x
let string_of_commitment ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_commitment ob x;
  Bi_outbuf.contents ob
let get_commitment_reader = (
  fun tag ->
    if tag <> 21 then Ag_ob_run.read_error () else
      fun ib ->
        let field_a = ref (Obj.magic 0.0) in
        let field_b = ref (Obj.magic 0.0) in
        let bits0 = ref 0 in
        let len = Bi_vint.read_uvint ib in
        for i = 1 to len do
          match Bi_io.read_field_hashtag ib with
            | 97 ->
              field_a := (
                (
                  Ag_ob_run.read_string
                ) ib
              );
              bits0 := !bits0 lor 0x1;
            | 98 ->
              field_b := (
                (
                  Ag_ob_run.read_string
                ) ib
              );
              bits0 := !bits0 lor 0x2;
            | _ -> Bi_io.skip ib
        done;
        if !bits0 <> 0x3 then Ag_ob_run.missing_fields [| !bits0 |] [| "a"; "b" |];
        (
          {
            a = !field_a;
            b = !field_b;
          }
         : commitment)
)
let read_commitment = (
  fun ib ->
    if Bi_io.read_tag ib <> 21 then Ag_ob_run.read_error_at ib;
    let field_a = ref (Obj.magic 0.0) in
    let field_b = ref (Obj.magic 0.0) in
    let bits0 = ref 0 in
    let len = Bi_vint.read_uvint ib in
    for i = 1 to len do
      match Bi_io.read_field_hashtag ib with
        | 97 ->
          field_a := (
            (
              Ag_ob_run.read_string
            ) ib
          );
          bits0 := !bits0 lor 0x1;
        | 98 ->
          field_b := (
            (
              Ag_ob_run.read_string
            ) ib
          );
          bits0 := !bits0 lor 0x2;
        | _ -> Bi_io.skip ib
    done;
    if !bits0 <> 0x3 then Ag_ob_run.missing_fields [| !bits0 |] [| "a"; "b" |];
    (
      {
        a = !field_a;
        b = !field_b;
      }
     : commitment)
)
let commitment_of_string ?pos s =
  read_commitment (Bi_inbuf.from_string ?pos s)
let proof_tag = Bi_io.record_tag
let write_untagged_proof : Bi_outbuf.t -> proof -> unit = (
  fun ob x ->
    Bi_vint.write_uvint ob 3;
    Bi_outbuf.add_char4 ob '²' 'c' 'ô' 'c';
    (
      Bi_io.write_string
    ) ob x.challenge;
    Bi_outbuf.add_char4 ob 'ð' 'ä' '}' '\021';
    (
      write_commitment
    ) ob x.commitment;
    Bi_outbuf.add_char4 ob '¢' '\012' '®' '\129';
    (
      Bi_io.write_string
    ) ob x.response;
)
let write_proof ob x =
  Bi_io.write_tag ob Bi_io.record_tag;
  write_untagged_proof ob x
let string_of_proof ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_proof ob x;
  Bi_outbuf.contents ob
let get_proof_reader = (
  fun tag ->
    if tag <> 21 then Ag_ob_run.read_error () else
      fun ib ->
        let field_challenge = ref (Obj.magic 0.0) in
        let field_commitment = ref (Obj.magic 0.0) in
        let field_response = ref (Obj.magic 0.0) in
        let bits0 = ref 0 in
        let len = Bi_vint.read_uvint ib in
        for i = 1 to len do
          match Bi_io.read_field_hashtag ib with
            | 845411427 ->
              field_challenge := (
                (
                  Ag_ob_run.read_string
                ) ib
              );
              bits0 := !bits0 lor 0x1;
            | -253461227 ->
              field_commitment := (
                (
                  read_commitment
                ) ib
              );
              bits0 := !bits0 lor 0x2;
            | 571256449 ->
              field_response := (
                (
                  Ag_ob_run.read_string
                ) ib
              );
              bits0 := !bits0 lor 0x4;
            | _ -> Bi_io.skip ib
        done;
        if !bits0 <> 0x7 then Ag_ob_run.missing_fields [| !bits0 |] [| "challenge"; "commitment"; "response" |];
        (
          {
            challenge = !field_challenge;
            commitment = !field_commitment;
            response = !field_response;
          }
         : proof)
)
let read_proof = (
  fun ib ->
    if Bi_io.read_tag ib <> 21 then Ag_ob_run.read_error_at ib;
    let field_challenge = ref (Obj.magic 0.0) in
    let field_commitment = ref (Obj.magic 0.0) in
    let field_response = ref (Obj.magic 0.0) in
    let bits0 = ref 0 in
    let len = Bi_vint.read_uvint ib in
    for i = 1 to len do
      match Bi_io.read_field_hashtag ib with
        | 845411427 ->
          field_challenge := (
            (
              Ag_ob_run.read_string
            ) ib
          );
          bits0 := !bits0 lor 0x1;
        | -253461227 ->
          field_commitment := (
            (
              read_commitment
            ) ib
          );
          bits0 := !bits0 lor 0x2;
        | 571256449 ->
          field_response := (
            (
              Ag_ob_run.read_string
            ) ib
          );
          bits0 := !bits0 lor 0x4;
        | _ -> Bi_io.skip ib
    done;
    if !bits0 <> 0x7 then Ag_ob_run.missing_fields [| !bits0 |] [| "challenge"; "commitment"; "response" |];
    (
      {
        challenge = !field_challenge;
        commitment = !field_commitment;
        response = !field_response;
      }
     : proof)
)
let proof_of_string ?pos s =
  read_proof (Bi_inbuf.from_string ?pos s)
let choice_tag = Bi_io.record_tag
let write_untagged_choice : Bi_outbuf.t -> choice -> unit = (
  fun ob x ->
    Bi_vint.write_uvint ob 2;
    Bi_outbuf.add_char4 ob '¡' '\150' '§' '^';
    (
      Bi_io.write_string
    ) ob x.choice_alpha;
    Bi_outbuf.add_char4 ob 'Á' '\019' 'ñ' 'ð';
    (
      Bi_io.write_string
    ) ob x.choice_beta;
)
let write_choice ob x =
  Bi_io.write_tag ob Bi_io.record_tag;
  write_untagged_choice ob x
let string_of_choice ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_choice ob x;
  Bi_outbuf.contents ob
let get_choice_reader = (
  fun tag ->
    if tag <> 21 then Ag_ob_run.read_error () else
      fun ib ->
        let field_choice_alpha = ref (Obj.magic 0.0) in
        let field_choice_beta = ref (Obj.magic 0.0) in
        let bits0 = ref 0 in
        let len = Bi_vint.read_uvint ib in
        for i = 1 to len do
          match Bi_io.read_field_hashtag ib with
            | 563521374 ->
              field_choice_alpha := (
                (
                  Ag_ob_run.read_string
                ) ib
              );
              bits0 := !bits0 lor 0x1;
            | -1055657488 ->
              field_choice_beta := (
                (
                  Ag_ob_run.read_string
                ) ib
              );
              bits0 := !bits0 lor 0x2;
            | _ -> Bi_io.skip ib
        done;
        if !bits0 <> 0x3 then Ag_ob_run.missing_fields [| !bits0 |] [| "alpha"; "beta" |];
        (
          {
            choice_alpha = !field_choice_alpha;
            choice_beta = !field_choice_beta;
          }
         : choice)
)
let read_choice = (
  fun ib ->
    if Bi_io.read_tag ib <> 21 then Ag_ob_run.read_error_at ib;
    let field_choice_alpha = ref (Obj.magic 0.0) in
    let field_choice_beta = ref (Obj.magic 0.0) in
    let bits0 = ref 0 in
    let len = Bi_vint.read_uvint ib in
    for i = 1 to len do
      match Bi_io.read_field_hashtag ib with
        | 563521374 ->
          field_choice_alpha := (
            (
              Ag_ob_run.read_string
            ) ib
          );
          bits0 := !bits0 lor 0x1;
        | -1055657488 ->
          field_choice_beta := (
            (
              Ag_ob_run.read_string
            ) ib
          );
          bits0 := !bits0 lor 0x2;
        | _ -> Bi_io.skip ib
    done;
    if !bits0 <> 0x3 then Ag_ob_run.missing_fields [| !bits0 |] [| "alpha"; "beta" |];
    (
      {
        choice_alpha = !field_choice_alpha;
        choice_beta = !field_choice_beta;
      }
     : choice)
)
let choice_of_string ?pos s =
  read_choice (Bi_inbuf.from_string ?pos s)
let _2_tag = Bi_io.array_tag
let write_untagged__2 = (
  Ag_ob_run.write_untagged_list
    proof_tag
    (
      write_untagged_proof
    )
)
let write__2 ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__2 ob x
let string_of__2 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__2 ob x;
  Bi_outbuf.contents ob
let get__2_reader = (
  Ag_ob_run.get_list_reader (
    get_proof_reader
  )
)
let read__2 = (
  Ag_ob_run.read_list (
    get_proof_reader
  )
)
let _2_of_string ?pos s =
  read__2 (Bi_inbuf.from_string ?pos s)
let _3_tag = Bi_io.array_tag
let write_untagged__3 = (
  Ag_ob_run.write_untagged_list
    _2_tag
    (
      write_untagged__2
    )
)
let write__3 ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__3 ob x
let string_of__3 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__3 ob x;
  Bi_outbuf.contents ob
let get__3_reader = (
  Ag_ob_run.get_list_reader (
    get__2_reader
  )
)
let read__3 = (
  Ag_ob_run.read_list (
    get__2_reader
  )
)
let _3_of_string ?pos s =
  read__3 (Bi_inbuf.from_string ?pos s)
let _1_tag = Bi_io.array_tag
let write_untagged__1 = (
  Ag_ob_run.write_untagged_list
    choice_tag
    (
      write_untagged_choice
    )
)
let write__1 ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__1 ob x
let string_of__1 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__1 ob x;
  Bi_outbuf.contents ob
let get__1_reader = (
  Ag_ob_run.get_list_reader (
    get_choice_reader
  )
)
let read__1 = (
  Ag_ob_run.read_list (
    get_choice_reader
  )
)
let _1_of_string ?pos s =
  read__1 (Bi_inbuf.from_string ?pos s)
let answer_tag = Bi_io.record_tag
let write_untagged_answer : Bi_outbuf.t -> answer -> unit = (
  fun ob x ->
    Bi_vint.write_uvint ob 3;
    Bi_outbuf.add_char4 ob 'Ù' '\023' 'µ' 'ò';
    (
      write__1
    ) ob x.choices;
    Bi_outbuf.add_char4 ob 'á' 'Î' '²' '\149';
    (
      write__3
    ) ob x.individual_proofs;
    Bi_outbuf.add_char4 ob 'ã' 'â' 'Ù' 'Ò';
    (
      Bi_io.write_string
    ) ob x.overall_proof;
)
let write_answer ob x =
  Bi_io.write_tag ob Bi_io.record_tag;
  write_untagged_answer ob x
let string_of_answer ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_answer ob x;
  Bi_outbuf.contents ob
let get_answer_reader = (
  fun tag ->
    if tag <> 21 then Ag_ob_run.read_error () else
      fun ib ->
        let field_choices = ref (Obj.magic 0.0) in
        let field_individual_proofs = ref (Obj.magic 0.0) in
        let field_overall_proof = ref (Obj.magic 0.0) in
        let bits0 = ref 0 in
        let len = Bi_vint.read_uvint ib in
        for i = 1 to len do
          match Bi_io.read_field_hashtag ib with
            | -652757518 ->
              field_choices := (
                (
                  read__1
                ) ib
              );
              bits0 := !bits0 lor 0x1;
            | -506547563 ->
              field_individual_proofs := (
                (
                  read__3
                ) ib
              );
              bits0 := !bits0 lor 0x2;
            | -471672366 ->
              field_overall_proof := (
                (
                  Ag_ob_run.read_string
                ) ib
              );
              bits0 := !bits0 lor 0x4;
            | _ -> Bi_io.skip ib
        done;
        if !bits0 <> 0x7 then Ag_ob_run.missing_fields [| !bits0 |] [| "choices"; "individual_proofs"; "overall_proof" |];
        (
          {
            choices = !field_choices;
            individual_proofs = !field_individual_proofs;
            overall_proof = !field_overall_proof;
          }
         : answer)
)
let read_answer = (
  fun ib ->
    if Bi_io.read_tag ib <> 21 then Ag_ob_run.read_error_at ib;
    let field_choices = ref (Obj.magic 0.0) in
    let field_individual_proofs = ref (Obj.magic 0.0) in
    let field_overall_proof = ref (Obj.magic 0.0) in
    let bits0 = ref 0 in
    let len = Bi_vint.read_uvint ib in
    for i = 1 to len do
      match Bi_io.read_field_hashtag ib with
        | -652757518 ->
          field_choices := (
            (
              read__1
            ) ib
          );
          bits0 := !bits0 lor 0x1;
        | -506547563 ->
          field_individual_proofs := (
            (
              read__3
            ) ib
          );
          bits0 := !bits0 lor 0x2;
        | -471672366 ->
          field_overall_proof := (
            (
              Ag_ob_run.read_string
            ) ib
          );
          bits0 := !bits0 lor 0x4;
        | _ -> Bi_io.skip ib
    done;
    if !bits0 <> 0x7 then Ag_ob_run.missing_fields [| !bits0 |] [| "choices"; "individual_proofs"; "overall_proof" |];
    (
      {
        choices = !field_choices;
        individual_proofs = !field_individual_proofs;
        overall_proof = !field_overall_proof;
      }
     : answer)
)
let answer_of_string ?pos s =
  read_answer (Bi_inbuf.from_string ?pos s)
let _4_tag = Bi_io.array_tag
let write_untagged__4 = (
  Ag_ob_run.write_untagged_list
    answer_tag
    (
      write_untagged_answer
    )
)
let write__4 ob x =
  Bi_io.write_tag ob Bi_io.array_tag;
  write_untagged__4 ob x
let string_of__4 ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write__4 ob x;
  Bi_outbuf.contents ob
let get__4_reader = (
  Ag_ob_run.get_list_reader (
    get_answer_reader
  )
)
let read__4 = (
  Ag_ob_run.read_list (
    get_answer_reader
  )
)
let _4_of_string ?pos s =
  read__4 (Bi_inbuf.from_string ?pos s)
let voter_tag = Bi_io.record_tag
let write_untagged_voter : Bi_outbuf.t -> voter -> unit = (
  fun ob x ->
    Bi_vint.write_uvint ob 3;
    Bi_outbuf.add_char4 ob 'Â' 'í' 'Ñ' '5';
    (
      write__4
    ) ob x.answers;
    Bi_outbuf.add_char4 ob 'ü' '~' 'L' '4';
    (
      Bi_io.write_string
    ) ob x.election_hash;
    Bi_outbuf.add_char4 ob '\133' '%' '6' '¡';
    (
      Bi_io.write_string
    ) ob x.election_uuid;
)
let write_voter ob x =
  Bi_io.write_tag ob Bi_io.record_tag;
  write_untagged_voter ob x
let string_of_voter ?(len = 1024) x =
  let ob = Bi_outbuf.create len in
  write_voter ob x;
  Bi_outbuf.contents ob
let get_voter_reader = (
  fun tag ->
    if tag <> 21 then Ag_ob_run.read_error () else
      fun ib ->
        let field_answers = ref (Obj.magic 0.0) in
        let field_election_hash = ref (Obj.magic 0.0) in
        let field_election_uuid = ref (Obj.magic 0.0) in
        let bits0 = ref 0 in
        let len = Bi_vint.read_uvint ib in
        for i = 1 to len do
          match Bi_io.read_field_hashtag ib with
            | -1024601803 ->
              field_answers := (
                (
                  read__4
                ) ib
              );
              bits0 := !bits0 lor 0x1;
            | -58831820 ->
              field_election_hash := (
                (
                  Ag_ob_run.read_string
                ) ib
              );
              bits0 := !bits0 lor 0x2;
            | 86324897 ->
              field_election_uuid := (
                (
                  Ag_ob_run.read_string
                ) ib
              );
              bits0 := !bits0 lor 0x4;
            | _ -> Bi_io.skip ib
        done;
        if !bits0 <> 0x7 then Ag_ob_run.missing_fields [| !bits0 |] [| "answers"; "election_hash"; "election_uuid" |];
        (
          {
            answers = !field_answers;
            election_hash = !field_election_hash;
            election_uuid = !field_election_uuid;
          }
         : voter)
)
let read_voter = (
  fun ib ->
    if Bi_io.read_tag ib <> 21 then Ag_ob_run.read_error_at ib;
    let field_answers = ref (Obj.magic 0.0) in
    let field_election_hash = ref (Obj.magic 0.0) in
    let field_election_uuid = ref (Obj.magic 0.0) in
    let bits0 = ref 0 in
    let len = Bi_vint.read_uvint ib in
    for i = 1 to len do
      match Bi_io.read_field_hashtag ib with
        | -1024601803 ->
          field_answers := (
            (
              read__4
            ) ib
          );
          bits0 := !bits0 lor 0x1;
        | -58831820 ->
          field_election_hash := (
            (
              Ag_ob_run.read_string
            ) ib
          );
          bits0 := !bits0 lor 0x2;
        | 86324897 ->
          field_election_uuid := (
            (
              Ag_ob_run.read_string
            ) ib
          );
          bits0 := !bits0 lor 0x4;
        | _ -> Bi_io.skip ib
    done;
    if !bits0 <> 0x7 then Ag_ob_run.missing_fields [| !bits0 |] [| "answers"; "election_hash"; "election_uuid" |];
    (
      {
        answers = !field_answers;
        election_hash = !field_election_hash;
        election_uuid = !field_election_uuid;
      }
     : voter)
)
let voter_of_string ?pos s =
  read_voter (Bi_inbuf.from_string ?pos s)
let create_commitment 
  ~a
  ~b
  () : commitment =
  {
    a = a;
    b = b;
  }
let create_proof 
  ~challenge
  ~commitment
  ~response
  () : proof =
  {
    challenge = challenge;
    commitment = commitment;
    response = response;
  }
let create_choice 
  ~choice_alpha
  ~choice_beta
  () : choice =
  {
    choice_alpha = choice_alpha;
    choice_beta = choice_beta;
  }
let create_answer 
  ~choices
  ~individual_proofs
  ~overall_proof
  () : answer =
  {
    choices = choices;
    individual_proofs = individual_proofs;
    overall_proof = overall_proof;
  }
let create_voter 
  ~answers
  ~election_hash
  ~election_uuid
  () : voter =
  {
    answers = answers;
    election_hash = election_hash;
    election_uuid = election_uuid;
  }
