open Batteries
open Proof_t
open Proof_j

let _ =

  let rec listToVec l =
    match l with
    | [] -> Lib.Nil
    | h :: t -> Lib.Cons (h, Lib.O, (listToVec t)) in
    
  let rec createFixedTuple con l =
    match l with
    | [] -> Lib.Nil
    | h :: t -> Lib.Cons ((Big_int_Z.big_int_of_string con, Big_int_Z.big_int_of_string h), Lib.O, (createFixedTuple con t)) in
 
  let rec sublist b e l =
  match l with
    [] -> failwith "sublist"
  | h :: t ->
     let tail = if e=0 then [] else sublist (b-1) (e-1) t in
     if b>0 then tail else h :: tail in

  (* Inital function *)

  Format.printf "%s\n" "Loading data";
  Format.print_flush();
  
  let get_proofs =
      (let proofs = BatFile.open_in "mixnet/verify-shuffle-argument.json" in
      let proofsstring = BatIO.read_all proofs in
      let proofjson = Yojson.Basic.from_string proofsstring in
      let prooflistjson = Yojson.Basic.Util.to_list proofjson in
      List.map (fun x -> Proof_j.proof_of_string (Yojson.Basic.to_string x)) prooflistjson) in
      
  let prooflist = get_proofs in
  
  Format.printf "%s\n" "Data loaded";
  
  (* We have now loaded in all the proofs, though
  only 6 of 8 have compitable parametes *)
  
  let i = 4 in
  let proof = List.nth prooflist i in
  
  (* Lets load the statement *)
  let createPublicKey l = createFixedTuple proof.context.g l in
  let createCiphertext c = createFixedTuple c.gamma c.phis in
  
  let pk = createPublicKey proof.context.pk in
  let h = Big_int_Z.big_int_of_string proof.context.ck.h in
  let hs = listToVec (List.map Big_int_Z.big_int_of_string proof.context.ck.g) in
  let ciphin = listToVec (List.map createCiphertext proof.input.statement.ciphertexts) in
  let ciphout = listToVec (List.map createCiphertext proof.input.statement.shuffled_ciphertexts) in
  let stat = ((((pk,h),hs),ciphin),ciphout) in
  
  (* Lib.vmap (fixedTupleToString "") Lib.O ciphin; *)
  
  (* We have copied the challenges in rather than computing them *)
  
  let c0 = listToVec (List.map Big_int_Z.big_int_of_string proof.input.argument.ca) in
  let e0 = Big_int_Z.big_int_of_string "67494205472125224061903239768413486368372124463067129769174990243458944954300" in
  let c1 = listToVec (List.map Big_int_Z.big_int_of_string proof.input.argument.cb) in
  let e1 = (Big_int_Z.big_int_of_string "14684454401923061436313139268608840192739698259430044541148080682849877464103",
    Big_int_Z.big_int_of_string "53456599641935726622438016320839853260431997463524359022379018969223599070689") in
  
  (* Now the commitments get hard *)
  let prod_arg = proof.input.argument.product_argument in
  let had_arg = Option.get prod_arg.hadamard_argument in
  let prodargsub = Big_int_Z.big_int_of_string (Option.get prod_arg.c_b) in
  let sig5 = listToVec (sublist 1 6 (List.map Big_int_Z.big_int_of_string had_arg.cUpperB))  in
  
  (** Format.printf "%s\n" (Big_int_Z.string_of_big_int (Big_int_Z.big_int_of_string (List.hd had_arg.cUpperB)));
  Format.printf "%s\n" (Big_int_Z.string_of_big_int (Lib.hd Lib.O sig5)); **)
  
  let sig_sub = ((Big_int_Z.big_int_of_string prod_arg.single_vpa.c_d,Big_int_Z.big_int_of_string prod_arg.single_vpa.c_lower_delta),Big_int_Z.big_int_of_string prod_arg.single_vpa.c_upper_delta) in
  let prodarg = ((prodargsub,sig5),sig_sub) in
  
  let multi = proof.input.argument.multi_exp_argument in
  let bgmultiarg = ((Big_int_Z.big_int_of_string multi.c_a_0,
  listToVec (List.map Big_int_Z.big_int_of_string multi.c_b)),
  listToVec (List.map createCiphertext multi.e)) in
  let c2 = (prodarg, bgmultiarg) in
  (* BGHadProd x 2, BGSingleprod ,Multiexp *)
  let e2 = ((( Big_int_Z.big_int_of_string "18137111886441911247259214762544358995330148319158016012191431349509072786672",
    Big_int_Z.big_int_of_string "94351562645198771793581633497709126087644286420857469489047677448351463445682"),
  Big_int_Z.big_int_of_string "77930062936474126676847080473959643521689773838194239942371432521342627018109"),
  Big_int_Z.big_int_of_string "71802416226237056305933783210914823714065594539770215255290796978401338841721") in
  
  (* Final two rounds *)
  let zero_arg = had_arg.zero_argument in
  let c3 = ((),((Big_int_Z.big_int_of_string zero_arg.c_a0, Big_int_Z.big_int_of_string zero_arg.c_bm),
    listToVec (List.map Big_int_Z.big_int_of_string zero_arg.c_d))) in
  (* BGzeroarg *)
  let e3 = Big_int_Z.big_int_of_string "43335003647150889177593960681224356185484549219712679136165329201212463622328" in
  
  (* Now we need to construct the response *)
  let sig5_t = ((((listToVec (List.map Big_int_Z.big_int_of_string zero_arg.a), Big_int_Z.big_int_of_string zero_arg.r),
    listToVec (List.map Big_int_Z.big_int_of_string zero_arg.b)), Big_int_Z.big_int_of_string zero_arg.s),
  Big_int_Z.big_int_of_string zero_arg.t) in
  let sig_t = (((listToVec (List.map Big_int_Z.big_int_of_string prod_arg.single_vpa.a_tilde),
    listToVec (List.map Big_int_Z.big_int_of_string prod_arg.single_vpa.b_tilde)),
    Big_int_Z.big_int_of_string prod_arg.single_vpa.r_tilde), Big_int_Z.big_int_of_string prod_arg.single_vpa.s_tilde) in
  let bg_t = ((((listToVec (List.map Big_int_Z.big_int_of_string multi.a),Big_int_Z.big_int_of_string multi.r),
  Big_int_Z.big_int_of_string multi.b),Big_int_Z.big_int_of_string multi.s),Lib.const (Big_int_Z.big_int_of_string multi.tau) (Lib.S (Lib.L.coq_N))) in
  let t = ((sig5_t,sig_t),bg_t) in
  
  Format.printf "Verifier result: %B\n" (Lib.ShuffleSigma.coq_V (((((((((stat,c0),e0),c1),e1),c2),e2),c3),e3),t));
  
  Format.printf "%s\n" "Done";

