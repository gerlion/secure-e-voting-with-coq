open Batteries
open ElectionGuard_t
open ElectionGuard_j

let _ =

  let debug = true in (* We use this switch to increase logging *)

  Format.printf "%s\n" "Loading data";

  let electionFile = BatFile.open_in "new.json" in
  let elstring = BatIO.read_all electionFile in
  let election = ElectionGuard_j.election_of_string elstring in
  
  (* We don't actually check that parameters match the lib *)
  
  Format.printf "%s\n" "Election loaded";
  
  Format.print_flush ();
  
  let g = Big_int.of_string election.parameters.generator in
  
  let pk = Big_int.of_string election.joint_public_key in
  
  (* Check proofs of correct encryption *)
  
  let getCiphertexts = (fun x ->
    (Big_int.of_string x.message.public_key, Big_int.of_string x.message.ciphertext)
  ) in
  
  let getSummation = (fun x ->
    List.fold_left Lib.DG.coq_Gdot Lib.DG.coq_Gone x
  ) in
  
  let getStatmentOfCorrectEncrytion = (fun selections ofOneProof ->
    let ciphInGroup = List.map getCiphertexts selections in
    let sum = getSummation ciphInGroup in
    Lib.oneOfNStatment (g,pk) sum ciphInGroup
  ) in
  
  let formatCommit = (fun (x : commitment) ->
    (Big_int.of_string x.public_key, Big_int.of_string x.ciphertext)
  ) in
  
  let rec getCommitmentOfCorrectEncrytion =
        (fun (x : message list) (y : proof) ->
    match x with
    | [] -> (formatCommit y.commitment)
    | z::zs ->
         Obj.magic (getCommitmentOfCorrectEncrytion zs y, (formatCommit z.zero_proof.commitment, formatCommit z.one_proof.commitment))
  ) in
  
  let rec getChallengeOfCorrectEncrytion = (fun x y ->
    match x with
    | [] -> (Big_int.of_string y.challenge)
    | z::zs ->
        let one = Big_int.of_string z.zero_proof.challenge in
        let two = Big_int.of_string z.one_proof.challenge in
         Obj.magic (getChallengeOfCorrectEncrytion zs y,
         Lib.fadd one two)
  ) in
  
  let rec getResponseOfCorrectEncrytion = (fun x y ->
    match x with
    | [] -> (Big_int.of_string y.response)
    | z::zs ->
        let r1 = Big_int.of_string z.zero_proof.response in
        let r2 = Big_int.of_string z.one_proof.response in
        let c2 = Big_int.of_string z.zero_proof.challenge in
         Obj.magic (getResponseOfCorrectEncrytion zs y, ((r1,c2),r2))
  ) in
  
  let sigmaCorrectEncryption =  Lib.oneOfNSigma [(g, pk); (g, pk);(g, pk)] in
  
  (* Check proof of correct decryption *)
  
  let rec getDefFac = (fun (x : decproof list) ->
    match x with
    | [] -> Lib.gone
    | z::zs -> (Lib.gdot (getDefFac zs) (Big_int.of_string z.share))
  ) in
  
  let rec getDefFacs = (fun (x : decproof list) ->
    match x with
    | z::[] -> Big_int.of_string z.share
    | z::zs -> Obj.magic (getDefFacs zs, Big_int.of_string z.share)
  ) in
  
  let rec getCommitmentOfCorrectDecrytionN = (fun (x : decproof list) ->
    match x with
    | z::[] -> formatCommit z.proof.commitment
    | z::zs -> Obj.magic (getCommitmentOfCorrectDecrytionN zs,  formatCommit z.proof.commitment)
  ) in
  
  let rec getChallengeOfCorrectDecrytionN = (fun x ->
    match x with
    | z::[] -> Big_int.of_string z.proof.challenge
    | z::zs -> Obj.magic (getChallengeOfCorrectDecrytionN zs,  Big_int.of_string z.proof.challenge)
  ) in
  
  let rec getResponsOfCorrectDecrytionN = (fun x ->
    match x with
    | z::[] -> Big_int.of_string z.proof.response
    | z::zs -> Obj.magic (getResponsOfCorrectDecrytionN zs,  Big_int.of_string z.proof.response)
  ) in
  
  let formatEnc = (fun (x : ciphertext) ->
    (Big_int.of_string x.public_key, Big_int.of_string x.ciphertext)
  ) in
  
  let rec getPk = (fun (x : trustee_public_key list list) ->
    match x with
    | z::[] -> (g, Big_int.of_string (List.hd z).public_key)
    | z::zs -> Obj.magic (getPk zs, (g, Big_int.of_string (List.hd z).public_key))
  ) in
  
  Format.printf "%s\n" "Getting ready to load public key";
  
  Format.print_flush ();
  
  let allPk = getPk election.trustee_public_keys in
  let r = election.trustee_public_keys in
  let allPk2 = ((((g,Big_int.of_string (List.hd (List.nth r 3)).public_key),(g,Big_int.of_string (List.hd (List.nth r 2)).public_key)),(g,Big_int.of_string (List.hd (List.nth r 1)).public_key)),(g,Big_int.of_string (List.hd (List.nth r 0)).public_key)) in 
	(*
  let allPk2 = ((((g,Big_int.of_string (List.hd (List.nth r 2)).public_key)),(g,Big_int.of_string (List.hd (List.nth r 1)).public_key)),(g,Big_int.of_string (List.hd (List.nth r 0)).public_key)) in *)
  
  (* Format.printf "%s\n" (Big_int.string_of_big_int (snd (snd (Obj.magic allPk))));
  Format.printf "%s\n" (Big_int.string_of_big_int (snd (snd allPk2))); *)
  
  let rec range a b =
  if a > b then []
  else a :: range (a+1) b in

  List.map (fun i -> 


  List.map (fun ballot -> (* Forall cast ballots *)
    List.map (fun contest -> (* Forall contests *)
    
        Format.printf "%s\n" "Checking";
        Format.print_flush ();
        
        let s = getStatmentOfCorrectEncrytion contest.selections contest.num_selections_proof in
        let c = getCommitmentOfCorrectEncrytion contest.selections contest.num_selections_proof in
        let e = getChallengeOfCorrectEncrytion contest.selections contest.num_selections_proof in
        let t = getResponseOfCorrectEncrytion contest.selections contest.num_selections_proof in
        
        if debug then Format.printf "%s\n" "Proof prepared";
        Format.print_flush ();
        
        let result = sigmaCorrectEncryption.coq_V1 (Obj.magic (((s, c), e), t)) in

        Format.printf "%b\n" result;
        
        Format.print_flush ();
        
    ) ballot.contests;
  ) election.cast_ballots;

  ) (range 0 50);
  
  List.map (fun contest ->
    List.map (fun option ->
        let decFac = getDefFac option.shares in
        let decFacTuple = getDefFacs option.shares in

        let sigmaCorrectDecryption =  Lib.decryptionSigma in

        let sd = Lib.decryptionSigmaStatment (formatEnc option.encrypted_tally) (Obj.magic allPk2) (Obj.magic decFacTuple) in
        
        let cd = getCommitmentOfCorrectDecrytionN option.shares in
        let ed = getChallengeOfCorrectDecrytionN option.shares in
        let td = getResponsOfCorrectDecrytionN option.shares in

        let inputD =  Obj.magic (((sd, cd), ed), td) in
        
        Format.printf "%s\n" "Prepared";
        Format.print_flush ();
        
        let result = sigmaCorrectDecryption.coq_V1 inputD in

        Format.printf "%b\n"  result;
    ) contest;
  ) election.contest_tallies;

  (* ) (range 0 50); *)
  
  (* and we are done *)
  
  Format.printf "%s\n" "All over";
