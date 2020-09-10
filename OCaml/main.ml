open Batteries
open Voter_t
open Voter_j
open Voterlist_t
open Voterlist_j
open Authority_t
open Authority_j
open VoterAudit_t
open VoterAudit_j

(* try to pattern matching on Voter_t = Voter_j.voter_of_string vt. and call the functions from Lib *) 
let _ =

  Format.printf "%s\n" "Loading data";

  let voterFile = BatFile.open_in "voters/votes.json" in
  let vtstring = BatIO.read_all voterFile in
  let vtjson = Yojson.Basic.from_string vtstring in
  let vtlistjson = Yojson.Basic.Util.to_list vtjson in
  let vlist = List.map (fun x -> Voter_j.voter_of_string (Yojson.Basic.to_string x)) vtlistjson in

  Format.printf "%s\n" "Voters loaded";

  let auditFile  = BatFile.open_in "voters/audit.json" in
  let auditstring = BatIO.read_all auditFile in
  let audit = VoterAudit_j.voterAudit_of_string auditstring in

  Format.printf "%s\n" "Audit data loaded";

  let authorityFile = BatFile.open_in "authority.json" in
  let authstring = BatIO.read_all authorityFile in
  let authjson = Yojson.Basic.from_string authstring in
  let authlistjson = Yojson.Basic.Util.to_list authjson in
  let authlist = List.map (fun x -> Authority_j.authority_of_string (Yojson.Basic.to_string x)) authlistjson in

  Format.printf "%s\n" "Authorities loaded";

  (* Code to print all the data *)
  (* List.map (fun x -> Format.printf "%s\n" (show_voter x)) vlist;

  List.map (fun x -> Format.printf "%s\n" (show_authority x)) authlist; *)

  Format.printf "%s\n" "Loading keys";

  let g = Big_int.of_string "14887492224963187634282421537186040801304008017743492304481737382571933937568724473847106029915040150784031882206090286938661464458896494215273989547889201144857352611058572236578734319505128042602372864570426550855201448111746579871811249114781674309062693442442368697449970648232621880001709535143047913661432883287150003429802392229361583608686643243349727791976247247948618930423866180410558458272606627111270040091203073580238905303994472202930783207472394578498507764703191288249547659899997131166130259700604433891232298182348403175947450284433411265966789131024573629546048637848902243503970966798589660808533" in

  let pk = Big_int.of_string "5094375976223224568964651454460925388781798323160987974549997662320894807199196387285793268149533231524316486536859809631901313311727213621237552174308119910219053536785796941133164375673068579015438046768056052860704355951368362675779467751170239053255405681642674112345136560781998557862629437006696597524954238447837538711466325269712536532291531424031626021280245010837179218152172112384102830142901284529674873258249495223467977322918747822078046597129742818011867417595419321965956492106267786518619367111880069090311895122768899784523423071410088919393993523335021191956275467663988265574587575901193639949095" in

  Format.printf "%s\n" "Data and keys loaded";

  let time f x =
    let t = Sys.time() in
    let fx = f x in
    Printf.printf "Execution time: %fs\n" (Sys.time() -. t);
    f x in

  Format.printf "%s\n" (Big_int.to_string (time (Lib.op0 g) Lib.q));

  let pks = List.map (fun x -> (Big_int.of_string x.public_key.y)) authlist in

  let pk1 = List.nth pks 0 in
  let pk2 = List.nth pks 1 in
  let pk3 = List.nth pks 2 in
  let pk4 = List.nth pks 3 in
  let pkProd = Lib.fpMul (Lib.fpMul (Lib.fpMul pk1 pk2) pk3) pk4 in
  let publicKeysEqual = Big_int.eq_big_int pk pkProd in
  Format.printf "%b\n" publicKeysEqual;

  (* Setup the sigma protocol for 7 choices *)
  let sigmaCorrectEncryption =  Lib.approvalSigma [(g, pk); (g, pk); (g, pk);(g, pk);(g, pk);(g, pk);(g, pk)] in

  let pairFromChoice = (fun (x : Voter_t.choice) ->
    (Big_int.of_string x.choice_alpha, Big_int.of_string x.choice_beta)
  ) in

  let pairFromChoiceAudit = (fun (x : VoterAudit_t.choice) ->
    (Big_int.of_string x.choice_alpha, Big_int.of_string x.choice_beta)
  ) in

  let proofFromProof = (fun g pk (x : Voter_t.answer) n ->
    let choice = List.nth x.choices n in
    let proof0 = List.nth (List.nth x.individual_proofs n) 0 in
    let proof1 = List.nth (List.nth x.individual_proofs n) 1 in

    let s0 = ((g,Big_int.of_string choice.choice_alpha),(pk, Big_int.of_string choice.choice_beta)) in
    let s1 = ((g,Big_int.of_string choice.choice_alpha),(pk, Lib.gdot (Big_int.of_string choice.choice_beta) (Lib.ginv g))) in

    let c0 = (Big_int.of_string proof0.commitment.a, Big_int.of_string proof0.commitment.b) in
    let c1 = (Big_int.of_string proof1.commitment.a, Big_int.of_string proof1.commitment.b) in

    let e0 = Big_int.of_string proof0.challenge in
    let e1 = Big_int.of_string proof1.challenge in

    let t0 = Big_int.of_string proof0.response in
    let t1 = Big_int.of_string proof1.response in

    Obj.magic ((((s0,s1),(c0,c1)),Lib.fadd e0 e1),((t0,e0),t1))
  ) in
 
  let proofFromProof0 = (fun g pk (x : Voter_t.answer) n ->
    let choice = List.nth x.choices n in
    let proof = List.nth (List.nth x.individual_proofs n) 0 in

    let s = ((g,Big_int.of_string choice.choice_alpha),(pk, Big_int.of_string choice.choice_beta)) in
    let c = (Big_int.of_string proof.commitment.a, Big_int.of_string proof.commitment.b) in
    let e = Big_int.of_string proof.challenge in
    let t = Big_int.of_string proof.response in
    Obj.magic (((s,c),e),t)
  ) in

  let proofFromProof1 = (fun g pk (x : Voter_t.answer) n ->
    let choice = List.nth x.choices n in
    let proof = List.nth (List.nth x.individual_proofs n) 1 in

    let s = ((g,Big_int.of_string choice.choice_alpha),(pk, Lib.gdot (Big_int.of_string choice.choice_beta) (Lib.ginv g))) in
    let c = (Big_int.of_string proof.commitment.a, Big_int.of_string proof.commitment.b) in
    let e = Big_int.of_string proof.challenge in
    let t = Big_int.of_string proof.response in
    Obj.magic (((s,c),e),t)
  ) in

  let commitFromProof = (fun (x : Voter_t.proof list) ->
    let proofForZero = List.nth x 0 in
    let proofForOne = List.nth x 1 in
    ((Big_int.of_string proofForZero.commitment.a, Big_int.of_string proofForZero.commitment.b),
     (Big_int.of_string proofForOne.commitment.a, Big_int.of_string proofForOne.commitment.b))
  ) in

  let challengeFromProof  = (fun (x : Voter_t.proof list) ->
    let proofForZero = List.nth x 0 in
    let proofForOne = List.nth x 1 in
    Lib.fadd (Big_int.of_string proofForZero.challenge)
        (Big_int.of_string proofForOne.challenge)) in

  let responseFromProof  = (fun (x : Voter_t.proof list) ->
    let proofForZero = List.nth x 0 in
    let proofForOne = List.nth x 1 in
    ((Big_int.of_string proofForZero.response,
        Big_int.of_string proofForZero.challenge),
      Big_int.of_string proofForOne.response)
  ) in

  let getChoices = (fun (x : Voter_t.voter) ->
    let answer = List.hd x.answers in
    let choices = answer.choices in
    List.map pairFromChoice choices
  ) in

  let getChoicesAudit = (fun (x : VoterAudit_t.answer) ->
    let choices = x.choices in
    List.map pairFromChoiceAudit choices
  ) in

  let getRandomness = (fun x ->
    List.map Big_int.of_string x.randomness
  ) in

  let getStatmentOfCorrectEncrytion = (fun (x : Voter_t.voter) ->
        Lib.approvalSigmaStatment (g,pk) (List.rev (getChoices x))
  ) in

  let mOne = Big_int.of_string "1" in

let getCommitmentOfCorrectEncrytion = (fun (x : Voter_t.voter) ->
    let answer = List.hd x.answers in
    let individual_proofs = answer.individual_proofs in
    let cc = List.map commitFromProof individual_proofs in
    (((((((g,List.nth cc 0), List.nth cc 1), List.nth cc 2),
        List.nth cc 3), List.nth cc 4), List.nth cc 5), List.nth cc 6)
  ) in

  let getChallengeOfCorrectEncrytion = (fun (x : Voter_t.voter) ->
    let answer = List.hd x.answers in
    let individual_proofs = answer.individual_proofs in
    let cc = List.map challengeFromProof individual_proofs in
    (((((((mOne,List.nth cc 0), List.nth cc 1), List.nth cc 2), List.nth cc 3), List.nth cc 4), List.nth cc 5), List.nth cc 6)
  ) in

  let getResponsOfCorrectEncrytion = (fun (x : Voter_t.voter) ->
    let answer = List.hd x.answers in
    let individual_proofs = answer.individual_proofs in
    let cc = List.map responseFromProof individual_proofs in
    (((((((mOne,List.nth cc 0), List.nth cc 1), List.nth cc 2), List.nth cc 3), List.nth cc 4), List.nth cc 5), List.nth cc 6)
  ) in

  let addTwoCiphertexts = (fun x y ->
     ((Lib.gdot (Lib.fst x) (Lib.fst y)),(Lib.gdot (Lib.snd x) (Lib.snd y)))
  ) in

  let addTwoListsOfCiphertexts = (fun x y ->
    List.map2 addTwoCiphertexts x y
  ) in

  let ciphOne = (mOne, mOne) in

  let getSummations = (fun x ->
    let choices = List.map getChoices x in
    let initAcum = [ciphOne;ciphOne;ciphOne;ciphOne;ciphOne;ciphOne;ciphOne] in

    List.fold_left addTwoListsOfCiphertexts initAcum choices
  ) in

  (***
    *   Check ballots
    *
    *   We are currenlty attempting to check the first ballot and segfaulting
    *)

  Format.printf "%s\n" "Preparing encrytion sigma proof";

  Format.print_flush ();


 List.mapi (fun i (x : Voter_t.voter) ->

    let s = getStatmentOfCorrectEncrytion x in
    let c = getCommitmentOfCorrectEncrytion x in
    let e = getChallengeOfCorrectEncrytion x in
    let t = getResponsOfCorrectEncrytion x in

    let result = Lib.Sigma.coq_V1 sigmaCorrectEncryption (Obj.magic (((s, c), e), t)) in

    Format.printf "%i: %b\n" i result;

    Format.print_flush ();


  ) vlist;


 (***
    *   Check audit ballots
    *
    *)

  Format.printf "%s\n" "Audit Ballots";

 List.map (fun (x : VoterAudit_t.answer) ->

    let c = getChoicesAudit x in
    let randomness = getRandomness x in

    let choiceIndex = [0;1;2;3;4;5;6] in

    List.map (fun i ->
        let result = Lib.ALES.decryptsToExt (g,pk) (List.nth c i) g (List.nth randomness i) in
         Format.printf "%b\n"  result;
    ) choiceIndex;

 ) audit.answers;

  (***
    *   End check ballots
    *
    *)

  Format.printf "%s\n" "Beginning summation";

  Format.print_flush ();

  let summations = getSummations vlist in

  Format.printf "%s\n" (Big_int.string_of_big_int (Lib.fst (List.hd summations)));

  Format.printf "%s\n" (Big_int.string_of_big_int pk);

  let result = [253,137,155,203,93,178,170] in

  let getNthDecFac = (fun n auths ->
    List.map (fun x ->
        let decFacQ1 = List.hd x.decryption_factors in
        List.nth decFacQ1 n
    ) auths
  ) in

  (* We need to refactor proof *)
  let getCommitmentOfCorrectDecrytionN = (fun auth n ->
     let com = List.map (fun x ->
        let decPrQ1 = List.hd x.decryption_proofs in
        (Big_int.of_string (List.nth decPrQ1 n).commitment.a, Big_int.of_string (List.nth decPrQ1 n).commitment.b)
     ) auth in
     (((List.nth com 0, List.nth com 1), List.nth com 2),List.nth com 3)
  ) in

  let getChallengeOfCorrectDecrytionN = (fun auth n ->
    let chal = List.map (fun x ->
      let decPrQ1 = List.hd x.decryption_proofs in
      Big_int.of_string (List.nth decPrQ1 n).challenge
    ) auth in
    (((List.nth chal 0, List.nth chal 1), List.nth chal 2),List.nth chal 3)
  ) in

  let getResponsOfCorrectDecrytionN = (fun auth n ->
    let chal = List.map (fun x ->
      let decPrQ1 = List.hd x.decryption_proofs in
      Big_int.of_string (List.nth decPrQ1 n).response
    ) auth in
    (((List.nth chal 0, List.nth chal 1), List.nth chal 2),List.nth chal 3)
  ) in

    (***
    *   Check decrytion
    * c:= ((((M*M)*(M*M))*((M*M)*(M*M)))*((M*M)*(M*M)))*((M*M)*(M*M))
    * e1 := ((R*R)*R)*R
    * t1 := ((R*R)*R)*R
    *
    *)

  let pkTuple = ((((g,List.nth pks 0), (g,List.nth pks 1)), (g,List.nth pks 2)), (g,List.nth pks 3)) in

  (* We create a list of choice index to map over *)
  let choiceIndex = [0;1;2;3;4;5;6] in

  List.map (fun i ->

        let decFac = (getNthDecFac i authlist) in
        let decFacTuple = (((Big_int.of_string (List.nth decFac 0), Big_int.of_string (List.nth decFac 1)), Big_int.of_string (List.nth decFac 2)), Big_int.of_string (List.nth decFac 3)) in


        let sigmaCorrectDecryption =  Lib.decryptionSigma in

        Format.printf "%s\n" "Preparing decryption sigma proof";

        Format.print_flush ();

        let sd = Lib.decryptionSigmaStatment (List.nth summations i) pkTuple decFacTuple in
        let cd = getCommitmentOfCorrectDecrytionN authlist i in
        let ed = getChallengeOfCorrectDecrytionN authlist i in
        let td = getResponsOfCorrectDecrytionN authlist i in

        let inputD =  Obj.magic (((sd, cd), ed), td) in
        let result = sigmaCorrectDecryption.coq_V1 inputD in

        Format.printf "%b\n"  result;
  ) choiceIndex;

   Format.printf "%s\n" "All done";

    (***
    *   End check decryption
    *
    *)
