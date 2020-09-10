let _ =

  Format.printf "%s\n" "Loading data";

  let wikSigma = Lib.ElGamalWikstrom.coq_WikstromSigma in
  let wikStatment = Lib.ElGamalWikstrom.coq_WikstromStatment in
  
  Format.printf "%s\n" (Big_int.string_of_big_int Lib.p);
  Format.printf "%s\n" (Big_int.string_of_big_int Lib.q);

  let toVector2 = (fun x y ->
    Lib.Cons (Big_int.big_int_of_string x, (Lib.S Lib.O), Lib.Cons (Big_int.big_int_of_string y, Lib.O, Lib.Nil))
  ) in
  
  let toVector2Ciph = (fun x y z w ->
    Lib.Cons ((Big_int.big_int_of_string x,Big_int.big_int_of_string y), (Lib.S Lib.O), Lib.Cons ((Big_int.big_int_of_string z, Big_int.big_int_of_string w), Lib.O, Lib.Nil))
  ) in

  (* Transcript *)
  let pk = (Big_int.big_int_of_string "3", Big_int.big_int_of_string "3") in
  let h = Big_int.big_int_of_string "3" in
  let hs = toVector2 "9" "3" in
  let c = toVector2 "5" "5" in (* PermutationCommitment01.json *)
  let cHat = toVector2 "1" "3" in
  let u = toVector2 "0" "0" in
  let e = toVector2Ciph "5" "1" "3" "4" in    (* Ciphertexts01.json index 0 *)
  let e' = toVector2Ciph "5" "1" "3" "4" in (* Ciphertexts01.json index 1 *)
  
  Format.printf "%s\n" "Data loaded";

  Format.print_flush ();
  
  let statment = wikStatment pk h h hs c cHat u e e' in
  
  Format.printf "%s\n" "Statment Prepared";
  
  let t1 = Big_int.big_int_of_string "3" in
  let t2 = Big_int.big_int_of_string "3" in
  let t3 = Big_int.big_int_of_string "5" in
  let t4 = (Big_int.big_int_of_string "5", Big_int.big_int_of_string "9") in
  let tHat = toVector2 "3" "9" in
  
  let com = Obj.magic ((t1,t2),((t3,t4),tHat)) in
  let chal = Big_int.big_int_of_string "0" in
  
  let s1 = Big_int.big_int_of_string "1" in
  let s2 = Big_int.big_int_of_string "1" in
  let s3 = Big_int.big_int_of_string "1" in
  let s4 = Big_int.big_int_of_string "2" in
  let sHat = toVector2 "3" "2" in
  let sPrime = toVector2 "3" "1" in
  
  let resp = Obj.magic ((s1, s2), (((sPrime, s3), s4), sHat))  in
  
  Format.printf "%s\n" "Transcript Prepared";
  Format.print_flush ();
  
  let result = wikSigma.coq_V1 (((statment, com), chal), resp) in
  
  Format.printf "%b\n" result;

    Format.print_flush ();
  
  Format.printf "%s\n" "All done";
