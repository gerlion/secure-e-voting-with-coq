open Core.Std
open Yojson.Basic.Util 

let () =
   let json = Yojson.Basic.from_file "v1003.json" in
   let voter = json |> member "answers" |> member "choices" |>
	member "alpha" |> to_string in
    printf "Voter: %s\n" voter;