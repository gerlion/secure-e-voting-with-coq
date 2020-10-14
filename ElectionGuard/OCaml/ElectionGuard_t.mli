(* Auto-generated from "ElectionGuard.atd" *)
              [@@@ocaml.warning "-27-32-35-39"]

type pkproof = { commitment: string; challenge: string; response: string }

type trustee_public_key = { public_key: string; proof: pkproof }

type commitment = { public_key: string; ciphertext: string }

type proof = { commitment: commitment; challenge: string; response: string }

type decproof = { recovery: string option; proof: proof; share: string }

type ciphertext = { public_key: string; ciphertext: string }

type spoil = {
  cleartext: string;
  decrypted_message: string;
  encrypted_message: ciphertext;
  shares: decproof list
}

type parameters = {
  date: string;
  location: string;
  num_trustees: string;
  threshold: string;
  prime: string;
  generator: string
}

type message = { message: ciphertext; zero_proof: proof; one_proof: proof }

type decrypt = {
  cleartext: string;
  decrypted_tally: string;
  encrypted_tally: ciphertext;
  shares: decproof list
}

type contest = {
  selections: message list;
  max_selections: string;
  num_selections_proof: proof
}

type ballot_info = {
  date: string;
  device_info: string;
  time: string;
  tracker: string
}

type ballotspoiled = { ballot_info: ballot_info; contests: spoil list list }

type ballot = { ballot_info: ballot_info; contests: contest list }

type election = {
  parameters: parameters;
  base_hash: string;
  trustee_public_keys: trustee_public_key list list;
  joint_public_key: string;
  extended_base_hash: string;
  cast_ballots: ballot list;
  contest_tallies: decrypt list list;
  spoiled_ballots: ballotspoiled list
}
