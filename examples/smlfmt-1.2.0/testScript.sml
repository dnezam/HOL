(* above *)
open HolKernel (* A *) Parse boolLib bossLib;

(* C *) open HolKernel Parse boolLib bossLib (* right *)

 open HolKernel Parse boolLib bossLib;
(* below *)

val _ = new_theory "joe"
