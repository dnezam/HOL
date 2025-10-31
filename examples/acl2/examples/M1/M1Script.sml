(*****************************************************************************)
(* Create "M1Theory"                                                         *)
(*****************************************************************************)

(* Commands when run interactively:
quietdec := true;                                    (* Switch off output    *)

map load ["imported_acl2Theory"];
open imported_acl2Theory;

quietdec := false;                                   (* Restore output       *)
*)

Theory M1
Ancestors
  complex_rational acl2_package sexp imported_acl2
Libs
  stringLib sexp

val simp_fn =
 SIMP_RULE
  list_ss
  ([let_simp,andl_fold,itel_fold,itel_append,
    forall2_thm,exists2_thm,forall_fold,exists_fold,
    implies,andl_simp,not_simp,t_nil]
   @
   (map GSYM [int_def,nat_def,List_def,asym_def,csym_def,ksym_def,osym_def]));

(******************************************************************************
M1 contains simplified definitions and theorems from other theories
******************************************************************************)

Theorem exclaim_def = simp_fn exclaim_defun

Theorem ifact_def = simp_fn ifact_defun

Theorem ifact_lemma = simp_fn ifact_lemma_thm

Theorem ifact_is_factorial = simp_fn ifact_is_factorial_thm

Theorem ifact_correct = simp_fn ifact_correct_thm

Theorem repeat_def = simp_fn repeat_defun

Theorem ifact_sched_def = simp_fn ifact_sched_defun

Theorem test_ifact_examples = simp_fn test_ifact_examples_thm
