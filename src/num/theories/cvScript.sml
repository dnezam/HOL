open HolKernel Parse boolLib IndDefLib

open arithmeticTheory BasicProvers simpLib

fun simp ths = ASM_SIMP_TAC (srw_ss()) ths
fun SRULE ths = SIMP_RULE (srw_ss()) ths

val _ = new_theory "cv";

val N0_def = new_definition("N0_def",
  “N0 (m:num) n = if n = 0 then m+1 else 0”);

val P0_def = new_definition("P0_def",
  “P0 (c:num -> num) d n =
   if n = 0 then 0
   else if ODD n then c (n DIV 2)
   else d ((n-2) DIV 2)”);

Theorem N0_11[local,simp]:
  N0 m = N0 n <=> m = n
Proof
  simp[FUN_EQ_THM, N0_def, EQ_IMP_THM] >>
  disch_then $ Q.SPEC_THEN ‘0’ mp_tac >> simp[EQ_MONO_ADD_EQ]
QED

Theorem simple_inequalities[local,simp]:
  1 <> 0 /\ 2 <> 0
Proof
  simp[ONE, TWO]
QED

Theorem ODD12[local,simp]:
  ODD 1 /\ ~ODD 2
Proof
  simp[ONE, TWO, ODD]
QED

Theorem ONE_DIV2[local,simp]:
  1 DIV 2 = 0
Proof
  simp[ONE, TWO, prim_recTheory.LESS_MONO_EQ, prim_recTheory.LESS_0,
       LESS_DIV_EQ_ZERO]
QED

Theorem P0_11[local,simp]:
  P0 c d = P0 e f <=> c = e /\ d = f
Proof
  simp[FUN_EQ_THM, P0_def, EQ_IMP_THM] >> rpt strip_tac
  >- (Q.RENAME_TAC [‘c x = e x’] >>
      pop_assum $ Q.SPEC_THEN ‘2 * x + 1’ mp_tac >>
      simp[ADD_EQ_0, ADD_CLAUSES, ODD_ADD, ODD_MULT]) >>
  Q.RENAME_TAC [‘d x = f x’] >>
  pop_assum $ Q.SPEC_THEN ‘2 * x + 2’ mp_tac >>
  simp[ADD_EQ_0, ADD_CLAUSES, ODD_ADD, ODD_MULT, MULT_EQ_0, ADD_SUB]
QED

Inductive iscv:
[~num:] (!m. iscv (N0 m)) /\
[~pair:] (!c d. iscv c /\ iscv d ==> iscv (P0 c d))
End

val cv_tydefrec = newtypeTools.rich_new_type("cv",
  prove(“?cv. iscv cv”,
        Q.EXISTS_TAC ‘N0 0’ >> REWRITE_TAC[iscv_num]))

val Pair_def = new_definition("Pair_def",
  “Pair c d = cv_ABS (P0 (cv_REP c) (cv_REP d))”);

Theorem Pair_11:
  Pair c d = Pair e f <=> c = e /\ d = f
Proof
  simp[Pair_def, EQ_IMP_THM] >> strip_tac >>
  drule_at (Pat ‘cv_ABS _ = cv_ABS _’)
           (iffLR $ #term_ABS_pseudo11 cv_tydefrec) >>
  simp[#termP_term_REP cv_tydefrec, iscv_pair, #term_REP_11 cv_tydefrec]
QED

val Num_def = new_definition("Num_def", “Num n = cv_ABS (N0 n)”);

Theorem Num_11:
  Num m = Num n <=> m = n
Proof
  simp[Num_def, EQ_IMP_THM] >> strip_tac >>
  drule_at (Pat ‘cv_ABS _ = cv_ABS _’)
           (iffLR $ #term_ABS_pseudo11 cv_tydefrec) >>
  simp[iscv_num]
QED

Theorem cv_distinct:
  Num n <> Pair c d
Proof
  simp[Num_def, Pair_def] >> strip_tac >>
  drule_at (Pat ‘cv_ABS _ = cv_ABS _’)
           (iffLR $ #term_ABS_pseudo11 cv_tydefrec) >>
  simp[iscv_num, iscv_pair, #termP_term_REP cv_tydefrec] >>
  simp[N0_def, P0_def, FUN_EQ_THM] >> Q.EXISTS_TAC ‘0’ >>
  simp[ADD_EQ_0]
QED

Theorem cv_induction =
        iscv_strongind |> Q.SPEC ‘λc0. P (cv_ABS c0)’
                       |> BETA_RULE
                       |> SRULE [GSYM Num_def]
                       |> SRULE [#termP_exists cv_tydefrec, PULL_EXISTS,
                                 GSYM Pair_def, #absrep_id cv_tydefrec]
                       |> Q.GEN ‘P’

Inductive cvrel:
[~num:]
  (!n. cvrel f g (Num n) (f n)) /\
[~pair:]
  (!c d rc rd. cvrel f g c rc /\ cvrel f g d rd ==>
               cvrel f g (Pair c d) (g c d rc rd))
End

Theorem cvrel_exists:
  !f g c. ?r. cvrel f g c r
Proof
  ntac 2 gen_tac >> ho_match_mp_tac cv_induction >> rpt strip_tac
  >- irule_at Any cvrel_num >>
  irule_at Any cvrel_pair >> rpt (first_assum $ irule_at Any)
QED

Theorem cvrel_unique:
  !c r1. cvrel f g c r1 ==>
         !r2. cvrel f g c r2 ==> r1 = r2
Proof
  ho_match_mp_tac cvrel_strongind >> rpt strip_tac
  >- (pop_assum mp_tac >> simp[Once cvrel_cases] >>
      simp[Num_11,cv_distinct]) >>
  Q.PAT_X_ASSUM ‘cvrel _ _ (Pair _ _) _’ mp_tac>>
  simp[Once cvrel_cases] >> simp[cv_distinct, Pair_11]>>
  metisLib.METIS_TAC[]
QED

val cvrelf_def = new_definition("cvrelf_def",
                                “cvrelf f g c = @r. cvrel f g c r”);

Theorem cvrelf_Pair:
  cvrelf f g (Pair c d) = g c d (cvrelf f g c) (cvrelf f g d)
Proof
  CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss()) [cvrelf_def])) >>
  SELECT_ELIM_TAC>> conj_tac
  >- (irule_at Any cvrel_exists) >>
  simp[Once cvrel_cases, cv_distinct, Pair_11, PULL_EXISTS] >>
  rpt strip_tac >>
  Q.SUBGOAL_THEN ‘cvrelf f g c = rc /\ cvrelf f g d = rd’ strip_assume_tac
  >- (simp[cvrelf_def] >> conj_tac >> SELECT_ELIM_TAC >>
      metisLib.METIS_TAC[cvrel_unique]) >>
  simp[]
QED

Theorem cv_Axiom:
  !f g. ?h. (!n. h (Num n) = f n) /\
            (!c d. h (Pair c d) = g c d (h c) (h d))
Proof
  rpt gen_tac >> Q.EXISTS_TAC ‘cvrelf f g’ >> simp[cvrelf_Pair] >>
  simp[cvrelf_def, Once cvrel_cases, Num_11, cv_distinct]
QED

(* helpers/auxiliaries *)
val c2b_def = new_definition ("c2b_def", “c2b x = ?k. x = Num (SUC k)”);
val cv_if_def = new_definition(
  "cv_if_def",
  “cv_if p (q:cv) (r:cv) = if c2b p then q else r”);

val cv_case_def = Prim_rec.new_recursive_definition {
  name = "cv_case_def",
  rec_axiom = cv_Axiom,
  def = “cv_CASE (Num n) nmf prf = nmf n /\
         cv_CASE (Pair c d) nmf prf = prf c d”};

Overload case = “cv_CASE”

val cv_size_def = Prim_rec.new_recursive_definition {
  name = "cv_size_def",
  rec_axiom = cv_Axiom,
  def = “cv_size (Num n) = 1 + n /\
         cv_size (Pair c d) = 1 + (cv_size c + cv_size d)”};

val _ = TypeBase.export (
    TypeBasePure.gen_datatype_info{
      ax = cv_Axiom, ind = cv_induction, case_defs = [cv_case_def]
    } |> map (TypeBasePure.put_size (“cv_size”, TypeBasePure.ORIG cv_size_def))
)

fun recdef (n,t) =
  Prim_rec.new_recursive_definition{name = n, def = t, rec_axiom = cv_Axiom}

val cv_fst_def = recdef("cv_fst_def",
                       “cv_fst (Num n) = Num 0 /\ cv_fst (Pair c d) = c”);
val cv_snd_def = recdef("cv_snd_def",
                       “cv_snd (Num n) = Num 0 /\ cv_snd (Pair c d) = d”);
val cv_ispair_def = recdef("cv_ispair_def",
                           “cv_ispair (Num n) = Num 0 /\
                            cv_ispair (Pair c d) = Num (SUC 0)”);

val b2c_def = Prim_rec.new_recursive_definition{
  def = “b2c T = Num (SUC 0) /\ b2c F = Num 0”,
  rec_axiom = TypeBase.axiom_of “:bool”,
  name = "b2c_def"};

Theorem b2c_if:
  b2c g = if g then Num (SUC 0) else Num 0
Proof
  Cases_on ‘g’ >> simp[b2c_def]
QED

val cv_lt_def0 = recdef(
  "cv_lt_def0",
  “cv_lt (Num m) c = (case c of | Num n => b2c (m < n) | _ => Num 0) /\
   cv_lt (Pair c d) e = Num 0”);

Theorem cv_lt_def:
  cv_lt (Num m) (Num n) = Num (if m < n then SUC 0 else 0) /\
  cv_lt (Num m) (Pair c d) = Num 0 /\
  cv_lt (Pair c d) (Num m) = Num 0 /\
  cv_lt (Pair c1 d1) (Pair c2 d2) = Num 0
Proof
  simp[cv_lt_def0, b2c_if, SF boolSimps.COND_elim_ss]
QED

Inductive isnseq:
[~nil:] isnseq (Num 0) /\
[~cons:] (!n c. isnseq c ==> isnseq (Pair n c))
End

val cvnumval_def = recdef(
  "cvnumval_def",
  “cvnumval (Num n) = n /\ cvnumval (Pair c d) = 0”
);

val cvnum_map2_def = new_definition(
  "cvnum_map2_def",
  “cvnum_map2 f c d = Num (f (cvnumval c) (cvnumval d))”);

val cv_add_def0 = new_definition ("cv_add_def0", “cv_add = cvnum_map2 $+”);
Theorem cv_add_def[simp]:
  cv_add (Num m) (Num n) = Num (m + n) /\
  cv_add (Num m) (Pair c d) = Num m /\
  cv_add (Pair c d) (Num m) = Num m /\
  cv_add (Pair c d) (Pair e f) = Num 0
Proof
  simp[cv_add_def0, FUN_EQ_THM,cvnumval_def, cvnum_map2_def, ADD_CLAUSES]
QED

val cv_sub_def0 = new_definition("cv_sub_def0", “cv_sub = cvnum_map2 $-”);
Theorem cv_sub_def[simp]:
  cv_sub (Num m) (Num n) = Num (m - n) /\
  cv_sub (Num m) (Pair p q) = Num m /\
  cv_sub (Pair p q) (Num n) = Num 0 /\
  cv_sub (Pair p q) (Pair r s) = Num 0
Proof
  simp[cv_sub_def0, FUN_EQ_THM, cvnum_map2_def, cvnumval_def, SUB_0]
QED

val cv_mul_def0 = new_definition("cv_mul_def0", “cv_mul = cvnum_map2 $*”);
Theorem cv_mul_def[simp]:
  cv_mul (Num m) (Num n) = Num (m * n) /\
  cv_mul (Num m) (Pair p q) = Num 0 /\
  cv_mul (Pair p q) (Num n) = Num 0 /\
  cv_mul (Pair p q) (Pair r s) = Num 0
Proof
  simp[cv_mul_def0, FUN_EQ_THM, cvnum_map2_def, cvnumval_def]
QED

val cv_div_def0 = new_definition("cv_div_def0", “cv_div = cvnum_map2 $DIV”);
Theorem cv_div_def[simp]:
  cv_div (Num m) (Num n) = Num (m DIV n) /\
  cv_div (Num m) (Pair p q) = Num 0 /\
  cv_div (Pair p q) (Num n) = Num 0 /\
  cv_div (Pair p q) (Pair r s) = Num 0
Proof
  simp[cv_div_def0, FUN_EQ_THM, cvnum_map2_def, cvnumval_def]
QED

val cv_mod_def0 = new_definition("cv_mod_def0", “cv_mod = cvnum_map2 $MOD”);
Theorem cv_mod_def[simp]:
  cv_mod (Num m) (Num n) = Num (m MOD n) /\
  cv_mod (Num m) (Pair p q) = Num m /\
  cv_mod (Pair p q) (Num n) = Num 0 /\
  cv_mod (Pair p q) (Pair r s) = Num 0
Proof
  simp[cv_mod_def0, FUN_EQ_THM, cvnum_map2_def, cvnumval_def]
QED



val _ = export_theory();