(* Automatically migrate to new Theory syntax introduced in HOL#1364 (GitHub) *)

open Parser


exception Fail of string

fun parse file = let
  val s = TextIO.openIn file
  fun readFile acc = case TextIO.inputLine s of
    SOME line => readFile (line :: acc)
  | NONE => (TextIO.closeIn s; concat (rev acc))
  val body = readFile []
  val infixes =
    map (fn x => (x, 0, false)) ["++", "&&", "|->", "THEN", "THEN1",
      "THENL", "THEN_LT", "THENC", "ORELSE", "ORELSE_LT", "ORELSEC", "THEN_TCL",
      "ORELSE_TCL", "?>", "|>", "|>>", "||>", "||->",
      ">>", ">-", ">|", "\\\\", ">>>", ">>-", "??", ">~", ">>~", ">>~-"] @
    [("by", 8, false), ("suffices_by", 8, false), ("$", 1, true)] @
    List.concat (map (fn ((b, a), l) => map (fn x => (x, a, b)) l) [
      ((false, 7), ["*", "/", "div", "mod"]),
      ((false, 6), ["+", "-", "^"]),
      ((true, 5), ["::", "@"]),
      ((false, 4), ["=", "<>", ">", ">=", "<", "<="]),
      ((false, 3), [":=", "o"]),
      ((false, 0), ["before"])])
  val sc = foldl
    (fn ((k, n, r), b) => Binarymap.insert (b, k, (n, r)))
    (Binarymap.mkDict String.compare) infixes
  val {parseDec, ...} = Parser.parseSML file body
    (fn (start, stop) => fn err =>
      (print (concat ["error ", Int.toString start, "-",
        Int.toString stop, ": ", err, "\n"])
        ; raise Bind
        ))
    sc
  fun pull acc = case parseDec () of
    SOME dec => pull (dec :: acc)
  | NONE => List.rev acc
in pull [] end;

val file = "/home/daniel/code/cakeml/semantics/astScript.sml";

val decs = parse file;

(* val .. = name arg <;>*)
fun destCall dec = let
  val DecVal {elems, ...} = dec
  val {args = [vb], ...} = elems
  val {eq = SOME ({exp = exp, ...}), ...} = vb
  val App (Ident {id = (_, name), ...}, arg) = exp
in SOME (name, arg) end handle Bind => NONE

(* local dec1 in dec2 end <;> *)
fun destLocal dec = let
  val DecLocal {dec1, dec2, ...} = dec
in SOME (dec1, dec2) end handle Bind => NONE

fun destStringConstant exp = let
  val StringConstant (_, s) = exp
in SOME s end handle Bind => NONE

fun isCallTo fname dec =
  case destCall dec of SOME (cname, _) => fname = cname | _ => false

fun isSemi dec = case dec of DecSemi _ => true | _ => false

fun isOpen dec = case dec of DecOpen _ => true | _ => false

(* local open ..<;> open .. <;> in end *)
fun isLocalOpen dec =
  case destLocal dec of
    SOME (dec1, []) => List.all (fn dec => isOpen dec orelse isSemi dec) dec1
  | _ => false

(* Include semicolons that follow *)
fun filterDecs filter decs =
  case decs of
    [] => []
  | [dec] => if filter dec then [dec] else []
  | dec1::dec2::rest =>
    if filter dec1 then (
      if isSemi dec2
      then dec1::dec2::(filterDecs filter rest)
      else dec1::(filterDecs filter rest))
    else filterDecs filter (dec2::rest)

fun sing xs = case xs of [x] => x | _ => raise Bind

;

val newTheoryCall = filterDecs (isCallTo "new_theory") decs;

val theoryName =
  newTheoryCall
  |> List.filter (not o isSemi)
  |> sing |> destCall |> Option.valOf |> #2
  |> destStringConstant |> Option.valOf;

val setGrammarAncestryCall = filterDecs (isCallTo "set_grammar_ancestry") decs;

val openDecs = filterDecs isOpen decs;

val localOpenDecs = filterDecs isLocalOpen decs;

