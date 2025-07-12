(* Automatically migrate to new Theory syntax introduced in HOL#1364 (GitHub) *)

open Parser


exception Fail of string

val file = "/home/daniel/code/cakeml/semantics/astScript.sml";
val file = "./testScript.sml"

val s = TextIO.openIn file

fun readFile acc = case TextIO.inputLine s of
  SOME line => readFile (line :: acc)
| NONE => (TextIO.closeIn s; concat (rev acc))

val body = readFile []

fun parse file = let
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

fun destList exp = let
  val List {elems, ...} = exp
  val {args, ...} = elems
in SOME args end handle Bind => NONE  

fun destOpen dec = let
  val DecOpen {elems, ...} = dec
  val openNames = map #2 elems
in SOME openNames end handle Bind => NONE

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
      else dec1::(filterDecs filter (dec2::rest)))
    else filterDecs filter (dec2::rest)

fun identStop (start, content) = start + String.size content

fun boundingBox dec =
  case dec of
    DecSemi s => (s, s+1)
  | DecVal {val_, elems, ...} => raise Fail "todo"
  | DecOpen {open_, elems} => (case elems of
      [] => (open_, open_ + 4)
    | _ => (open_, identStop (List.last elems)))
  | DecLocal {local_, end_, ...} =>  raise Fail "todo"
  | _ => raise Fail "unsupported for now"

fun boundingBoxes decs =
  case decs of
    [] => []
  | [dec] => [boundingBox dec]
  | dec1::dec2::rest => case dec2 of
      DecSemi i => let
      val (start, _) = boundingBox dec1
    in (start, i + 1)::boundingBoxes rest end
    | _ => boundingBox dec1::boundingBoxes (dec2::rest)

fun expandBox (start, stop) = raise Fail "todo"

fun hasComment (start, stop) = raise Fail "todo"

fun sing xs = (case xs of [x] => x | _ => raise Bind)

fun stripStringQuotes s = String.substring (s, 1, String.size s - 2)

fun stripTheory s = String.substring (s, 0, String.size s - 6)

fun mapOption _ [] = SOME []
  | mapOption f (x::xs) = 
    case f x of
        NONE => NONE
      | SOME y => 
        case mapOption f xs of
            NONE => NONE
          | SOME ys => SOME (y::ys)

fun mem _ [] = false
  | mem y (x::xs) = if x = y then true else mem y xs
;

fun lookup _ [] = raise Option
  | lookup y ((x,v)::xs) = if x = y then v else lookup y xs

datatype attr = IgnoreGrammar | NoBind

(* yoinked from mario *)
fun mkLineCounter str = let
  fun loop i ls =
    if i >= String.size str then Vector.fromList (List.rev ls)
    else
      let val c = String.sub (str, i)
      in loop (i+1) (if c = #"\n" then i+1::ls else ls) end
  in loop 0 [] end

fun partitionPoint len pred = let
  fun loop start len =
    if len = 0 then start
    else let
      val half = len div 2
      val middle = start + half
      in
        if pred middle
        then loop (middle + 1) (len - (half + 1))
        else loop start half
      end
  in loop 0 len end

fun getLineCol lines index = let
  val line = partitionPoint (Vector.length lines) (fn i => Vector.sub (lines, i) <= index)
  in (line, index - (if line = 0 then 0 else Vector.sub (lines, line - 1))) end

fun fromLineCol lines (line, col) =
  if line = 0 then col else Vector.sub (lines, line - 1) + col

val lines = mkLineCounter body

fun subTotal i = String.sub (body, i) handle Subscript => #"\000"

fun substringTotal i j =
  String.substring (body, i, j) handle Subscript => "\000"

fun isWhitespace c =
  c = #" " orelse c =  #"\t"

fun expandRight start = let
  fun loop i = if isWhitespace $ subTotal i then loop (i + 1) else i
  in loop start end

fun expandLeft start = let
  fun loop i = if isWhitespace $ subTotal (i - 1)then loop (i - 1) else i
  in loop start end

fun expandBox (start, stop) = (expandLeft start, expandRight stop)

fun maybeContainsComment (start, stop) = let
  val s = String.substring (body, start, stop - start)
  in String.isSubstring "(*" s orelse String.isSubstring "*)" s end

(* After expandBox, the next "token" is either a newline, or something else *)
fun checkCommentLeft start = let
  fun loop i =
    if substringTotal (i - 2) 2 = "*)" then SOME (i - 2)
    else if subTotal (i - 1) = #"\n" then NONE
    else if subTotal (i - 1) = #"\000" then NONE
    else checkCommentLeft (i - 1)
  in
    if subTotal (start - 1) = #"\n" then loop (start - 1)
    else loop start end

;

(* new_theory call *)

val newTheoryCall = filterDecs (isCallTo "new_theory") decs;

val theoryName =
  newTheoryCall
  |> List.filter (not o isSemi)
  |> sing |> destCall |> Option.valOf |> #2
  |> destStringConstant |> Option.valOf
  |> stripStringQuotes;

  
(* open decs *)

fun getLineColBox (start, stop) =
  (getLineCol lines start, getLineCol lines stop)

val openDecs = filterDecs isOpen decs;

val openBoxes = openDecs |> boundingBoxes |> map expandBox

val test =
  openBoxes
  |> List.mapPartial (fn (l,_) => checkCommentLeft l)
  |> map $ getLineCol lines

val warnDeletingComment =
  openBoxes |> List.filter maybeContainsComment

val (openTheories, openLibs) =
  openDecs
  |> List.filter (not o isSemi)
  |> mapOption destOpen |> Option.valOf
  |> List.concat
  |> List.partition (String.isSuffix "Theory")

val localOpenDecs = filterDecs isLocalOpen decs;

val (localOpenTheories, localOpenLibs) =
  localOpenDecs
  |> List.filter (not o isSemi)
  |> mapOption destLocal |> Option.valOf
  |> map #1 |> List.concat
  |> mapOption destOpen |> Option.valOf
  |> List.concat
  |> List.partition (String.isSuffix "Theory")

val localOpenTheories =
  List.filter (fn x => not (mem x openTheories)) localOpenTheories
  |> map (fn x => (stripTheory x, [NoBind]))

val openTheories: (string * attr list) list =
  map (fn x => (stripTheory x, [])) openTheories

val _ = if localOpenLibs <> [] then raise Fail "localOpenLibs not empty" else ()

val allTheories = openTheories @ localOpenTheories

val setGrammarAncestryCall = filterDecs (isCallTo "set_grammar_ancestry") decs;

val grammarAncestry =
  setGrammarAncestryCall
  |> List.filter (not o isSemi)
  |> sing |> destCall |> Option.valOf |> #2
  |> destList |> Option.valOf
  |> mapOption destStringConstant |> Option.valOf
  |> map stripStringQuotes

val grammarTheories =
  map (fn n => (n, lookup n allTheories)) grammarAncestry

val ignoreGrammarTheories =
  List.filter (fn (x,_) => not (mem x grammarAncestry)) allTheories
  |> map (fn (x,attrs) => (x,attrs @ [IgnoreGrammar]))

val exportTheoryCall = filterDecs (isCallTo "export_theory") decs;

(* TODO 
    - find beginning where we want to insert block
    - implement case where there is no set_grammar_ancestry
    - implement warning function if there is a comment within
      or around block we are going to delete
    - implement deletion function
    - implement function that actually writes the block
    - implement auto-fill for names
*)


