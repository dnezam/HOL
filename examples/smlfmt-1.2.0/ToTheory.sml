open Parser

val file = "/home/daniel/code/cakeml/semantics/astScript.sml";

(* fun apply file = let *)
  (* SML/HOL parsing *)
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

  (* General helpers *)
  fun fail msg = raise Fail msg
  
  fun assert b msg = if not b then fail msg else ()

  fun sing xs = (case xs of [x] => x | _ => fail "sing: Not a singleton")

  fun mem _ [] = false
    | mem y (x::xs) = if x = y then true else mem y xs

  fun mapOption _ [] = SOME []
    | mapOption f (x::xs) = 
      case f x of
          NONE => NONE
        | SOME y => 
          case mapOption f xs of
              NONE => NONE
            | SOME ys => SOME (y::ys)

  fun lookup _ [] = fail "lookup: Did not find element"
    | lookup y ((x,v)::xs) = if x = y then v else lookup y xs

  (* Parsing *)
  fun isEOF i = String.size body <= i
  fun isWhitespace c = (c = #" " orelse c =  #"\t")

  fun sub i = String.sub (body, i) handle Subscript => #"\000"

  fun substring i j =
    String.substring (body, i, j) handle Subscript => "\000"

  fun parseComment start = let
    fun loop i depth =
      if substring i 2 = "(*" then
        loop (i + 2) (depth + 1)
      else if substring i 2 = "*)" then 
        if depth <= 0 then (start, i + 2) else loop (i + 2) (depth - 1)
      else if isEOF i then raise Fail "Unterminated comment"
      else loop (i + 1) depth
    in
      if substring start 2 = "(*"
      then loop (start + 2) 0
      else fail "Expected comment" end

  fun stripStringQuotes s = String.substring (s, 1, String.size s - 2)
  fun stripTheory s = String.substring (s, 0, String.size s - 6)

  (* Potential false positives if we have the opening or closing
   * comment within a string literal *)
  fun maybeContainsComment (start, stop) = let
    val s = String.substring (body, start, stop - start)
    in String.isSubstring "(*" s orelse String.isSubstring "*)" s end

  (* AST *)
  fun destStringConstant exp = let
    val StringConstant (_, s) = exp
  in SOME s end handle Bind => NONE

  fun destOpen dec = let
    val DecOpen {elems, ...} = dec
    val openNames = map #2 elems
  in SOME openNames end handle Bind => NONE

  (* local dec1 in dec2 end <;> *)
  fun destLocal dec = let
    val DecLocal {dec1, dec2, ...} = dec
  in SOME (dec1, dec2) end handle Bind => NONE

  (* val .. = name arg <;>*)
  fun destCall dec = let
    val DecVal {elems, ...} = dec
    val {args = [vb], ...} = elems
    val {eq = SOME ({exp = exp, ...}), ...} = vb
    val App (Ident {id = (_, name), ...}, arg) = exp
  in SOME (name, arg) end handle Bind => NONE

  fun destList exp = let
    val List {elems, ...} = exp
    val {args, ...} = elems
  in SOME args end handle Bind => NONE  

  fun isOpen dec = case dec of DecOpen _ => true | _ => false
  fun isSemi dec = case dec of DecSemi _ => true | _ => false

  (* local open ..<;> open .. <;> in end *)
  fun isLocalOpen dec =
    case destLocal dec of
      SOME (dec1, []) => List.all (fn dec => isOpen dec orelse isSemi dec) dec1
    | _ => false

  fun isCallTo fname dec =
    case destCall dec of SOME (cname, _) => fname = cname | _ => false

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

  (* Attributes *)
  datatype attr = IgnoreGrammar | NoBind

  (* Bounding boxes *)
  (* (start [inclusive], stop [exclusive]) *)

  (* Find bounding boxes *)
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

  (* Merge boxes of declaration and semicolon that follow immediately *)
  fun boundingBoxes decs =
    case decs of
      [] => []
    | [dec] => [boundingBox dec]
    | dec1::dec2::rest => case dec2 of
        DecSemi i => let
        val (start, _) = boundingBox dec1
      in (start, i + 1)::boundingBoxes rest end
      | _ => boundingBox dec1::boundingBoxes (dec2::rest)

  (* Expand bounding boxes to contain trailing whitespace *)
  fun expandRight start = let
    fun loop i = if isWhitespace $ sub i then loop (i + 1) else i
    in loop start end

  fun expandLeft start = let
    fun loop i = if isWhitespace $ sub (i - 1)then loop (i - 1) else i
    in loop start end

  fun expandBox (start, stop) = (expandLeft start, expandRight stop)

  (* After expandBox we want to find comments that are immediately
   * before start *)
  fun checkCommentLeft start = let
    fun loop i =
      if substring (i - 2) 2 = "*)" then SOME (i - 2)
      else if sub (i - 1) = #"\n" then NONE
      else if isEOF (i - 1) then NONE
      else loop (i - 1)
    in
      if sub (start - 1) = #"\n" then loop (start - 1)
      else if substring (start - 2) 2 = "*)" then SOME (start - 2)
      else NONE end

  fun checkCommentRight start = let
    fun loop i =
      if substring i 2 = "(*" then SOME i
      else if sub i = #"\n" then NONE
      else if isEOF i then NONE
      else loop (i + 1)
    in
      if sub start = #"\n" then loop (start + 1)
      else if substring start 2 = "(*" then SOME start
      else NONE end

  (* offset => (line, col) *)
  (* yoinked from Mario *)
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
    val line = partitionPoint (Vector.length lines)
      (fn i => Vector.sub (lines, i) <= index)
    in
      (line, index - (if line = 0 then 0 else Vector.sub (lines, line - 1)))
    end

  val lines = mkLineCounter body


  (*** "main" body ****************************************************)

  (** Location of new header ******************************************)
  val (_, top) = parseComment 0
  val top =
    if sub top = #"\n" then top + 1 else fail "Expected newline after comment"

  (** Figure out theory name ******************************************)
  val newTheoryCall = filterDecs (isCallTo "new_theory") decs
  val theoryName =
    newTheoryCall
    |> List.filter (not o isSemi)
    |> sing |> destCall |> Option.valOf |> #2
    |> destStringConstant |> Option.valOf
    |> stripStringQuotes;

  (** Figure out theories and libraries *******************************)
  (* top-level open declarations **************************************)
  val openDecs = filterDecs isOpen decs
  val (openTheories, openLibs) =
    openDecs
    |> List.filter (not o isSemi)
    |> mapOption destOpen |> Option.valOf
    |> List.concat
    |> List.partition (String.isSuffix "Theory")

  (* local open declarations ******************************************)
  val localOpenDecs = filterDecs isLocalOpen decs;
  val (localOpenTheories, localOpenLibs) =
    localOpenDecs
    |> List.filter (not o isSemi)
    |> mapOption destLocal |> Option.valOf
    |> map #1 |> List.concat
    |> mapOption destOpen |> Option.valOf
    |> List.concat
    |> List.partition (String.isSuffix "Theory")

  (* Ignore theories occuring in local opens if we came across it in
     a top-level open *)
  val localOpenTheories =
    List.filter (fn x => not (mem x openTheories)) localOpenTheories

  (* top-level opens don't result in any attributes *)
  val openTheories: (string * attr list) list =
    map (fn x => (stripTheory x, [])) openTheories

  (* theories opened in a local block result in no_bind attribute *)
  val localOpenTheories =
    localOpenTheories |> map (fn x => (stripTheory x, [NoBind]))

  (* Sanity check *)
  val _ = assert (localOpenLibs = []) "localOpenLibs not empty"

  (* Deal with set_grammar_ancestry ***********************************)
  val setGrammarAncestryCall =
    filterDecs (isCallTo "set_grammar_ancestry") decs;   

  (* If a call to set_grammar_ancestry exists, we need to list theories
     in that order and add ignore_grammar to those not listed *)
  fun processSetGrammarAncestry sgac theories = let
    val sgac = List.filter (not o isSemi) sgac
    val count = List.length sgac in
    if count = 0 then theories
    else if 1 < count then
      fail "Multiple calls to set_grammar_ancestry"
    else let
      val grammarAncestry = sgac
        |> sing |> destCall |> Option.valOf |> #2
        |> destList |> Option.valOf
        |> mapOption destStringConstant |> Option.valOf
        |> map stripStringQuotes
      val grammarTheories =
        map (fn n => (n, lookup n theories)) grammarAncestry
      val ignoreGrammarTheories =
        List.filter (fn (x,_) => not (mem x grammarAncestry)) theories
        |> map (fn (x,attrs) => (x,attrs @ [IgnoreGrammar]))
      in grammarTheories @ ignoreGrammarTheories end
    end 

  val theoryList = processSetGrammarAncestry setGrammarAncestryCall
    (openTheories @ localOpenTheories)

  val libList = openLibs @ localOpenLibs
    
  (* export_theory call ***********************************************)
  val exportTheoryCall = filterDecs (isCallTo "export_theory") decs;

  (* Collect warnings *************************************************)
  val trash = List.concat [
    newTheoryCall,
    openDecs, 
    localOpenDecs,
    setGrammarAncestryCall,
    exportTheoryCall
    ]
  
  val trashBoxes = trash |> boundingBoxes |> map expandBox

  val maybeDeletedComment = trashBoxes |> List.filter maybeContainsComment

  (* Reports comments immediately before and after deleted elements *)
  val maybeStrayComments =
    trashBoxes
    |> map (fn (l,r) => [checkCommentLeft l, checkCommentRight r])
    |> List.concat |> List.filter isSome |> List.map valOf

  (* Delete declarations **********************************************)

  (* Write new syntax *************************************************)

  (* in () end   *)