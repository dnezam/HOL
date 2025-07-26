open Parser

(** Return shenanigans **********************************************)
exception AlreadyTheory
exception NoSgac
exception Ready of (string * (((int * int) * (int * int)) list) * ((int * int) list))

fun apply file = let
  (** SML/HOL parsing *************************************************)
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

  (** General helpers *************************************************)
  fun fail msg = raise Fail msg

  fun assert b msg = if not b then fail msg else ()

  fun sing xs = (case xs of [x] => x | _ => fail "sing: Not a singleton")

  fun mem y xs = List.exists (fn x => x = y) xs

  fun isNotIn xs y = not (List.exists (fn x => x = y) xs)

  fun mapOption _ [] = SOME []
    | mapOption f (x::xs) =
      case f x of
          NONE => NONE
        | SOME y =>
          case mapOption f xs of
              NONE => NONE
            | SOME ys => SOME (y::ys)

  (** Parsing *********************************************************)
  fun isOOF i = i < 0 orelse String.size body <= i
  fun isWhitespace c = (c = #" " orelse c =  #"\t")

  fun sub i = String.sub (body, i) handle Subscript => #"\000"

  fun substring i j =
    String.substring (body, i, j) handle Subscript => "\000"

  fun skipSpace i =
    if Char.isSpace (sub i) then skipSpace (i + 1) else i

  fun parseComment start = let
    fun loop i depth =
      if substring i 2 = "(*" then
        loop (i + 2) (depth + 1)
      else if substring i 2 = "*)" then
        if depth <= 0 then (start, i + 2) else loop (i + 2) (depth - 1)
      else if isOOF i then raise Fail "Unterminated comment"
      else loop (i + 1) depth
    in
      if substring start 2 = "(*"
      then loop (start + 2) 0
      else fail "Expected comment" end

  fun findTop () = let
    (* Loop to consume all comments *)
    fun loop (start, end_) =
      let val afterSpace = skipSpace end_ in
        if substring afterSpace 2 = "(*" then
          let val (_, end_) = loop (parseComment afterSpace) in (start, end_) end
        else (start, end_) end
    val afterSpace = skipSpace 0
  in
      if (not $ substring afterSpace 2 = "(*") then (0,0)
      else loop (parseComment afterSpace) end

  fun stripStringQuotes s = String.substring (s, 1, String.size s - 2)
  fun stripTheory s = String.substring (s, 0, String.size s - 6)

  (* Potential false positives if we have the opening or closing
   * comment within a string literal *)
  fun maybeContainsComment (start, stop) = let
    val s = String.substring (body, start, stop - start)
    in String.isSubstring "(*" s orelse String.isSubstring "*)" s end

  (** HOL/SML AST *****************************************************)
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

  fun isTheoryDec (HOLTheory {...}) = true
    | isTheoryDec _ = false

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

  (** Attributes ******************************************************)
  datatype attr = IgnoreGrammar | Qualified

  (** Bounding boxes **************************************************)
  (* (start [inclusive], stop [exclusive]) *)

  (* Find bounding boxes *)
  fun identStop (start, content) = start + String.size content

  fun expStop exp =
    case exp of
      Unit {right, ...} => right + 1
    | StringConstant (start, content) => start + String.size content
    | Ident {id, ...} => identStop id
    | App (_, e2) => expStop e2
    | List {right = SOME right, ...} => right + 1
    | _ => raise Fail "unsupported for now"

  fun boundingBox dec =
    case dec of
      DecSemi s => (s, s+1)
    | DecVal {val_, elems, ...} => let
      val {args = [vb], ...} = elems
      val {eq = SOME ({exp, ...}), ...} = vb
      in (val_, expStop exp) end
    | DecOpen {open_, elems} => (case elems of
        [] => (open_, open_ + 4)
      | _ => (open_, identStop (List.last elems)))
    | DecLocal {local_, end_ = SOME end_pos, ...} => (local_, end_pos + 3)
    | _ => fail "unsupported for now"

  (* Merge boxes of declaration and semicolon that follow immediately -
   * we are mainly worried about things like
   * open foo                                          ;
   * here - we want to consider that whitespace as part of the
   * declaration. No guarantees this is not necessary though, or does
   * not already happen.*)
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
  fun expandBox (start, stop) = let
    fun expandRight start = let
        fun loop i = if isWhitespace $ sub i then loop (i + 1) else i
        in loop start end
    fun expandLeft start = let
      fun loop i = if isWhitespace $ sub (i - 1) then loop (i - 1) else i
      in loop start end
    in (expandLeft start, expandRight stop) end

  (* We want to also deleted trailing newlines on the right side.
   * If we do this in expandRight already, checkCommentRight might start
   * to report comments that are on the left of something else. *)
  fun consumeSpace (start, stop) = let
    fun consumeSpaceRight start = let
      fun loop i = if Char.isSpace $ sub i then loop (i + 1) else i
      in loop start end
    in (start, consumeSpaceRight stop) end

  (* After expandBox we want to find comments that are immediately
   * before start *)
  fun checkCommentLeft start = let
    fun loop i =
      if substring (i - 2) 2 = "*)" then SOME (i - 2)
      else if sub (i - 1) = #"\n" then NONE
      else if isOOF (i - 1) then NONE
      else loop (i - 1)
    in
      if sub (start - 1) = #"\n" then loop (start - 1)
      else if substring (start - 2) 2 = "*)" then SOME (start - 2)
      else NONE end

  fun checkCommentRight start = let
    fun loop i =
      if substring i 2 = "(*" then SOME i
      else if sub i = #"\n" then NONE
      else if isOOF i then NONE
      else loop (i + 1)
    in
      if sub start = #"\n" then loop (start + 1)
      else if substring start 2 = "(*" then SOME start
      else NONE end

  (** Deleting slices *************************************************)
  (* Merges slices and returns them in increasing start order *)
  fun mergeSlices (slices: (int * int) list) : (int * int) list = let
    fun merge [] = []
      | merge [x] = [x]
      | merge ((s1, e1) :: (s2, e2) :: rest) =
          if s2 <= e1 then  (* Overlapping or adjacent *)
            merge ((s1, Int.max (e1, e2)) :: rest)
          else
            (s1, e1) :: merge ((s2, e2) :: rest)
    val sortedSlices =
      Listsort.sort (fn ((s1,_),(s2,_)) => Int.compare (s1,s2)) slices
    in merge sortedSlices end

  (* Assumes that slices are not overlapping and sorted in increasing
   * order (and maybe that there is some relation between start and stop
   * - who knows :D) *)
  (* Basic idea from Mario, mistakes from me *)
  fun deleteSlices s slices = let
    fun aux _ stop [] acc =
        Substring.concat (rev acc) ^
        String.extract (s, stop, NONE)
    | aux s p ((start, stop) :: rest) acc =
    aux s stop rest (Substring.substring (s, p, start - p) :: acc)
    in aux s 0 slices [] end

  (** ToString ********************************************************)
  fun attrToString attr =
      case attr of Qualified => "qualified" | IgnoreGrammar => "ignore_grammar"

  fun attrsToString attrs =
      case attrs of
          [] => ""
        | _ => "[" ^ String.concatWith ", " (map attrToString attrs) ^ "]"

  fun theoryWithAttrToString (name, attrs) = name ^ attrsToString attrs

  (* Returns a list of strings that start with two spaces as indent
   * and have their total length mostly restricted to max. *)
  fun fillRegion max ss =
    case ss of
      [] => []
    | (s::rest) => let
      fun aux cur [] acc = List.rev (cur::acc)
        | aux cur (s::rest) acc =
          if String.size cur + String.size s + 1 <= max then
            aux (cur ^ " " ^ s) rest acc
          else aux ("  " ^ s) rest (cur::acc)
      in aux ("  " ^ s) rest [] end

  (** offset => (line, col) *******************************************)
  (* yoinked from Mario *)
  fun mkLineCounter str = let
    fun loop i ls =
      if i >= String.size str then Vector.fromList (List.rev ls)
      else
        let val c = String.sub (str, i)
        in loop (i+1) (if c = #"\n" then i+1::ls else ls) end
    in loop 0 [] end

  val lines = mkLineCounter body

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

  fun getLineCol index = let
    val line = partitionPoint (Vector.length lines)
      (fn i => Vector.sub (lines, i) <= index)
    in
      (line, index - (if line = 0 then 0 else Vector.sub (lines, line - 1)))
    end

  fun getLineColBox (start, stop) = (getLineCol start, getLineCol stop)

  (*** "main" body ****************************************************)

  val _ = if List.exists isTheoryDec decs
          then raise AlreadyTheory else ()

  (** Location of new header ******************************************)
  val (_, top) = findTop ()
  val top = if sub top = #"\n" then top + 1 else top

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
    localOpenTheories |> map (fn x => (stripTheory x, [Qualified]))

  (* Deal with set_grammar_ancestry ***********************************)
  val setGrammarAncestryCall =
    filterDecs (isCallTo "set_grammar_ancestry") decs;

  (* If a call to set_grammar_ancestry exists, we need to list theories
     in that order and add ignore_grammar to those not listed *)
  fun processSetGrammarAncestry sgac theories = let
    (* This case occurs if something is mentioned in set_grammar_ancestry,
     * but has not been explicitly opened. *)
    fun lookup _ [] = [Qualified]
      | lookup y ((x,v)::xs) = if x = y then v else lookup y xs
    val sgac = List.filter (not o isSemi) sgac
    val count = List.length sgac in
    if count = 0 then (theories, []) (* raise NoSgac *)
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
      val _ = if List.null ignoreGrammarTheories then ()
              else print "[IGNORE_GRAMMAR OMITTED] "
      (* ignore_grammar does not actually ignore grammars that ancestors
         that are already part of the grammar depend on. Probably (?) better
         to use temp_set_grammar_ancestry or something. *)
          (* |> map (fn (x,attrs) => (x,attrs @ [IgnoreGrammar])) *)
      in (grammarTheories @ ignoreGrammarTheories, []) end
    end

  val (grammarTheories, ignoreGrammarTheories) =
      processSetGrammarAncestry setGrammarAncestryCall
                                (openTheories @ localOpenTheories)

  fun factorAttrs (xs : (string * attr list) list) : attr list * (string * attr list) list =
    let
      fun intersect (xs, ys) = List.filter (fn x => List.exists (fn y => x = y) ys) xs
      fun commonAttrs [] = []
        | commonAttrs ((_, attrs)::rest) =
          List.foldl (fn ((_, attrs2), acc) => intersect (acc, attrs2)) attrs rest
      fun removeAttrs attrs commons =
          List.filter (fn a => not (List.exists (fn c => a = c) commons)) attrs
      val commons = commonAttrs xs
      val stripped = List.map (fn (s, attrs) => (s, removeAttrs attrs commons)) xs
    in (commons, stripped) end

  val (commonGrammarAttrs, grammarThyStrings) = factorAttrs grammarTheories
  val grammarThyStrings = grammarThyStrings |> map theoryWithAttrToString |> fillRegion 65
  val ancestorString =
      if List.null grammarThyStrings then ""
      else "\nAncestors" ^ attrsToString commonGrammarAttrs ^ "\n" ^
           String.concatWith "\n" grammarThyStrings

  val (commonIgnoreGrammarAttrs, ignoreGrammarThyStrings) = factorAttrs ignoreGrammarTheories
  val ignoreGrammarThyStrings = ignoreGrammarThyStrings |> map theoryWithAttrToString |> fillRegion 65
  val ancestorIgnoreGrammarString =
      if List.null ignoreGrammarThyStrings then ""
      else "\nAncestors" ^ attrsToString commonIgnoreGrammarAttrs ^ "\n" ^
           String.concatWith "\n" ignoreGrammarThyStrings


  val openLibs = openLibs |> map (fn x => (x, []))
  val localOpenLibs = localOpenLibs |> map (fn x => (x, [Qualified]))

  val libList =
    openLibs @ localOpenLibs
    (* Since we do not use bare, we don't need to mention these *)
    |> List.filter (fn (x, _) => isNotIn ["HolKernel", "Parse", "boolLib", "bossLib"] x)
  val libStrings = libList |> map theoryWithAttrToString |> fillRegion 65

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

  val trashBoxes =
    trash |> boundingBoxes |> map expandBox |> mergeSlices

  val maybeDeletedComment =
    trashBoxes |> List.filter maybeContainsComment |> map getLineColBox

  (* Reports comments immediately before and after deleted elements *)
  val maybeStrayComments =
    trashBoxes
    |> map (fn (l,r) => [checkCommentLeft l, checkCommentRight r])
    |> List.concat |> List.filter isSome |> List.map valOf
    (* Hack to avoid initial comment to be recognized as stray *)
    |> List.filter (fn x => x <> (top - 3))
    |> map getLineCol

  (* We have collected the warnings, so now we can consume trailing
   * whitespace more aggressively. *)
   val trashBoxes = trashBoxes |> map consumeSpace

  (* Delete declarations **********************************************)
  val cleanBody = deleteSlices body trashBoxes

  (* Write new syntax *************************************************)

  (* Sanity check: Make sure top position has not been invalidated by
   * deleting things around there *)
  val _ = assert (List.null trashBoxes orelse top < #2 (List.hd trashBoxes))
    "Position where we wanted to insert the new header was invalidated"

  val newHeader =
      "Theory " ^ theoryName ^ (* "[bare]" ^ *)
      ancestorString ^
      ancestorIgnoreGrammarString ^
      (if List.null libStrings then ""
       else "\nLibs\n" ^
            String.concatWith "\n" libStrings)

  val newBody = String.concat [
    String.substring (cleanBody, 0, top),
    newHeader, "\n\n",
    String.extract (cleanBody, top, NONE)
    ]
in
  raise Ready (
      newBody,
      maybeDeletedComment,
      maybeStrayComments)
end



(*** scratchpad *******************************************************)

fun writeStringToFile file content = let
  val outstream = TextIO.openOut file
in TextIO.output(outstream, content); TextIO.closeOut outstream end

fun applyToFile file = let
  val _ = print (file ^ ": ")
  val _ = apply file handle
            AlreadyTheory => print "Nothing to do\n"
          | NoSgac => print "Missing set_grammar_ancestry\n"
          | Ready (newBody, maybeDeletedComment, maybeStrayComments) =>
            if maybeDeletedComment = [] andalso maybeStrayComments = [] then
                (writeStringToFile file newBody; print "OK\n")
            else (writeStringToFile file newBody; print "MANUALLY CHECK\n";
                  print "0-indexed (line, col):\n"; PolyML.print maybeDeletedComment; PolyML.print maybeStrayComments;
                 print "\n")
          | e  => (PolyML.print e; print "Unhandled exception\n")
in () end

fun applyToScriptsInDir dir =
    let
        val d = OS.FileSys.openDir dir
        fun loop () =
            case OS.FileSys.readDir d of
                NONE => ()
              | SOME f =>
                    (if String.isSuffix "Script.sml" f then
                         applyToFile (OS.Path.concat (dir, f))
                     else ();
                     loop ())
    in
        loop () before OS.FileSys.closeDir d
    end

fun applyToScriptsInDirRec (rootDir : string) =
  let
    val targetSuffix = "Script.sml"
    fun traverse (currentPath : string) =
      if OS.FileSys.isDir currentPath then
        let
          val dirStream = OS.FileSys.openDir currentPath
                          handle OS.SysErr (msg, _) =>
                                 (print ("Error opening " ^ currentPath ^ ": " ^ msg ^ "\n"); raise OS.SysErr (msg, NONE))
          fun loop () =
            case OS.FileSys.readDir dirStream of
              NONE => ()
            | SOME entry =>
                if entry <> "." andalso entry <> ".." then
                  let
                    val fullPath = OS.Path.joinDirFile {dir = currentPath, file = entry}
                  in
                    if OS.FileSys.isDir fullPath handle _ => false then
                      traverse fullPath
                    else if String.isSuffix targetSuffix fullPath then
                      applyToFile fullPath
                    else
                      ();

                    loop ()
                  end
                else
                  loop ()
        in
          loop ();
          OS.FileSys.closeDir dirStream
        end
      else ()
  in traverse rootDir end
