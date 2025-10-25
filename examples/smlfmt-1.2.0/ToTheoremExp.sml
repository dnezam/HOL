open Parser

val file = "/home/daniel/code/HOL-to-theory/examples/smlfmt-1.2.0/test.txt";

fun fileToString file = let
  val s = TextIO.openIn file
  fun readFile acc = case TextIO.inputLine s of
    SOME line => readFile (line :: acc)
  | NONE => (TextIO.closeIn s; concat (rev acc))
in readFile [] end

val body = fileToString file

(** offset => (line, col) *******************************************)
fun mkLineCounter str = let  (* yoinked from Mario *)
  fun loop i ls =
    if i >= String.size str then Vector.fromList (List.rev ls)
    else
      let val c = String.sub (str, i)
      in loop (i+1) (if c = #"\n" then i+1::ls else ls) end
in loop 0 [] end

fun partitionPoint len pred = let  (* yoinked from Mario *)
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

fun parse file body = let
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
in pull [] end

fun localInDecs (DecLocal {dec1, dec2, ...}) = dec2
  | localInDecs dec = [dec]

fun computeUpdates file body = let
  val decs = List.concat $ map localInDecs $ parse file body
  fun isOOF i = i < 0 orelse String.size body <= i
  fun isWhitespace c = (c = #" " orelse c =  #"\t")
  fun isAnyWhitespace c = (c = #" " orelse c =  #"\t" orelse c = #"\n")
  fun sub i = String.sub (body, i) handle Subscript => #"\000"
  fun expandLeft start = let
    fun loop i = if isWhitespace $ sub (i - 1) then loop (i - 1) else i
  in loop start end
  fun expandBoxLeft (start, stop) = (expandLeft start, stop)
  fun expandRight start = let
    fun loop i = if isWhitespace $ sub i then loop (i + 1) else i
  in loop start end
  fun expandBox (start, stop) = (expandLeft start, expandRight stop)
  fun expandLeftHard start = let
    fun loop i = if isAnyWhitespace $ sub (i - 1) then loop (i - 1) else i
  in loop start end
  fun expandRightHard start = let
    fun loop i = if isAnyWhitespace $ sub i then loop (i + 1) else i
  in loop start end
  val lines = mkLineCounter body
  fun getLineCol index = let  (* yoinked from Mario *)
    val line = partitionPoint (Vector.length lines)
      (fn i => Vector.sub (lines, i) <= index)
    in
      (line, index - (if line = 0 then 0 else Vector.sub (lines, line - 1)))
  end
  fun getColBox (start, _) = #2 (getLineCol start)
  fun getLineBox (start, _) = #1 (getLineCol start)
  fun getLine start = #1 (getLineCol start)
  fun identBox (id: ident) = (#1 id, (#1 id) + String.size (#2 id))
  fun boxLength (start, stop) = stop - start
  fun spaceString len = String.implode (List.tabulate (len, fn _ => #" "))
  fun removeBox box = (box, "")
  (* Sometimes, there is code that looks like:
     * val foo =
     *  Define
     *    ‘...’
     * In which case, we want to remove the Define line *)
  fun removeBoxSandwich bu bm bd =
    if getLineBox bu <> getLineBox bm
       andalso getLineBox bm <> getLineBox bd
    then let
      val (start, stop) = bm
      val start = expandLeft start
      val start = if sub (start - 1) = #"\n" then start - 1 else start
    in removeBox (start, stop) end
    else removeBox bm
  fun stripParens (Parens {exp, ...}) = stripParens exp
    | stripParens exp = exp
  (* val vname = fname arg *)
  fun destCall dec = let
    val DecVal {val_, elems, ...} = dec
    val {args = [vb], ...} = elems
    val {pat, eq = SOME ({eq, exp}), ...} = vb
    val Ident {id = vname , ...} = pat
    val App (Ident {id = fname, ...}, arg) = exp
  in (val_, vname, eq, fname, stripParens arg) end;
  fun destTuple t = let
    val Tuple {left, elems = {args, delims,...}, right = SOME right, ...} = t
    val [name, quote, proof] = args
    val [SOME comma0, SOME comma1] = delims
  in (left, stripParens name, comma0, stripParens quote, comma1, stripParens proof, right) end;
  fun destQuote q =
      case q of
          HOLQuote {head, end_tok = SOME end_tok, ...} => (head, end_tok)
        | HOLFullQuote {head, end_tok = SOME end_tok, ...} => (head, end_tok)
        | _ => raise Bind
  fun destString (StringConstant id) = id
  fun stringQuotes (i, s) = (i, i + String.size s - 1)
  fun updToCol0 box s =
      if getColBox box = 0 then (box, s) else (box, "\n" ^ s)
  fun computeUpdatesDec dec = let
    (* Destruct: val vname = fname arg *)
    val (val_, vname, eq, fname, arg) = destCall dec
    (* Only update calls to store_thm *)
    val _ = if not $ (#2 fname) = "store_thm" then raise Bind else ()
    val (left, name, comma0, exp, comma1, proof, right) = destTuple arg
    val (strQL, strQR) = stringQuotes $ destString name
    (* val ... = store_thm ("
       ==>
       Theorem  *)
    val thm_box = expandBoxLeft (val_, strQL + 1)
    val thm_upd = updToCol0 thm_box "Theorem "
    (* ..." ==> : *)
    val colon_box = expandBoxLeft (strQR, comma0)
    val colon_upd = (colon_box, ":")
    (* .., ==> Proof *)
    (* val proof_box = expandBoxLeft (comma1, comma1 + 1) *)
    (* val proof_upd = updToCol0 proof_box "Proof" *)
    (* ) ==> QED *)
    val qed_box = expandBoxLeft (right, right + 1)
    val qed_upd = updToCol0 qed_box "QED"
    (* *)
    val exp_left = expandRightHard (comma0+1)
    val exp_left_str = if getLine exp_left <> getLine comma0 then "\n^(" else " ^("
    val exp_left_upd = ((comma0, exp_left+1), exp_left_str ^ (str $ String.sub (body, exp_left)))
    val exp_right = expandLeftHard comma1
    val exp_right_upd = ((exp_right, comma1+1), ")\nProof")


  in [thm_upd, colon_upd, exp_left_upd, exp_right_upd, qed_upd] end handle Bind => []
in List.concat $ map computeUpdatesDec $ decs end

(* By doing the last update first, an update cannot mess with
 * the indices of other updates *)
fun sortUpdates upds =
  Listsort.sort (fn (((s1,_),_),((s2,_),_)) => Int.compare (s2,s1)) upds

fun applyUpdate (((start, stop), replacement), str) =
  String.substring (str, 0, start) ^
  replacement ^
  String.extract (str, stop, NONE)

fun applyUpdates (str, updates) = foldl applyUpdate str updates

fun updatedString file = let
  val body = fileToString file
  val upds = sortUpdates $ computeUpdates file body
in applyUpdates (body, upds) end

fun writeStringToFile file content = let
  val outstream = TextIO.openOut file
in TextIO.output(outstream, content); TextIO.closeOut outstream end

fun runCommand cmd = let
  val proc = Unix.execute ("/bin/sh", ["-c", cmd])
in ignore (Unix.reap proc) end

fun removeTrailingWhitespace file =
  runCommand $ "sed -i 's/[[:space:]]\\+$//' " ^ file

fun removeSemicolonAfterEnd file =
  runCommand $ "sed -i 's/^QED[[:space:];]*/QED/' " ^ file

fun applyToFile file = let
  val _ = print (file ^ ": ")
  val new = updatedString file
  val _ = writeStringToFile file new
  val _ = removeSemicolonAfterEnd file
  val _ = removeTrailingWhitespace file
  val _ = print "Done.\n"
in () end handle Bind => print "FAIL\n"

(*** scratchpad *******************************************************)


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
