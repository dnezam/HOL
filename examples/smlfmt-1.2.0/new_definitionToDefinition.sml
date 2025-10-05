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

fun computeUpdates file body = let
  val decs = parse file body
  fun isOOF i = i < 0 orelse String.size body <= i
  fun isWhitespace c = (c = #" " orelse c =  #"\t")
  fun sub i = String.sub (body, i) handle Subscript => #"\000"
  fun expandLeft start = let
    fun loop i = if isWhitespace $ sub (i - 1) then loop (i - 1) else i
  in loop start end
  fun expandRight start = let
    fun loop i = if isWhitespace $ sub i then loop (i + 1) else i
  in loop start end
  fun expandBoxLeft (start, stop) = (expandLeft start, stop)
  fun expandBox (start, stop) = (expandLeft start, expandRight stop)
  val lines = mkLineCounter body
  fun getLineCol index = let  (* yoinked from Mario *)
    val line = partitionPoint (Vector.length lines)
      (fn i => Vector.sub (lines, i) <= index)
    in
      (line, index - (if line = 0 then 0 else Vector.sub (lines, line - 1)))
  end
  fun getColBox (start, _) = #2 (getLineCol start)
  fun getLineBox (start, _) = #1 (getLineCol start)
  fun identBox id = (#1 id, (#1 id) + String.size (#2 id))
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
  (* val pat = fname arg *)
  fun destCall dec = let
    val DecVal {val_, elems, ...} = dec
    val {args = [vb], ...} = elems
    val {pat, eq = SOME ({eq, exp}), ...} = vb
    val App (Ident {id = fname, ...}, arg) = exp
  in (val_, eq, fname, arg) end;
  fun destTuple t = let
    val Tuple {left, elems = {args, delims}, right = SOME right, ...} = t
    val [name, exp] = args
    val [SOME comma0] = delims
  in (left, name, comma0, exp, right) end;
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
    val (val_, eq, fname, arg) = destCall dec
    (* Only update calls to ... *)
    val _ = if not $ (#2 fname) = "new_definition" then raise Bind else ()
    val (left, name, comma0, exp, right) = destTuple arg
    val (strQL, strQR) = stringQuotes $ destString name
    val (openq, closeq) = destQuote exp
    (* val ... = ... ("
       ==>
       Theorem  *)
    val thm_box = expandBoxLeft (val_, strQL + 1)
    val thm_upd = updToCol0 thm_box "Definition "
    (* ...", ==> : *)
    val eq_box = expandBoxLeft (strQR, comma0 + 1)
    (* Potential position of a ] closing existing tags *)
    val myb_sqc = (expandLeft (strQR-1))
    val eq_upd = if sub myb_sqc  = #"]"
                 then ((myb_sqc, #2 eq_box), ",nocompute]:")
                 else (eq_box, "[nocompute]:")
    (* `` ==>    *)
    (* Remove opening quote of HOL term *)
    val openq_box = identBox openq
    (* some code looks something like this:
     val ASSOC_DEF = new_definition("ASSOC_DEF",
         ``
         ...
     *)
    val openq_upd = removeBoxSandwich eq_box openq_box (#2 openq_box+1, (#2 openq_box+2))
    (* val openq_len = #2 openq_box - #1 openq_box *)
    (* val openq_upd = if openq_len = 3 *)
    (*                 then (openq_box, spaceString 1) (* It's a unicode quote *) *)
    (*                 else (openq_box, spaceString openq_len) *)
    (* ``) ==> End*)
    val rpar_box = expandBoxLeft (#1 closeq, right + 1)
    val rpar_upd = updToCol0 rpar_box "End"
  in [thm_upd, eq_upd, openq_upd, rpar_upd] end handle Bind => []
                                                    |  Match => []
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
  runCommand $ "sed -i 's/^End[[:space:];]*/End/' " ^ file

fun applyToFile file = let
  val _ = print (file ^ ": ")
  val new = updatedString file
  val _ = writeStringToFile file new
  val _ = removeSemicolonAfterEnd file
  val _ = removeTrailingWhitespace file
  val _ = print "Done.\n"
in () end handle _ => print "FAIL\n"

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

fun deletedComments dir =
  "git diff -G'\\(\\*' -- " ^ dir ^ " | awk '/^--- a\\// {file=$2; gsub(/^a\\//,\"\",file)} /^-.*\\(\\*/ && !/^---/ {print file \": \" $0}'"

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
  in traverse rootDir;
     print "\nUse this command to check for deleted comments:\n";
     print $ deletedComments rootDir;
     print"\n" end
