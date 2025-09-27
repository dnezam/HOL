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
  fun expandBoxLeft (start, stop) = (expandLeft start, stop)
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
  (* val vname = fname arg *)
  fun destCall dec = let
    val DecVal {val_, elems, ...} = dec
    val {args = [vb], ...} = elems
    val {pat, eq = SOME ({eq, exp}), ...} = vb
    val Ident {id = vname , ...} = pat
    val App (Ident {id = fname, ...}, arg) = exp
  in (val_, vname, eq, fname, arg) end;
  fun destQuote q = let
    val HOLQuote {head, end_tok = SOME end_tok, ...} = q
  in (head, end_tok) end
  fun computeUpdatesDec dec = let
    (* Destruct: val vname = fname ‘...’ *)
    val (val_, vname, eq, fname, arg) = destCall dec
    (* Give up for now if the SML name is _ *)
    val _ = if #2 vname = "_" then raise Bind else ()
    (* Only update calls to Define *)
    val _ = if not $ (#2 fname) = "Define" then raise Bind else ()
    val (openq, closeq) = destQuote arg
    (* Convert to boxes [start, stop) *)
    val val_box = expandBoxLeft (val_, val_ + 3)
    val vname_box = identBox vname
    val eq_box = (eq, eq + 1)
    val fname_box = identBox fname
    val openq_box = identBox openq
    (* I don't think putting space before the closing quote is meaningful;
     * could be wrong though! *)
    val closeq_box = expandBoxLeft $ identBox closeq
    (** Compute the updates *)
    (* val *)
    val defkw_str = if getColBox val_box = 0 then "Definition" else "\nDefinition"
    val val_upd = (val_box, defkw_str)
    (* vname *)
    val defn_str = #2 vname ^ ":"
    val vname_upd = (vname_box, defn_str)
    (* =, function name, opening quote*)
    val eq_upd = removeBox eq_box
    val fname_upd = removeBoxSandwich eq_box fname_box openq_box
    (* If Define and ‘ are on different lines, then we probably want to
     * replace the quote with a space instead of deleting it to preserve
     * alignment. *)
    val openq_upd = if getLineBox fname_box <> getLineBox openq_box
                    then (openq_box, " ") else removeBox openq_box
    (* Closing quote *)
    val endkw_str = if getColBox closeq_box = 0 then "End" else "\nEnd"
    val closeq_upd = (closeq_box, endkw_str)
  in [val_upd, vname_upd, eq_upd, fname_upd, openq_upd, closeq_upd] end handle Bind => []
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
