module

public import LeanQbe.T.BinaryLayout
public meta import Lean
public meta import LeanQbe.T.BinaryLayout

set_option autoImplicit false

public section

namespace LeanQbe.T.BinaryLayoutElab

syntax binaryLayoutOpt := "(" ident ":=" term ")"

syntax (name := binaryLayoutX64Cmd)
  "binary_layout_x64!" ident str (binaryLayoutOpt)* ("for" term)? (binaryLayoutOpt)* : command

syntax (name := binaryLayoutArm64Cmd)
  "binary_layout_arm64!" ident str (binaryLayoutOpt)* ("for" term)? (binaryLayoutOpt)* : command

end LeanQbe.T.BinaryLayoutElab

meta section

namespace LeanQbe.T.BinaryLayoutElab

open Lean Elab Command Meta

private inductive TargetArch where
  | x64
  | arm64
  deriving Repr, DecidableEq, Inhabited

private structure BinaryLayoutOpts where
  sectionName : String := ".text"
  symbols : Option (List String) := none
  allowPadding : Bool := true
  absorbPadding : Bool := false
  deriving Inhabited

private structure ObjSymbol where
  name : String
  addr : Nat
  deriving Repr, Inhabited

private structure ObjInsn where
  addr : Nat
  byteLen : Nat
  bytesHex : String
  mnemonic : String
  deriving Repr, Inhabited

private def isWsChar (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\r' || c == '\n'

private def trimRightStr (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile isWsChar).reverse)

private def trimStr (s : String) : String :=
  String.ofList ((trimRightStr s).toList.dropWhile isWsChar)

private def dropRightStr (s : String) (n : Nat) : String :=
  let cs := s.toList
  String.ofList (cs.take (cs.length - n))

private def toLowerStr (s : String) : String :=
  String.ofList (s.toList.map Char.toLower)

private def isHexChar (c : Char) : Bool :=
  ('0' <= c && c <= '9') || ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F')

private def hexVal (c : Char) : Nat :=
  if '0' <= c && c <= '9' then c.toNat - '0'.toNat
  else if 'a' <= c && c <= 'f' then 10 + (c.toNat - 'a'.toNat)
  else 10 + (c.toNat - 'A'.toNat)

private def parseHexNat? (s : String) : Option Nat := do
  let s := trimStr s
  guard (!s.isEmpty)
  guard (s.all isHexChar)
  let mut acc : Nat := 0
  for c in s.toList do
    acc := acc * 16 + hexVal c
  return acc

private def isHexByteGroup (tok : String) : Bool :=
  !tok.isEmpty && tok.length % 2 == 0 && tok.all isHexChar

private def parseSymbolHeader? (line : String) : Option ObjSymbol := do
  let trimmed := trimRightStr line
  guard (trimmed.endsWith ">:")
  let parts := trimmed.splitOn " <"
  guard (parts.length == 2)
  let addr ← parseHexNat? parts[0]!
  let rest := parts[1]!
  let sym := dropRightStr rest 2
  guard (!sym.isEmpty)
  return { name := sym, addr }

private def parseObjInsnLine? (line : String) : Option ObjInsn := do
  let trimmed := trimStr line
  guard (!trimmed.isEmpty)
  guard (!trimmed.endsWith ">:")
  let colonParts := trimmed.splitOn ":"
  guard (colonParts.length >= 2)
  let addr ← parseHexNat? colonParts[0]!
  let afterColon := ":".intercalate colonParts.tail!
  let tabParts := afterColon.splitOn "\t"
  if tabParts.length >= 2 then
    let hexCol := trimStr tabParts[0]!
    let tokens := (hexCol.splitOn " ").filter (!·.isEmpty)
    guard (!tokens.isEmpty)
    guard (tokens.all isHexByteGroup)
    let joined := String.join tokens
    let byteLen := joined.length / 2
    guard (byteLen > 0)
    let mnemonic := trimStr ("\t".intercalate tabParts.tail!)
    return { addr, byteLen, bytesHex := toLowerStr joined, mnemonic }
  else
    let tokens := ((trimStr afterColon).splitOn " ").filter (!·.isEmpty)
    let hexTokens := tokens.takeWhile isHexByteGroup
    guard (!hexTokens.isEmpty)
    let joined := String.join hexTokens
    let byteLen := joined.length / 2
    guard (byteLen > 0)
    let remTokens := tokens.drop hexTokens.length
    let mnemonic := trimStr (" ".intercalate remTokens)
    return { addr, byteLen, bytesHex := toLowerStr joined, mnemonic }

private def runObjdump (binPath sectionName : String) :
    IO (Array ObjSymbol × Array ObjInsn) := do
  let exists? ← System.FilePath.pathExists binPath
  if !exists? then
    throw <| IO.userError s!"binary file not found: {binPath}"
  let out ← IO.Process.output {
    cmd := "llvm-objdump"
    args := #["-d", "--disassemble-zeroes", "--show-all-symbols", "-j", sectionName, binPath]
  }
  if out.exitCode != 0 then
    throw <| IO.userError
      s!"llvm-objdump failed on '{binPath}' (section '{sectionName}'): {out.stderr}"
  let mut syms : Array ObjSymbol := #[]
  let mut insns : Array ObjInsn := #[]
  let mut seenSection := false
  for line in out.stdout.splitOn "\n" do
    let t := trimStr line
    if t.startsWith "Disassembly of section " then
      seenSection := true
    else if t == "..." then
      throw <| IO.userError
        s!"unexpected '...' ellipsis in objdump for '{binPath}' section '{sectionName}'"
    else if let some sym := parseSymbolHeader? line then
      seenSection := true
      if !sym.name.startsWith "$" then
        syms := syms.push sym
    else if seenSection then
      if let some insn := parseObjInsnLine? line then
        insns := insns.push insn
  return (syms, insns)

private def isPaddingInsn (arch : TargetArch) (insn : ObjInsn) : Bool :=
  let m := toLowerStr (trimStr insn.mnemonic)
  let h := insn.bytesHex
  match arch with
  | .x64 =>
    m == "nop" || m.startsWith "nop " || m.startsWith "nop\t" ||
    m.startsWith "nopw" || m.startsWith "nopl" || m.startsWith "nopq" ||
    m == "int3" || m.startsWith "int3 " || m.startsWith "int3\t" ||
    h == "90" || h == "cc" || h == "6690" ||
    h.startsWith "0f1f" || h.startsWith "660f1f" || h.startsWith "6666"
  | .arm64 =>
    m == "nop" || m.startsWith "nop " || m.startsWith "nop\t" ||
    h == "1f2003d5"

private partial def extractTagsFromWhnf (e : Expr) : MetaM (Option (List DirTag)) := do
  let e' ← withTransparency .all (whnf e)
  match e'.getAppFn.constName? with
  | some ``List.nil => return some []
  | some ``List.cons =>
    let args := e'.getAppArgs
    if args.size < 3 then return none
    let hd ← withTransparency .all (whnf args[1]!)
    let tag? ←
      match hd.getAppFn.constName? with
      | some `Kraken.Directive.instr => pure (some DirTag.instr)
      | some `Kraken.Directive.label =>
        let largs := hd.getAppArgs
        if h : 2 < largs.size then
          let s? ← try pure (some (← unsafe evalExpr String (mkConst ``String) largs[2]))
            catch _ => pure none
          pure (s?.map DirTag.label)
        else pure none
      | some `Kraken.Directive.byteArray =>
        let bargs := hd.getAppArgs
        if h : 2 < bargs.size then
          let sz? ← try
            let arr ← unsafe evalExpr ByteArray (mkConst ``ByteArray) bargs[2]
            pure (some arr.size)
          catch _ => pure none
          pure (sz?.map DirTag.byteArray)
        else pure none
      | some `Kraken.Directive.word =>
        let wargs := hd.getAppArgs
        if h : 2 < wargs.size then
          let n? ← try pure (some (← unsafe evalExpr Nat (mkConst ``Nat) wargs[2]))
            catch _ => pure none
          pure (n?.map DirTag.word)
        else pure none
      | _ => pure none
    match tag? with
    | none => return none
    | some tag =>
      let some tl ← extractTagsFromWhnf args[2]! | return none
      return some (tag :: tl)
  | some ``List.append =>
    let args := e'.getAppArgs
    if args.size < 3 then return none
    let some l1 ← extractTagsFromWhnf args[1]! | return none
    let some l2 ← extractTagsFromWhnf args[2]! | return none
    return some (l1 ++ l2)
  | _ => return none

private def extractProgTags (progE : Expr) : MetaM (List DirTag) := do
  let tagsExpr ← mkAppM ``LeanQbe.T.progTags #[progE]
  try
    return ← unsafe evalExpr (List DirTag)
      (mkApp (mkConst ``List [Level.zero]) (mkConst ``DirTag)) tagsExpr
  catch _ =>
    match ← extractTagsFromWhnf progE with
    | some tags => return tags
    | none =>
      throwError "failed to inspect directive skeleton of program expression:\n{progE}"

private def collectAllLabels (tags : List DirTag) : List String :=
  tags.filterMap fun | .label s => some s | _ => none

private def isTopLevelAnchorLabel (s : String) : Bool :=
  !s.startsWith "." && (s.splitOn ".L").length <= 1

private def hasInstrAfterLabel (target : String) : List DirTag → Bool
  | [] => false
  | .label s :: rest =>
    if s == target then rest.any (fun | .instr => true | _ => false)
    else hasInstrAfterLabel target rest
  | _ :: rest => hasInstrAfterLabel target rest

private def autoEntryAnchors (tags : List DirTag) : List String :=
  let cands := tags.filterMap fun
    | .label s => if isTopLevelAnchorLabel s && hasInstrAfterLabel s tags then some s else none
    | _ => none
  cands.eraseDups

private def splitByAnchors (anchors : List String) (tags : List DirTag) :
    Except String (List (Option String × List DirTag)) := do
  match anchors with
  | [] => return [(none, tags)]
  | a0 :: _ =>
    let allLabels := collectAllLabels tags
    if anchors.length == 1 && !allLabels.contains a0 then
      return [(some a0, tags)]
    let rec go (remAnchors : List String) (curAnchor : Option String)
        (curRev : List DirTag) (accRev : List (Option String × List DirTag))
        (rest : List DirTag) : Except String (List (Option String × List DirTag)) := do
      match rest with
      | [] =>
        if !remAnchors.isEmpty then
          throw s!"symbol anchor(s) not found in program labels: {remAnchors}"
        let finalRev := (curAnchor, curRev.reverse) :: accRev
        return finalRev.reverse
      | tag :: tl =>
        match tag, remAnchors with
        | .label s, a :: arest =>
          if s == a then
            if curAnchor.isNone then
              let hasPreInstr := curRev.any (fun | .instr => true | _ => false)
              if hasPreInstr then
                throw s!"program has instructions before first anchor label '{a}'"
              go arest (some a) (tag :: curRev) accRev tl
            else
              go arest (some a) [tag] ((curAnchor, curRev.reverse) :: accRev) tl
          else
            go (a :: arest) curAnchor (tag :: curRev) accRev tl
        | _, _ =>
          go remAnchors curAnchor (tag :: curRev) accRev tl
    go anchors none [] [] tags

private def lookupObjSymbol (syms : Array ObjSymbol) (name : String) :
    Except String ObjSymbol := do
  let matches_ := syms.filter (·.name == name)
  if h : matches_.size == 1 then
    return matches_[0]'(by have := beq_iff_eq.mp h; omega)
  else if matches_.isEmpty then
    let preview := (syms.toList.take 20).map (·.name)
    throw s!"symbol '{name}' not found in ELF section; sample symbols: {preview}"
  else
    throw s!"symbol '{name}' appears {matches_.size} times in disassembled section"

private def hexAddr (n : Nat) : String :=
  "0x" ++ String.ofList (Nat.toDigits 16 n)

private def alignChunk (arch : TargetArch) (opts : BinaryLayoutOpts)
    (anchorName? : Option String) (chunkTags : List DirTag)
    (sliceInsns : Array ObjInsn) (chunkStartAddr : Nat)
    (isLastChunk : Bool) (nextAnchorAddr? : Option Nat) :
    Except String (Array Nat) := do
  let nInstr := chunkTags.foldl (fun n t => match t with | .instr => n + 1 | _ => n) 0
  let labelDesc := anchorName?.getD "<section>"
  if sliceInsns.size < nInstr then
    throw <| s!"instruction count mismatch for '{labelDesc}': program has {nInstr} " ++
      s!"instructions, binary slice contains only {sliceInsns.size}"
  if nInstr > 0 then
    if sliceInsns[0]!.addr != chunkStartAddr then
      throw <| s!"address mismatch at start of '{labelDesc}': symbol at " ++
        s!"{hexAddr chunkStartAddr}, first instruction at {hexAddr sliceInsns[0]!.addr}"
  for i in [0 : nInstr] do
    if i + 1 < sliceInsns.size then
      let cur := sliceInsns[i]!
      let nxt := sliceInsns[i + 1]!
      if cur.addr + cur.byteLen != nxt.addr then
        throw s!"non-contiguous instruction gap in '{labelDesc}' after {hexAddr cur.addr}"
  let mut instrSizes : Array Nat := (sliceInsns.extract 0 nInstr).map (·.byteLen)
  let extra := sliceInsns.extract nInstr sliceInsns.size
  if !extra.isEmpty then
    if !opts.allowPadding then
      let firstExtra := extra[0]!
      throw <| s!"trailing instructions after '{labelDesc}' (expected {nInstr}, got " ++
        s!"{sliceInsns.size}, next '{firstExtra.mnemonic}'); pass (allowPadding := true)"
    for padInsn in extra do
      if !isPaddingInsn arch padInsn then
        throw <| s!"non-padding trailing instruction after '{labelDesc}' at " ++
          s!"{hexAddr padInsn.addr}: '{padInsn.mnemonic}' (bytes {padInsn.bytesHex}); " ++
          s!"program has {nInstr}, binary has {sliceInsns.size}"
    if !isLastChunk then
      let extraBytes := extra.foldl (fun s i => s + i.byteLen) 0
      if !opts.absorbPadding then
        throw <| s!"inter-function padding of {extraBytes} bytes after '{labelDesc}'; " ++
          s!"pass (absorbPadding := true) or assemble without inter-function .p2align"
      if nInstr == 0 then
        throw s!"cannot absorb {extraBytes} padding bytes into empty chunk '{labelDesc}'"
      let lastIdx := nInstr - 1
      instrSizes := instrSizes.set! lastIdx (instrSizes[lastIdx]! + extraBytes)
  else if !isLastChunk then
    if let some nextAddr := nextAnchorAddr? then
      let endAddr :=
        if nInstr > 0 then
          let last := sliceInsns[nInstr - 1]!
          last.addr + last.byteLen
        else chunkStartAddr
      if nextAddr != endAddr then
        if !opts.absorbPadding || nInstr == 0 then
          throw <| s!"address gap of {nextAddr - endAddr} bytes between '{labelDesc}' " ++
            s!"and next anchor; pass (absorbPadding := true)"
        let lastIdx := nInstr - 1
        instrSizes := instrSizes.set! lastIdx (instrSizes[lastIdx]! + (nextAddr - endAddr))
  let mut out : Array Nat := #[]
  let mut idx := 0
  for tag in chunkTags do
    match tag with
    | .instr =>
      out := out.push instrSizes[idx]!
      idx := idx + 1
    | _ =>
      out := out.push 1
  return out

private def alignProgToElf (arch : TargetArch) (opts : BinaryLayoutOpts)
    (syms : Array ObjSymbol) (insns : Array ObjInsn) (tags : List DirTag) :
    Except String (Nat × Array Nat) := do
  let anchors := match opts.symbols with
    | some xs => xs
    | none => autoEntryAnchors tags
  if anchors.isEmpty then
    if insns.isEmpty then
      throw "disassembled ELF section contains no instructions"
    let startAddr := insns[0]!.addr
    let sizes ← alignChunk arch opts none tags insns startAddr true none
    return (startAddr, sizes)
  let chunks ← splitByAnchors anchors tags
  let allProgLabels := collectAllLabels tags
  let anchorInfos ← anchors.mapM fun a => lookupObjSymbol syms a
  for i in [0 : anchorInfos.length] do
    if i + 1 < anchorInfos.length then
      let a1 := anchorInfos[i]!
      let a2 := anchorInfos[i + 1]!
      if a2.addr < a1.addr then
        throw <| s!"symbols '{a1.name}' ({hexAddr a1.addr}) and '{a2.name}' " ++
          s!"({hexAddr a2.addr}) are out of order in ELF"
  let startAddr := anchorInfos.head!.addr
  let mut allSizes : Array Nat := #[]
  for i in [0 : chunks.length] do
    let (anchor?, chunkTags) := chunks[i]!
    let aName := anchor?.getD anchors[i]!
    let aInfo := anchorInfos[i]!
    let isLast := i + 1 == chunks.length
    let nextAddr? : Option Nat :=
      if isLast then
        let foreign? := syms.find? fun s =>
          s.addr > aInfo.addr && !allProgLabels.contains s.name &&
            !s.name.startsWith (aName ++ ".")
        foreign?.map (·.addr)
      else
        some anchorInfos[i + 1]!.addr
    let sliceInsns := insns.filter fun insn =>
      insn.addr >= aInfo.addr &&
      match nextAddr? with
      | some e => insn.addr < e
      | none => true
    let chunkSizes ←
      alignChunk arch opts (some aName) chunkTags sliceInsns aInfo.addr isLast
        (if isLast then none else nextAddr?)
    allSizes := allSizes ++ chunkSizes
  return (startAddr, allSizes)

private def alignRawToElf (opts : BinaryLayoutOpts)
    (syms : Array ObjSymbol) (insns : Array ObjInsn) :
    Except String (Nat × Array Nat) := do
  match opts.symbols with
  | none =>
    if insns.isEmpty then
      throw "disassembled ELF section contains no instructions"
    return (insns[0]!.addr, insns.map (·.byteLen))
  | some [] =>
    throw "(symbols := []) cannot be empty"
  | some (firstSym :: restSyms) =>
    let symNames := firstSym :: restSyms
    let infos ← symNames.mapM (lookupObjSymbol syms)
    for i in [0 : infos.length] do
      if i + 1 < infos.length then
        let a1 := infos[i]!
        let a2 := infos[i + 1]!
        if a2.addr < a1.addr then
          throw s!"symbols '{a1.name}' and '{a2.name}' are out of order in ELF"
    let firstAddr := infos.head!.addr
    let lastInfo := infos.getLast!
    let endAddr? :=
      (syms.find? fun s =>
        s.addr > lastInfo.addr && !symNames.contains s.name &&
          !symNames.any fun p => s.name.startsWith (p ++ ".")).map (·.addr)
    let slice := insns.filter fun insn =>
      insn.addr >= firstAddr &&
      match endAddr? with
      | some e => insn.addr < e
      | none => true
    if slice.isEmpty then
      throw s!"no instructions found in ELF slice starting at '{firstSym}'"
    return (firstAddr, slice.map (·.byteLen))

private def parseBoolIdent (stx : TSyntax `term) (optName : String) : TermElabM Bool := do
  let e ← Term.elabTerm stx (some (mkConst ``Bool))
  Term.synthesizeSyntheticMVarsNoPostponing
  let e' ← instantiateMVars e
  try
    unsafe evalExpr Bool (mkConst ``Bool) e'
  catch _ =>
    throwError "option '{optName}' must evaluate to a Bool"

private def parseStringLit (stx : TSyntax `term) (optName : String) : TermElabM String := do
  let e ← Term.elabTerm stx (some (mkConst ``String))
  Term.synthesizeSyntheticMVarsNoPostponing
  let e' ← instantiateMVars e
  try
    unsafe evalExpr String (mkConst ``String) e'
  catch _ =>
    throwError "option '{optName}' must evaluate to a String"

private def parseStringList (stx : TSyntax `term) (optName : String) :
    TermElabM (List String) := do
  let listStrTy := mkApp (mkConst ``List [Level.zero]) (mkConst ``String)
  let e ← Term.elabTerm stx (some listStrTy)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e' ← instantiateMVars e
  try
    unsafe evalExpr (List String) listStrTy e'
  catch _ =>
    throwError "option '{optName}' must evaluate to a List String"

private def parseOpts (optStxs : Array (TSyntax `LeanQbe.T.BinaryLayoutElab.binaryLayoutOpt)) :
    TermElabM BinaryLayoutOpts := do
  let mut opts : BinaryLayoutOpts := {}
  for opt in optStxs do
    match opt with
    | `(binaryLayoutOpt| ($key:ident := $val:term)) =>
      match key.getId.toString with
      | "section" => opts := { opts with sectionName := ← parseStringLit val "section" }
      | "symbols" => opts := { opts with symbols := some (← parseStringList val "symbols") }
      | "allowPadding" =>
        opts := { opts with allowPadding := ← parseBoolIdent val "allowPadding" }
      | "absorbPadding" =>
        opts := { opts with absorbPadding := ← parseBoolIdent val "absorbPadding" }
      | other => throwError "unknown binary_layout option '{other}'"
    | _ => throwError "invalid binary_layout option syntax"
  return opts

private def mkNatListExpr (ns : List Nat) : Expr :=
  ns.foldr
    (fun n acc =>
      mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Nat) (mkNatLit n) acc)
    (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Nat))

private def mkNatArrayExpr (sizes : Array Nat) : Expr :=
  mkApp2 (mkConst ``Array.mk [Level.zero]) (mkConst ``Nat) (mkNatListExpr sizes.toList)

private def addPublicDef (declNm : Name) (ty val : Expr) (compile : Bool := true)
    (reducible : Bool := false) : CommandElabM Unit := do
  liftTermElabM do
    let decl := Declaration.defnDecl {
      name := declNm
      levelParams := []
      type := ty
      value := val
      hints := .abbrev
      safety := .safe
    }
    addDecl decl (forceExpose := true)
    if reducible then
      Lean.setReducibilityStatus declNm .reducible
    if compile then
      compileDecl decl
    else
      modifyEnv (Lean.addNoncomputable · declNm)

private def addPublicTheorem (declNm : Name) (ty val : Expr) : CommandElabM Unit := do
  liftTermElabM do
    addDecl (Declaration.thmDecl {
      name := declNm
      levelParams := []
      type := ty
      value := val
    })

private def targetNames (arch : TargetArch) :
    Name × Name × Name × Name × Name × Name :=
  match arch with
  | .x64 =>
    ( `LeanQbe.T.Amd64.x64BinaryLayout
    , `LeanQbe.T.Amd64.x64BinaryTargetLayout
    , `LeanQbe.T.Amd64.x64HostOfBinary
    , `LeanQbe.T.Amd64.x64HostOfBinary_prog
    , `LeanQbe.T.Amd64.x64HostOfBinary_labelsUnique
    , `Program )
  | .arm64 =>
    ( `LeanQbe.T.Arm64.armBinaryLayout
    , `LeanQbe.T.Arm64.armBinaryTargetLayout
    , `LeanQbe.T.Arm64.armHostOfBinary
    , `LeanQbe.T.Arm64.armHostOfBinary_prog
    , `LeanQbe.T.Arm64.armHostOfBinary_labelsUnique
    , `Program )

private def elabBinaryLayout (arch : TargetArch) (nameStx : TSyntax `ident)
    (pathStx : TSyntax `str) (optsPre : Array (TSyntax `LeanQbe.T.BinaryLayoutElab.binaryLayoutOpt))
    (progStx? : Option (TSyntax `term))
    (optsPost : Array (TSyntax `LeanQbe.T.BinaryLayoutElab.binaryLayoutOpt)) :
    CommandElabM Unit := do
  let ns ← getCurrNamespace
  let baseName := ns ++ nameStx.getId
  let binPath := pathStx.getString
  let opts ← liftTermElabM <| parseOpts (optsPre ++ optsPost)
  let (layoutFn, targLayoutFn, hostFn, hostProgThm, hostLabThm, progTyConst) := targetNames arch
  let env ← getEnv
  if !env.contains layoutFn then
    let modHint := match arch with
      | .x64 => "LeanQbe.T.Amd64.BinaryLayout"
      | .arm64 => "LeanQbe.T.Arm64.BinaryLayout"
    throwError "missing '{layoutFn}' in environment; please add `import {modHint}`"
  let (syms, insns) ← liftIO <| runObjdump binPath opts.sectionName
  let progE? ← progStx?.mapM fun stx => liftTermElabM do
    let e ← Term.elabTerm stx (some (mkConst progTyConst))
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let (startAddr, sizes) ←
    match progE? with
    | some progE =>
      let tags ← liftTermElabM <| extractProgTags progE
      match alignProgToElf arch opts syms insns tags with
      | .ok res => pure res
      | .error msg => throwError "binary_layout! failed for '{binPath}': {msg}"
    | none =>
      match alignRawToElf opts syms insns with
      | .ok res => pure res
      | .error msg => throwError "binary_layout! failed for '{binPath}': {msg}"
  let startVal := mkApp (mkConst ``Int64.ofInt) (mkApp (mkConst ``Int.ofNat) (mkNatLit startAddr))
  let startNm := Name.mkStr baseName.getPrefix (baseName.getString! ++ "Start")
  addPublicDef startNm (mkConst ``Int64) startVal
  let sizesTy := mkApp (mkConst ``Array [Level.zero]) (mkConst ``Nat)
  let sizesVal := mkNatArrayExpr sizes
  let sizesNm := Name.mkStr baseName.getPrefix (baseName.getString! ++ "Sizes")
  addPublicDef sizesNm sizesTy sizesVal
  let sizesConst := mkConst sizesNm
  let boolRefl := mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Bool)
    (mkConst ``Bool.true)
  let (posTy, posProof) ← liftTermElabM do
    let fnApp := mkApp (mkConst ``LeanQbe.T.all_pos_of_toList) sizesConst
    let fnTy ← whnf (← inferType fnApp)
    let retTy := fnTy.bindingBody!.instantiate1 boolRefl
    pure (retTy, mkApp fnApp boolRefl)
  let posNm := Name.mkStr baseName.getPrefix (baseName.getString! ++ "Sizes_pos")
  addPublicTheorem posNm posTy posProof
  let startC := mkConst startNm
  let posC := mkConst posNm
  let specVal := mkApp3 (mkConst ``LeanQbe.T.BinaryLayoutSpec.mk) startC sizesConst posC
  let specNm := Name.mkStr baseName.getPrefix (baseName.getString! ++ "Spec")
  addPublicDef specNm (mkConst ``LeanQbe.T.BinaryLayoutSpec) specVal
  let layoutVal := mkApp3 (mkConst layoutFn) startC sizesConst posC
  let layoutTy ← liftTermElabM (inferType layoutVal)
  let layoutNm := Name.mkStr baseName.getPrefix (baseName.getString! ++ "Layout")
  addPublicDef layoutNm layoutTy layoutVal (reducible := true)
  let tLayoutVal := mkApp3 (mkConst targLayoutFn) startC sizesConst posC
  let tLayoutTy ← liftTermElabM (inferType tLayoutVal)
  let tLayoutNm := Name.mkStr baseName.getPrefix (baseName.getString! ++ "TargetLayout")
  addPublicDef tLayoutNm tLayoutTy tLayoutVal
  if let some progE := progE? then
    let smallExpr ← liftTermElabM <| mkAppM ``LeanQbe.T.tableProgSmall #[sizesConst, progE]
    let smallTy ← liftTermElabM <| mkEq smallExpr (mkConst ``Bool.true)
    let smallNm := Name.mkStr baseName.getPrefix (baseName.getString! ++ "Host_small")
    addPublicTheorem smallNm smallTy boolRefl
    let smallC := mkConst smallNm
    let hostVal := mkApp5 (mkConst hostFn) startC sizesConst posC progE smallC
    let hostTy ← liftTermElabM (inferType hostVal)
    let isNoncomp := progE.getUsedConstants.any (Lean.isNoncomputable env)
    let hostNm := Name.mkStr baseName.getPrefix (baseName.getString! ++ "Host")
    addPublicDef hostNm hostTy hostVal (compile := !isNoncomp) (reducible := true)
    let hostC := mkConst hostNm
    let hProgVal := mkApp5 (mkConst hostProgThm) startC sizesConst posC progE smallC
    let hProgTy ← liftTermElabM <| mkEq (mkApp (mkConst `Host.prog) hostC) progE
    let hProgNm := Name.mkStr baseName.getPrefix (baseName.getString! ++ "Host_prog")
    addPublicTheorem hProgNm hProgTy hProgVal
    let nodupExpr ← liftTermElabM do
      let listDirTy ← whnf (← inferType progE)
      let some dirTy := listDirTy.getAppArgs[0]?
        | throwError "expected List (Kraken.Directive ...) type for program"
      let dirTyW ← whnf dirTy
      let dirArgs := dirTyW.getAppArgs
      if h : dirArgs.size = 2 then
        let dirLabFn := mkApp2 (mkConst ``LeanQbe.T.dirLabel?) dirArgs[0] dirArgs[1]
        mkAppM `LeanQbe.T.labelsNodupBy #[dirLabFn, progE]
      else
        throwError "expected Kraken.Directive type for program element, got {dirTyW}"
    let nodupTy ← liftTermElabM <| mkEq nodupExpr (mkConst ``Bool.true)
    let nodupNm := Name.mkStr baseName.getPrefix (baseName.getString! ++ "Host_labelsNodup")
    addPublicTheorem nodupNm nodupTy boolRefl
    let nodupC := mkConst nodupNm
    let hLabVal := mkApp6 (mkConst hostLabThm) startC sizesConst posC progE smallC nodupC
    let hLabTy := mkApp (mkConst `Host.LabelsUnique) hostC
    let hLabNm := Name.mkStr baseName.getPrefix (baseName.getString! ++ "Host_labelsUnique")
    addPublicTheorem hLabNm hLabTy hLabVal

elab_rules : command
  | `(command| binary_layout_x64! $name:ident $path:str $opts1:binaryLayoutOpt*
        $[for $prog:term]? $opts2:binaryLayoutOpt*) =>
    elabBinaryLayout .x64 name path opts1 prog opts2
  | `(command| binary_layout_arm64! $name:ident $path:str $opts1:binaryLayoutOpt*
        $[for $prog:term]? $opts2:binaryLayoutOpt*) =>
    elabBinaryLayout .arm64 name path opts1 prog opts2

end LeanQbe.T.BinaryLayoutElab

end
