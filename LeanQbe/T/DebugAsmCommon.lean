module

public import LeanQbe.T.Main
public import Std.Data.HashSet

/-!
# Target-Generic ELF Debug Assembly, Label Scrubbing & DWARF CFI Helpers

Shared architecture-independent machinery for `LeanQbe.T.Amd64.DebugAsm` and
`LeanQbe.T.Arm64.DebugAsm`:
* Function-slice splitting (`splitFnSlices`), `{fn}.L{i}` local-label scrubbing (`scrubSym`), and
  prefix/suffix list utilities (`dropPrefix?`, `isSuffixOf`).
* Generic frame-slot inference (`collectSavePrefix`, `collectRestoreRev`, `collectTailRestores`,
  `inferSavedSlice`).
* ELF/DWARF `.cfi_*` emission (`emitFnWithCfi`) and top-level `emitDebugAsmChecked`.

Imports neither `Kraken.X64` nor `Kraken.AArch64` nor any `*Lemmas*` module.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.DebugAsmCommon

open Std
open LeanQbe.T

/-- Frame inference result shared across targets. -/
structure FnFrameInfo (Reg : Type) where
  zeroFrame : Bool
  nslots : Nat
  saved : List Reg

/-- Target-specific hooks for ELF/DWARF CFI assembly emission. -/
structure DebugAsmCfg (D Reg : Type) where
  commentPfx : String
  p2align? : Option String
  emitLtorg : Bool
  cfaDesc : Nat → String
  frameSize : Nat → Nat
  cfaBase : Nat → Nat
  proSteps : Sym → Nat → Nat → List (List D × List String × String)
  nextSave : Nat → List Reg → Option (List Reg × List D × List Reg)
  mkRestoreChunks : Nat → List Reg → List (List Reg × List D)
  epiSections : Nat → Nat → List (List D × List String)
  isTailDir : D → Option String
  printDir : D → String
  cfiReg : Reg → String
  preBodyDir : D → Option String := fun _ => none

def scrubSym (fn : Sym) (nonLocal : HashSet Sym) (s : Sym) : Sym :=
  let pfx := fn ++ ".L"
  let tail := String.ofList (s.toList.drop pfx.length)
  if !nonLocal.contains s && s.startsWith pfx && !tail.isEmpty && tail.toList.all Char.isDigit
  then ".L" ++ s else s

def isLocalFnLabel (fn : Sym) (nonLocal : HashSet Sym) (s : Sym) : Bool :=
  let dotPfx := ".L" ++ fn ++ "."
  let dotTail := String.ofList (s.toList.drop dotPfx.length)
  let alreadyLocal :=
    !nonLocal.contains s && s.startsWith dotPfx && !dotTail.isEmpty &&
      dotTail.toList.all Char.isDigit
  alreadyLocal || scrubSym fn nonLocal s != s

def dropPrefix? {α : Type} [BEq α] : List α → List α → Option (List α)
  | [], ys => some ys
  | x :: xs, y :: ys => if x == y then dropPrefix? xs ys else none
  | _ :: _, [] => none

def isSuffixOf {α : Type} [BEq α] (suf xs : List α) : Bool :=
  suf.length <= xs.length && xs.drop (xs.length - suf.length) == suf

def splitFnSlices {D : Type} (label? : D → Option Sym) (pp : D → String) :
    List Sym → List D → Except String (List (Sym × List D))
  | [], [] => .ok []
  | [], d :: _ => .error s!"unexpected trailing directives after functions: {pp d}"
  | nm :: _, [] => .error s!"unexpected EOF before function '{nm}'"
  | nm :: rest, d :: body =>
    match label? d with
    | none => .error s!"expected function label '{nm}', found '{pp d}'"
    | some l =>
      if l != nm then .error s!"expected function label '{nm}', found '{l}'"
      else match rest with
        | [] => .ok [(nm, body)]
        | g :: _ => do
          let (fnBody, rem) := body.span (fun x => label? x != some g)
          .ok ((nm, fnBody) :: (← splitFnSlices label? pp rest rem))

def collectSavePrefix {D Reg : Type} [BEq Reg]
    (matchStep : List D → Option (Nat × List Reg × List D)) (slotOk : Nat → List Reg → Bool) :
    Nat → Option Nat → List Reg → List D → List (Nat × Reg)
  | 0, _, _, _ => []
  | fuel + 1, expSlot, seen, ds =>
    match matchStep ds with
    | none => []
    | some (slot, regs, rest) =>
      let ok := (match expSlot with | none => true | some exp => slot == exp) &&
        slotOk slot regs && regs.all (!seen.contains ·)
      if ok then
        ((List.range regs.length).zip regs |>.map fun (k, r) => (slot + k, r)) ++
          collectSavePrefix matchStep slotOk fuel (some (slot + regs.length))
            (regs.reverse ++ seen) rest
      else []

def collectRestoreRev {D Reg : Type} [BEq Reg]
    (matchStepRev : List D → Option (Nat × List Reg × List D)) :
    Nat → Option Nat → List Reg → List D → List (Nat × Reg)
  | 0, _, _, _ => []
  | fuel + 1, expSlot?, seen, dsRev =>
    match matchStepRev dsRev with
    | none => []
    | some (slot, regs, prev) =>
      let top := slot + regs.length - 1
      let ok := (match expSlot? with | none => true | some exp => top == exp) &&
        regs.all (!seen.contains ·)
      if ok then
        let pairs :=
          ((List.range regs.length).zip regs |>.map fun (k, r) => (slot + k, r)).reverse
        if slot > 0 then
          pairs ++ collectRestoreRev matchStepRev fuel (some (slot - 1)) (regs ++ seen) prev
        else pairs
      else []

def collectTailRestores {D Reg : Type} [BEq D] [BEq Reg]
    (matchStepRev : List D → Option (Nat × List Reg × List D))
    (isTailDir : D → Option String) (epi : List D) :
    List D → List D → List (List (Nat × Reg)) → List (List (Nat × Reg))
  | _, [], acc => acc
  | revSeen, ds@(d :: rest), acc =>
    let acc := match dropPrefix? epi ds with
      | some (tailD :: _) =>
        if (isTailDir tailD).isSome then
          (collectRestoreRev matchStepRev revSeen.length none [] revSeen).reverse :: acc
        else acc
      | _ => acc
    collectTailRestores matchStepRev isTailDir epi (d :: revSeen) rest acc

def inferSavedSlice {Reg : Type} [BEq Reg]
    (cands : List (Nat × Reg)) (tails : List (List (Nat × Reg)))
    (defaultSlots : Nat) (slotOk : Nat → Nat → Bool) : Option (Nat × List Reg) :=
  let rec go : Nat → Option (Nat × List Reg)
    | 0 => some (defaultSlots, [])
    | m + 1 => match cands.take (m + 1) with
      | [] => some (defaultSlots, [])
      | slice@((base, _) :: _) =>
        if slotOk base slice.length && tails.all (isSuffixOf slice) then
          some (base, slice.map Prod.snd)
        else go m
  go cands.length

private def pushRaw {D Reg : Type} (cfg : DebugAsmCfg D Reg) (lds : List D) (a : Array String) :
    Array String := lds.foldl (·.push <| cfg.printDir ·) a

private def pushPreDir {D Reg : Type} (cfg : DebugAsmCfg D Reg) (a : Array String) (d : D) :
    Array String := (cfg.preBodyDir d |>.elim a a.push).push (cfg.printDir d)

private def emitBodyTails {D Reg : Type} [BEq D] (cfg : DebugAsmCfg D Reg) (comments : Bool)
    (restoreChunks : List (List Reg × List D)) (restoreFlat : List D)
    (epiSections : List (List D × List String)) (epiFlat : List D) :
    Nat → List D → Array String → Array String
  | 0, rem, out => rem.foldl (pushPreDir cfg) out
  | _ + 1, [], out => out
  | fuel + 1, rem@(d :: ds), out =>
    let step := match dropPrefix? restoreFlat rem with
      | some afterRest => match dropPrefix? epiFlat afterRest with
        | some (tailD :: afterTail) => (cfg.isTailDir tailD).map (·, tailD, afterTail)
        | _ => none
      | none => none
    match step with
    | some (kind, tailD, afterTail) =>
      let needState := !afterTail.isEmpty
      let out := if comments then out.push s!"\t{cfg.commentPfx} epilogue ({kind})" else out
      let out := if needState then out.push "\t.cfi_remember_state" else out
      let out := restoreChunks.foldl (fun acc (rs, lds) =>
        rs.foldl (fun a r => a.push s!"\t.cfi_restore {cfg.cfiReg r}") (pushRaw cfg lds acc)) out
      let out := epiSections.foldl (fun acc (eds, cfis) =>
        cfis.foldl (·.push ·) (pushRaw cfg eds acc)) out
      let out := out.push (cfg.printDir tailD)
      let out := if needState then out.push "\t.cfi_restore_state" else out
      emitBodyTails cfg comments restoreChunks restoreFlat epiSections epiFlat fuel afterTail out
    | none =>
      emitBodyTails cfg comments restoreChunks restoreFlat epiSections epiFlat fuel ds
        (pushPreDir cfg out d)

def emitFnWithCfi {D Reg : Type} [BEq D] (cfg : DebugAsmCfg D Reg)
    (fn : Sym) (info : FnFrameInfo Reg) (comments : Bool) (body : List D)
    (out : Array String) : Except String (Array String) :=
  let emitHdr sz savedNames :=
    let out := if comments then
      out.push s!"{cfg.commentPfx} fn {fn}: frame={sz}B cfa={cfg.cfaDesc sz} saved=[{savedNames}]"
      else out
    let out := cfg.p2align?.elim out out.push
    out |>.push s!"\t.globl {fn}" |>.push s!"\t.type {fn}, %function"
      |>.push s!"{fn}:" |>.push "\t.cfi_startproc"
  let emitFtr (a : Array String) :=
    let a := a.push "\t.cfi_endproc" |>.push s!"\t.size {fn}, .-{fn}"
    if cfg.emitLtorg then a.push "\t.ltorg" else a
  if info.zeroFrame then .ok (emitFtr (body.foldl (pushPreDir cfg) (emitHdr 0 "")))
  else
    let ns := info.nslots + info.saved.length; let sz := cfg.frameSize ns
    let cbase := cfg.cfaBase sz
    let rec matchPro (ds : List D) (acc : Array String) :
        List (List D × List String × String) → Except String (Array String × List D)
      | [] => .ok (acc, ds)
      | (pds, cfis, err) :: rest => match dropPrefix? pds ds with
        | none => .error err
        | some rem => matchPro rem (cfis.foldl (·.push ·) (pushRaw cfg pds acc)) rest
    let rec consumeSaves : Nat → Nat → List D → Array String → List Reg →
        Except String (Array String × List D)
      | 0, _, ds, acc, _ => .ok (acc, ds)
      | fuel + 1, idx, ds, acc, rs => match cfg.nextSave idx rs with
        | none => .ok (acc, ds)
        | some (chunkRegs, st, restRegs) => match dropPrefix? st ds with
          | none =>
            let r0 := chunkRegs.head?.map cfg.cfiReg |>.getD "?"
            .error s!"function '{fn}': saveCs mismatch for {r0} at slot {idx}"
          | some rest =>
            let acc := (List.range chunkRegs.length).zip chunkRegs |>.foldl (fun a (k, r) =>
              a.push s!"\t.cfi_offset {cfg.cfiReg r}, -{cbase - 8 * (idx + k)}")
              (pushRaw cfg st acc)
            consumeSaves fuel (idx + chunkRegs.length) rest acc restRegs
    match matchPro body (emitHdr sz (String.intercalate "," (info.saved.map cfg.cfiReg)))
        (cfg.proSteps fn ns sz) with
    | .error e => .error e
    | .ok (out, afterPro) =>
      match consumeSaves info.saved.length info.nslots afterPro out info.saved with
      | .error e => .error e
      | .ok (out, restBody) =>
        let restoreChunks := cfg.mkRestoreChunks info.nslots info.saved
        let epis := cfg.epiSections ns sz
        .ok (emitFtr (emitBodyTails cfg comments restoreChunks (restoreChunks.flatMap Prod.snd)
          epis (epis.flatMap Prod.fst) restBody.length restBody out))

def fnInfoOfHints {D Reg : Type} [BEq D] (leafZero : Bool) (pro0 : List D) (isNonLeaf : D → Bool)
    (errMsg : String) (nslots : Nat) (saved : List Reg) (body : List D) :
    Except String (FnFrameInfo Reg) :=
  if nslots + saved.length == 0 && leafZero then
    match dropPrefix? pro0 body with
    | some _ => .ok ⟨false, 0, []⟩
    | none => if !body.any isNonLeaf then .ok ⟨true, 0, []⟩ else .error errMsg
  else .ok ⟨false, nslots, saved⟩

def emitDebugAsmChecked {D Reg Hints : Type} (label? : D → Option Sym) (pp : D → String)
    (fnInfoOfHints : Sym → List D → Hints → Except String (FnFrameInfo Reg))
    (inferFnFrame : Sym → HashSet Sym → List D → Except String (FnFrameInfo Reg))
    (emitFn : Sym → FnFrameInfo Reg → HashSet Sym → List D → Array String →
      Except String (Array String))
    (fs : List Fn) (code : List D) (hints? : Option (List Hints)) (exits : List Sym) :
    Except String String := do
  let names := fs.map (·.name)
  let slices ← splitFnSlices label? pp names code
  let nonLocal := (names ++ exits).foldl (fun s k => s.insert k) ({} : HashSet Sym)
  let pairs ← match hints? with
    | some hs =>
      if hs.length != fs.length then
        .error s!"hints length {hs.length} != functions length {fs.length}"
      else
        (slices.zip hs).mapM fun ((fn, body), h) => return ((fn, body), ← fnInfoOfHints fn body h)
    | none => slices.mapM fun (fn, body) => return ((fn, body), ← inferFnFrame fn nonLocal body)
  let mut out : Array String := #[".text"]
  for ((fn, body), info) in pairs do out ← emitFn fn info nonLocal body out
  return String.intercalate "\n" out.toList ++ "\n"

end LeanQbe.T.DebugAsmCommon
