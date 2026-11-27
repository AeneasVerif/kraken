module

public import LeanQbe.T.Live

/-!
# Wave 6.2-A Liveness / Elision Passes (`LiveW62`, untrusted)

In-block `load (.bits 64/32) -> trunc` narrowing (`elideLoadTruncDeps`, `OPT-10b`) and
extended straight-line `shl`/`zext`/`add` -> `lea`/`shiftAlu`/`shiftCmp` dep propagation
(`elideLeaTreeDeps`). Untrusted: verified by `Rega.lowerFn`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T
namespace Live

open Rega

/-- `true` when `I` supports loading `.bits n` from address variable `av` whose definition was
elided in `defs`. -/
def supportsElidedAddrForWidth (I : Isa) (defs : Trie DefFact) (n : Nat) (av : Nat) : Bool :=
  let tyN := Ty.bits n
  match addrDefOf I.gpr.addrCse defs av with
  | some (.imm64 _) => true
  | some (.addImm64 _ disp) => I.supportsAddrDisp tyN disp
  | some (.addrSum b i sh disp) =>
    match AddrScale.ofShift? sh with
    | some sc =>
      I.supportsAddrIdx tyN sc disp ||
        (I.supportsAddrZextIdx tyN sc disp && (zextAddrSumVar? defs b i sh).isSome)
    | none => false
  | _ => false

structure TruncFold where
  ipLoad : Nat
  ipTrunc : Nat
  ldeps : List Nat

mutual
/-- Collect `defs` and `elidedVars` from the pre-elision tree `t0` (where elided `.let_` nodes have
not yet been rewritten to `.skip`) for `elideIps`. -/
def collectElidedAddrDefs (I : Isa) (elideIps : Trie Bool) (defs : Trie DefFact)
    (elidedVars : Trie Bool) : Tree → Trie DefFact × Trie Bool
  | .let_ _ ip nv0 _ op k =>
    let { sig := _, code, args } := op
    let defs' := match recordDefC I.gpr.addrCse defs code args with
      | some df => defs.insert nv0 df
      | none => defs
    let elided' := if elideIps.getD ip false then elidedVars.insert nv0 true else elidedVars
    collectElidedAddrDefs I elideIps defs' elided' k
  | .load _ _ _ _ _ k | .store _ _ _ _ _ k | .call _ _ _ _ _ _ _ k | .skip _ _ k =>
    collectElidedAddrDefs I elideIps defs elidedVars k
  | .jnz _ _ _ _ t e =>
    let (d1, e1) := collectElidedAddrDefs I elideIps defs elidedVars t
    collectElidedAddrDefs I elideIps d1 e1 e
  | .group _ bs k =>
    let (d1, e1) := collectElidedAddrDefsB I elideIps defs elidedVars bs
    collectElidedAddrDefs I elideIps d1 e1 k
  | _ => (defs, elidedVars)

def collectElidedAddrDefsB (I : Isa) (elideIps : Trie Bool) (defs : Trie DefFact)
    (elidedVars : Trie Bool) : TreeBlocks → Trie DefFact × Trie Bool
  | .nil => (defs, elidedVars)
  | .cons _ _ b bs =>
    let (d1, e1) := collectElidedAddrDefs I elideIps defs elidedVars b
    collectElidedAddrDefsB I elideIps d1 e1 bs
end

mutual
def scanLoadTrunc (I : Isa) (useCnt : Trie Nat) (addrDeps : Trie (List Nat))
    (elideIps : Trie Bool) (defs : Trie DefFact) (elidedVars : Trie Bool)
    (avail : Trie (Nat × Nat × Arg VNat i64 × List Nat)) :
    Tree → List TruncFold → List TruncFold
  | .let_ _ ip nv0 _ op k, acc =>
    let { sig := _, code, args } := op
    let df? := recordDefC I.gpr.addrCse defs code args
    let defs' := match df? with | some df => defs.insert nv0 df | none => defs
    if elideIps.getD ip false then
      scanLoadTrunc I useCnt addrDeps elideIps defs' (elidedVars.insert nv0 true) avail k acc
    else
      let acc' := match code, args with
        | .trunc m n, (.var x, ()) =>
          if [8, 16, 32].contains n && Nat.blt n m && I.frame.bitWidths.contains n then
            match avail.find? x with
            | some (ipL, mw, a, ldeps) =>
              if !Nat.beq mw m then acc
              else
                let addrOk := match a with
                  | .imm _ => true
                  | .var av =>
                    !elidedVars.getD av false || supportsElidedAddrForWidth I defs' n av
                if addrOk then ⟨ipL, ip, ldeps⟩ :: acc else acc
            | none => acc
          else acc
        | _, _ => acc
      scanLoadTrunc I useCnt addrDeps elideIps defs' elidedVars avail k acc'
  | .load _ ip x (.bits m) a k, acc =>
    let avail' :=
      if !elideIps.getD ip false && Nat.beq (useCnt.getD x 0) 1 &&
          (Nat.beq m 64 || Nat.beq m 32 || Nat.beq m 16) then
        let ldeps := addrDeps.getD ip (argVarIds a)
        avail.insert x (ip, m, a, ldeps)
      else avail
    scanLoadTrunc I useCnt addrDeps elideIps defs elidedVars avail' k acc
  | .load _ _ _ _ _ k, acc =>
    scanLoadTrunc I useCnt addrDeps elideIps defs elidedVars avail k acc
  | .store _ _ _ _ _ k, acc | .call _ _ _ _ _ _ _ k, acc =>
    scanLoadTrunc I useCnt addrDeps elideIps defs elidedVars .empty k acc
  | .jnz _ _ _ _ t e, acc =>
    let acc1 := scanLoadTrunc I useCnt addrDeps elideIps defs elidedVars .empty t acc
    scanLoadTrunc I useCnt addrDeps elideIps defs elidedVars .empty e acc1
  | .skip _ _ k, acc =>
    scanLoadTrunc I useCnt addrDeps elideIps defs elidedVars avail k acc
  | .group _ bs k, acc =>
    let acc1 := scanLoadTruncB I useCnt addrDeps elideIps defs elidedVars bs acc
    scanLoadTrunc I useCnt addrDeps elideIps defs elidedVars .empty k acc1
  | _, acc => acc

def scanLoadTruncB (I : Isa) (useCnt : Trie Nat) (addrDeps : Trie (List Nat))
    (elideIps : Trie Bool) (defs : Trie DefFact) (elidedVars : Trie Bool) :
    TreeBlocks → List TruncFold → List TruncFold
  | .nil, acc => acc
  | .cons _ _ b bs, acc =>
    let acc1 := scanLoadTrunc I useCnt addrDeps elideIps defs elidedVars .empty b acc
    scanLoadTruncB I useCnt addrDeps elideIps defs elidedVars bs acc1
end

/-- Elide straight-line `load (.bits 64/32/16) a` into a single-use `.trunc m n` (`n ∈ {8,16,32}`),
marking the original load `ip` elided and moving its address dependencies to the `trunc` `ip`.
Uses pre-elision `t0` so address definitions already rewritten to `.skip` in `t` remain visible. -/
def elideLoadTruncDeps (I : Isa) (t0 t : Tree) (elideIps : Trie Bool)
    (addrDeps : Trie (List Nat)) : Tree × Trie Bool × Trie (List Nat) :=
  if !(I.frame.bitWidths.contains 32 && I.supportsAddrDisp (.bits 32) 0) then (t, elideIps,
    addrDeps)
  else
    let useCnt := countRawUses addrDeps t .empty
    let (defs0, elided0) := collectElidedAddrDefs I elideIps .empty .empty t0
    let folds := scanLoadTrunc I useCnt addrDeps elideIps defs0 elided0 .empty t []
    if folds.isEmpty then (t, elideIps, addrDeps)
    else
      let (eip', deps') := folds.foldl (fun (eip, deps) f =>
        (eip.insert f.ipLoad true, deps.insert f.ipTrunc (dedup f.ldeps))) (elideIps, addrDeps)
      (rewriteCmpElide eip' t, eip', deps')

end Live
end LeanQbe.T
