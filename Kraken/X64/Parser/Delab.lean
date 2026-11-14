module

public import Kraken.X64.Parser.Rules
public meta import Kraken.X64.Parser.Rules
public meta import Lean

/-!
Delaborators of the X64 syntax categories that are not written with `notation ... in c`:
constants, `disp(%rip)` memory operands and relative jump targets (issue 5 of
`Kraken/X64/Parser/design.md`). They produce the embeddings `⸨const| … ⸩`, `⸨mem| … ⸩` and
`⸨target| … ⸩`, which the printers of `notation ... in c` rules take apart.
-/

namespace Kraken.X64.Parser
open Lean Meta PrettyPrinter Delaborator SubExpr Kraken.Parser

public meta section

private def annotateStx {cat : Name} (stx : TSyntax cat) : DelabM (TSyntax cat) := do
  return ⟨(← annotateTermInfo ⟨stx.raw⟩).raw⟩

private def evalInt64? (e : Expr) : Option Int :=
  e.int?.map fun i => (Int64.ofInt i).toInt

/-- Delaborate a `Label` into an `x64_ident`, falling back to `❰t❱`. -/
def delabIdent : DelabM (TSyntax `x64_ident) := do
  if let .lit (.strVal s) ← getExpr then
    if isAsmIdent s then
      return ← annotateStx ⟨Syntax.node .none ``x64_ident_ #[Syntax.atom .none s]⟩
  let t ← delab
  annotateStx (← `(x64_ident| ❰ $t ❱))

/-- Delaborate a `ConstExpr` into an `x64_const`, falling back to `❰t❱` for open terms. -/
def delabConstExpr : DelabM (TSyntax `x64_const) := do
  let stx ← match_expr ← getExpr with
  | ConstExpr.int64 iExpr =>
    if let some i := evalInt64? iExpr then
      if i ≥ 0 then
        let n := Syntax.mkNumLit (toString i.toNat)
        `(x64_const| $n:num)
      else
        let n := Syntax.mkNumLit (toString (-i).toNat)
        `(x64_const| -$n:num)
    else
      let t ← withAppArg delab
      `(x64_const| ❰ $t ❱)
  | ConstExpr.label _ =>
    let id ← withAppArg delabIdent
    `(x64_const| $id:x64_ident)
  | ConstExpr.add aExpr bExpr =>
    if aExpr.isAppOfArity ``ConstExpr.label 1 then
      match_expr bExpr with
      | ConstExpr.int64 iExpr =>
        if let some i := evalInt64? iExpr then
          let id ← withNaryArg 0 (withAppArg delabIdent)
          if i ≥ 0 then
            let n := Syntax.mkNumLit (toString i.toNat)
            `(x64_const| $id:x64_ident + $n:num)
          else
            let n := Syntax.mkNumLit (toString (-i).toNat)
            `(x64_const| $id:x64_ident - $n:num)
        else
          let t ← delab
          `(x64_const| ❰ $t ❱)
      | _ =>
        let t ← delab
        `(x64_const| ❰ $t ❱)
    else
      let t ← delab
      `(x64_const| ❰ $t ❱)
  | ConstExpr.sub aExpr bExpr =>
    if aExpr.isAppOfArity ``ConstExpr.label 1 then
      match_expr bExpr with
      | ConstExpr.int64 iExpr =>
        if let some i := evalInt64? iExpr then
          let id ← withNaryArg 0 (withAppArg delabIdent)
          if i ≥ 0 then
            let n := Syntax.mkNumLit (toString i.toNat)
            `(x64_const| $id:x64_ident - $n:num)
          else
            let n := Syntax.mkNumLit (toString (-i).toNat)
            `(x64_const| $id:x64_ident + $n:num)
        else
          let t ← delab
          `(x64_const| ❰ $t ❱)
      | ConstExpr.label _ =>
        let a ← withNaryArg 0 (withAppArg delabIdent)
        let b ← withNaryArg 1 (withAppArg delabIdent)
        `(x64_const| $a:x64_ident - $b:x64_ident)
      | _ =>
        let t ← delab
        `(x64_const| ❰ $t ❱)
    else
      let t ← delab
      `(x64_const| ❰ $t ❱)
  | _ =>
    let t ← delab
    `(x64_const| ❰ $t ❱)
  annotateStx stx

@[delab app.ConstExpr.int64, delab app.ConstExpr.label,
  delab app.ConstExpr.add, delab app.ConstExpr.sub]
def delabConstEntry : Delab := whenPPOption getPPNotation do
  let c ← delabConstExpr
  if c.raw.isOfKind ``x64_const.escape then failure
  `(⸨const| $c ⸩)

/-- `disp(%rip)`, the inverse of `elabRipMemory`. -/
@[delab app.AddrExpr.mk]
def delabRipMemory : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  let_expr AddrExpr.mk base idx disp := e | failure
  let_expr Option.some _ b := base | failure
  unless b.isConstOf ``RegOrRip.rip && idx.isAppOfArity ``Option.none 1 do failure
  let d? : Option (TSyntax `x64_const) ← match_expr disp with
    | ConstExpr.sub d after =>
      unless after.isConstOf ``ConstExpr.after_current_instruction do failure
      if d.isAppOfArity ``ConstExpr.int64 1 then failure
      some <$> withNaryArg 2 (withNaryArg 0 delabConstExpr)
    | ConstExpr.int64 i =>
      if evalInt64? i == some 0 then pure none else some <$> withNaryArg 2 delabConstExpr
    | _ => failure
  if let some d := d? then if d.raw.isOfKind ``x64_const.escape then failure
  `(⸨mem| $[$d?:x64_const]?(%rip) ⸩)

/-- A label as a jump target, the inverse of `elabRelTarget`. -/
@[delab app.RelRegOrMem.rel]
def delabRelTarget : Delab := whenPPOption getPPNotation do
  let e ← getExpr
  let_expr RelRegOrMem.rel c := e | failure
  let_expr ConstExpr.sub l after := c | failure
  unless after.isConstOf ``ConstExpr.after_current_instruction && l.isAppOfArity ``ConstExpr.label 1 do
    failure
  let id ← withAppArg (withNaryArg 0 (withAppArg delabIdent))
  `(⸨target| $id:x64_ident ⸩)

end

end Kraken.X64.Parser
