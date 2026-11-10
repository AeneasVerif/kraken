module

meta import LeanQbe.Print
meta import spike.il.Smoke

/-! Regression test of `LeanQbe.Print` (the full differential test against stock QBE is
`scripts/qbe_difftest.sh`). -/

open LeanQbe

#guard (Print.fn ⟨"tracer", Smoke.tracer⟩).toOption == some "export function l $tracer(l %v0, l %v1, l %v2) {
@start
\t%v3 =l add %v0, %v1
\tstorel %v3, %v2
\tret %v3
}
"

-- Junk is rejected.
#guard (Print.fn ⟨"bad", fun _ _ => .ret [.imm 0, .imm 1]⟩).toOption.isNone
#guard (Print.fn ⟨"bad", fun _ _ => .let_ (.copy .l (.imm 0)) fun _ => .param fun x => .ret [.var x]⟩).toOption.isNone
