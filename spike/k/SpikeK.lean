module

public import Kraken.X64.WP
public import Kraken.X64.Sep
import Kraken.X64.Parser

/-!
# Spike K: control-flow lemmas for code generated *to* Kraken x64

Everything here is generic in the `Host` (host program + unknown layout) and in the position of the
instruction in the host program. Nothing mentions a concrete address.
-/

set_option autoImplicit false

@[expose] public section

namespace SpikeK

/-! ## The encodings the x64 parser produces -/

/-- `jmp L` -/
abbrev jmpTo (L : Label) : Directive :=
  .instr (.regular .W64 .W64 (.jmp (.rel (.sub (.label L) .after_current_instruction))))

/-- `jcc L`, e.g. `jnz L` is `jccTo .nz L` -/
abbrev jccTo (cc : CondCode) (L : Label) : Directive :=
  .instr (.regular .W64 .W64 (.jcc cc L))

/-- `call L` -/
abbrev callTo (L : Label) : Directive :=
  .instr (.regular .W64 .W64 (.call (.rel (.sub (.label L) .after_current_instruction))))

/-- `ret` -/
abbrev retD : Directive := .instr (.regular .W64 .W64 .ret)

/-- `dec %r` for a 64-bit register `r` -/
abbrev dec64 (r : Reg64) : Directive :=
  .instr (.regular .W64 .W64 (.dec (.reg (.low r .W64))))

section ParserChecks
open Kraken.X64.Parser

example : parse("jmp sym") = [jmpTo "sym"] := rfl
example : parse("jnz sym") = [jccTo .nz "sym"] := rfl
example : parse("call sym") = [callTo "sym"] := rfl
example : parse("ret") = [retD] := rfl
example : parse("dec %rcx") = [dec64 .rcx] := rfl

end ParserChecks

/-! ## List helpers -/

theorem findSome?_eq_of_getElem? {α β : Type _} {f : α → Option β} {l : List α} {k : Nat} {a : α}
    {b : β} (hk : l[k]? = some a) (hf : f a = some b)
    (hprior : ∀ j, j < k → ∀ c, l[j]? = some c → f c = none) :
    l.findSome? f = some b := by
  induction l generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      simp [hf]
    | succ k =>
      have hx : f x = none := hprior 0 (Nat.succ_pos k) x (by simp)
      rw [List.findSome?_cons, hx]
      exact ih (by simpa using hk) (fun j hj c hc => hprior (j + 1) (by omega) c (by simpa using hc))

theorem isInfixAt_singleton {α : Type _} {d : α} {l : List α} {k : Nat} :
    [d].IsInfixAt l k ↔ l[k]? = some d := by
  rw [List.isInfixAt_iff_getElem?]
  constructor
  · intro h
    simpa using h 0 (by simp)
  · intro h i hi
    have : i = 0 := by simpa using hi
    subst this
    simpa using h

/-! ## K1: label resolution -/

/--
K1. If the `k`-th directive of the host program is `.label l` and no earlier directive is, then the
address the semantics assigns to `l` (through `Executable.labels Host.exe`) is `Host.addrOf k`.
-/
theorem label_eq_addrOf [Host] {l : Label} {k : Nat}
    (hk : Host.prog[k]? = some (.label l))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label l)) :
    @Labels.label (Executable.labels Host.exe) l = Host.addrOf k := by
  show (Host.exe.withAddresses.findSome? _).getD (-1) = Host.addrOf k
  rw [findSome?_eq_of_getElem? (k := k)
    (a := { directive := .label l, size := Kraken.Layout.size Instr k, addr := Host.exe.addrOf k })
    (b := Host.exe.addrOf k)]
  · rfl
  · rw [Kraken.Executable.getElem?_withAddresses_eq, Host.exe_getElem?, hk]
    rfl
  · simp
  · intro j hj c hc
    rw [Kraken.Executable.getElem?_withAddresses_eq, Host.exe_getElem?] at hc
    cases hd : Host.prog[j]? with
    | none => simp [hd] at hc
    | some d =>
      simp only [hd, Option.map_some, Option.some.injEq] at hc
      subst hc
      have hne : d ≠ .label l := fun h => hfirst j hj (by rw [hd, h])
      simp [hne]

/-- K1, stated with the `Labels` instance that instance resolution finds under `[Host]`. -/
theorem label_eq_addrOf' [Host] {l : Label} {k : Nat}
    (hk : Host.prog[k]? = some (.label l))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label l)) :
    Labels.label l = Host.addrOf k :=
  label_eq_addrOf hk hfirst

/-! ## The generic one-directive step lemma, in continuation-passing form -/

/--
To run from the `i`-th directive `d` of the host program, it suffices that every outcome of
interpreting `d` (fall-through to `Host.addrOf (i + 1)` or a jump) eventually reaches `post`.
This is `Host.eventually_of_interp` composed with `eventually_trans`.
-/
theorem eventually_of_interp_cps [Host] {i : Nat} {d : Directive} {post : @Post MachineState}
    {s : MachineData} (hi : Host.prog[i]? = some d)
    (h : (d.interp s ⟨Host.addrOf i, Host.addrOf (i + 1)⟩
      (fun s' => .done ⟨s', Host.addrOf (i + 1)⟩) (fun a s' => .done ⟨s', a⟩)).All
        (fun st => Eventually (step1 Host.exe) post st)) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ :=
  eventually_trans _ _ _ _
    (Host.eventually_of_interp (p := []) (isInfixAt_singleton.mpr hi) h) (fun _ h => h)

/-- Labels are skipped (whatever size the layout gives them). -/
theorem eventually_label [Host] {i : Nat} {l : Label} {post : @Post MachineState}
    {s : MachineData} (hi : Host.prog[i]? = some (.label l))
    (h : Eventually (step1 Host.exe) post ⟨s, Host.addrOf (i + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ :=
  eventually_of_interp_cps hi h

/-! ## K2: direct jump -/

/--
K2. `jmp L` at index `i`, where `L` resolves to index `k`: to run from the jump it suffices to run
from the label, in the same machine data.
-/
theorem eventually_jmp [Host] {i k : Nat} {L : Label} {post : @Post MachineState}
    {s : MachineData}
    (hi : Host.prog[i]? = some (jmpTo L))
    (hk : Host.prog[k]? = some (.label L))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (h : Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All]
  rw [label_eq_addrOf' hk hfirst, Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  exact h

/-! ## K3: conditional jump -/

/--
K3. `jcc cc L` at index `i`, where `L` resolves to index `k`: to run from the jump it suffices to
run from the label if the condition holds in the current flags, and from the next directive
otherwise.
-/
theorem eventually_jcc [Host] {i k : Nat} {cc : CondCode} {L : Label} {post : @Post MachineState}
    {s : MachineData}
    (hi : Host.prog[i]? = some (jccTo cc L))
    (hk : Host.prog[k]? = some (.label L))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (h : Eventually (step1 Host.exe) post
      ⟨s, if cc.interp s.status then Host.addrOf k else Host.addrOf (i + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Effects.All]
  rw [label_eq_addrOf' hk hfirst]
  split <;> simp_all [Effects.All]

/-- K3, taken outcome. -/
theorem eventually_jcc_taken [Host] {i k : Nat} {cc : CondCode} {L : Label}
    {post : @Post MachineState} {s : MachineData}
    (hi : Host.prog[i]? = some (jccTo cc L))
    (hk : Host.prog[k]? = some (.label L))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (hcc : cc.interp s.status = true)
    (h : Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ :=
  eventually_jcc hi hk hfirst (by simp only [hcc, ↓reduceIte]; exact h)

/-- K3, fall-through outcome. No hypothesis about the label is needed: it may even be undefined. -/
theorem eventually_jcc_fallthrough [Host] {i : Nat} {cc : CondCode} {L : Label}
    {post : @Post MachineState} {s : MachineData}
    (hi : Host.prog[i]? = some (jccTo cc L))
    (hcc : cc.interp s.status = false)
    (h : Eventually (step1 Host.exe) post ⟨s, Host.addrOf (i + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Effects.All, hcc]
  exact h

/-! ## K4: call and return, with the stack described in separation logic -/

theorem store_All_of_sep (s : MachineData) (addr : BitVec 64) (w : Width) (v : w.type)
    (ret : MachineData → Effects) (post : MachineState → Prop) (bs : List UInt8)
    (R : DataMem → Prop) (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R) (h_len : bs.length = w.bytes) :
    (MachineData.store s addr v ret).All post ↔
      (ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }).All post := by
  have h := store_sep s addr w v ret bs R h_mem h_len
  simp only at h
  rw [h, Effects.All_require_write_access]

theorem load_All_of_sep (s : MachineData) (addr : BitVec 64) (w : Width)
    (ret : w.type → MachineData → Effects) (post : MachineState → Prop) (bs : List UInt8)
    (R : DataMem → Prop) (h_mem : s.dmem =⋆ Eq (bs.At addr) ⋆ R) (h_len : bs.length = w.bytes) :
    (MachineData.load s addr w ret).All post ↔
      (ret (.ofInt w.bits (Int.ofBytes bs)) s).All post := by
  rw [load_sep s addr w ret bs R h_mem h_len, Effects.All_require_read_access]

/--
K4, call. `call L` at index `i`, where `L` resolves to index `k`. The 8 bytes below the stack
pointer must be owned (`old`). Afterwards they hold the return address `Host.addrOf (i + 1)`, the
stack pointer is 8 lower, the frame `R` is preserved, and control is at the label.
-/
theorem eventually_call [Host] {i k : Nat} {L : Label} {post : @Post MachineState}
    {s : MachineData} {old : List UInt8} {R : DataMem → Prop}
    (hi : Host.prog[i]? = some (callTo L))
    (hk : Host.prog[k]? = some (.label L))
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (hlen : old.length = 8)
    (hmem : s.dmem =⋆ Eq (old.At (s.regs.rsp.toBitVec - 8#64)) ⋆ R)
    (h : ∀ m' : DataMem,
      (m' =⋆ Eq ((Host.addrOf (i + 1)).toUInt64.At (s.regs.rsp.toBitVec - 8#64)) ⋆ R) →
      Eventually (step1 Host.exe) post
        ⟨{ s with regs := { s.regs with rsp := s.regs.rsp - 8 }, dmem := m' }, Host.addrOf k⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All]
  refine (store_All_of_sep _ _ .W64 _ _ _ old R ?_ hlen).mpr ?_
  · exact hmem
  rw [label_eq_addrOf' hk hfirst, Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel]
  exact h _ (Mem.storeInt_sep _ 8 old R s.dmem ⟨hmem, hlen⟩ _)

/--
K4, return. `ret` at index `i`. The 8 bytes at the stack pointer hold a return address `ra`.
Afterwards the stack pointer is 8 higher, memory is unchanged, and control is at `ra`.
-/
theorem eventually_ret [Host] {i : Nat} {post : @Post MachineState} {s : MachineData}
    {ra : Int64} {R : DataMem → Prop}
    (hi : Host.prog[i]? = some retD)
    (hmem : s.dmem =⋆ Eq (ra.toUInt64.At s.regs.rsp.toBitVec) ⋆ R)
    (h : Eventually (step1 Host.exe) post
      ⟨{ s with regs := { s.regs with rsp := s.regs.rsp + 8 } }, ra⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, Effects.All]
  refine (load_All_of_sep _ _ .W64 _ _ ra.toUInt64.toBytes R ?_ (UInt64.toBytes_length _)).mpr ?_
  · exact hmem
  have hra : BitVec.ofInt 64 (Int.ofBytes ra.toUInt64.toBytes) = ra.toBitVec :=
    BitVec.ofInt_ofBytes_toBytes 64 8 rfl ra.toBitVec
  simp only [Effects.All]
  rw [hra, Int64.ofBitVec_toBitVec]
  exact h

/-! ## K5: a generic compiled counting loop -/

/-- The machine data after `dec %r` for a 64-bit register `r`. -/
def decState (s : MachineData) (r : Reg64) : MachineData :=
  let a := s.regs.get64 r
  let v := a - 1
  { s with
    regs := s.regs.set64 r v
    status := .from_result v {
      cf := s.status.cf
      af := (v.take 4).unsigned != (a.take 4).unsigned - 1
      of := v.signed != a.signed - 1 } }

theorem toNat_sub_one (a : BitVec 64) (n : Nat) (h : a.toNat = n + 1) : (a - 1#64).toNat = n := by
  have := a.isLt
  rw [BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  omega

theorem get_low64 (regs : Reg64s) (r : Reg64) : regs.get (.low r .W64) = regs.get64 r := by
  simp [Reg64s.get, BitVec.take, BitVec.drop, Reg.base, Reg.offset]

theorem get64_set64_same (regs : Reg64s) (r : Reg64) (v : BitVec 64) :
    (regs.set64 r v).get64 r = v := by
  cases r <;> rfl

theorem set64_set64_same (regs : Reg64s) (r : Reg64) (v v' : BitVec 64) :
    (regs.set64 r v).set64 r v' = regs.set64 r v' := by
  cases r <;> rfl

/-- `dec %r` (64-bit register) at index `i` falls through with `decState`. -/
theorem eventually_dec64 [Host] {i : Nat} {r : Reg64} {post : @Post MachineState}
    {s : MachineData} (hi : Host.prog[i]? = some (dec64 r))
    (h : Eventually (step1 Host.exe) post ⟨decState s r, Host.addrOf (i + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  refine eventually_of_interp_cps hi ?_
  simp only [Directive.interp, Instr.interp, Operation.interp, RegOrMem.interp, MachineData.set,
    MachineData.setReg, Effects.All, get_low64]
  exact h

/-- The loop `L: dec %r; jnz L`. -/
def countdown (L : Label) (r : Reg64) : Program := [.label L, dec64 r, jccTo .nz L]

section ParserChecks
open Kraken.X64.Parser
example : parse("L:
  dec %rcx
  jnz L") = countdown "L" .rcx := rfl
end ParserChecks

/-- The machine data after the loop: `r` is 0, the flags are those of the last `dec`. -/
def countdownFinal (s : MachineData) (r : Reg64) : MachineData :=
  { s with
    regs := s.regs.set64 r 0
    status := { cf := s.status.cf, pf := true, af := false, zf := true, sf := false, of := false } }

theorem decState_of_one (s : MachineData) (r : Reg64) (h : s.regs.get64 r = 1#64) :
    decState s r = countdownFinal s r := by
  simp only [decState, countdownFinal, h]
  rfl

/--
K5 in continuation-passing form. The loop `L: dec %r; jnz L` at any position `k` of any host
program, provided this is the first `L` in the host program: from a state where `r` holds `n + 1`,
to reach `post` it suffices to reach it from the fall-through address with `r = 0`.
-/
theorem eventually_countdown [Host] {L : Label} {r : Reg64} {k : Nat}
    (hk : (countdown L r).IsInfixAt Host.prog k)
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    {post : @Post MachineState} (n : Nat) :
    ∀ s : MachineData, (s.regs.get64 r).toNat = n + 1 →
      Eventually (step1 Host.exe) post ⟨countdownFinal s r, Host.addrOf (k + 3)⟩ →
      Eventually (step1 Host.exe) post ⟨s, Host.addrOf k⟩ := by
  have h0 : Host.prog[k]? = some (.label L) := by
    simpa [countdown] using List.isInfixAt_iff_getElem?.mp hk 0 (by simp [countdown])
  have h1 : Host.prog[k + 1]? = some (dec64 r) := by
    simpa [countdown] using List.isInfixAt_iff_getElem?.mp hk 1 (by simp [countdown])
  have h2 : Host.prog[k + 2]? = some (jccTo .nz L) := by
    simpa [countdown] using List.isInfixAt_iff_getElem?.mp hk 2 (by simp [countdown])
  induction n with
  | zero =>
    intro s hs h
    have ha : s.regs.get64 r = 1#64 := BitVec.eq_of_toNat_eq (by simpa using hs)
    apply eventually_label h0
    apply eventually_dec64 h1
    rw [decState_of_one s r ha]
    exact eventually_jcc_fallthrough h2 rfl h
  | succ n ih =>
    intro s hs h
    have hv : (s.regs.get64 r - 1#64).toNat = n + 1 := toNat_sub_one _ _ hs
    apply eventually_label h0
    apply eventually_dec64 h1
    apply eventually_jcc_taken h2 h0 hfirst
    · have hne : s.regs.get64 r - 1#64 ≠ 0#64 := fun h0 => by rw [h0] at hv; simp at hv
      simp [CondCode.interp, decState, StatusFlags.from_result, hne]
    · apply ih (decState s r)
      · simpa [decState, get64_set64_same] using hv
      · have : countdownFinal (decState s r) r = countdownFinal s r := by
          simp [countdownFinal, decState, set64_set64_same, StatusFlags.from_result]
        rw [this]
        exact h

theorem countdownFinal_get64 (s : MachineData) (r : Reg64) :
    (countdownFinal s r).regs.get64 r = 0 :=
  get64_set64_same _ _ _

/--
K5. For every host, every position `k` of the loop `L: dec %r; jnz L` such that this is the first
`L` in the host program, and every `n > 0`: from a state where `r` holds `n`, execution eventually
reaches the fall-through address `Host.addrOf (k + 3)` with `r = 0`. More precisely the final
machine data is `countdownFinal s r`: all other registers, memory and the carry flag are unchanged.
-/
theorem countdown_spec [Host] (L : Label) (r : Reg64) (k : Nat)
    (hk : (countdown L r).IsInfixAt Host.prog k)
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (n : Nat) (hn : 0 < n) (s : MachineData) (hs : (s.regs.get64 r).toNat = n) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf (k + 3) ∧ st.data.regs.get64 r = 0 ∧
        st.data = countdownFinal s r)
      ⟨s, Host.addrOf k⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact eventually_countdown hk hfirst m s hs (.done _ ⟨rfl, countdownFinal_get64 s r, rfl⟩)

/--
K5 as a `Program.wp` fact. `Program.wp` quantifies over every occurrence of the fragment in the
host, so it needs a hypothesis that `Host` does not provide: before any occurrence of the fragment
there is no other definition of `L`.
-/
theorem countdown_wp [Host] (L : Label) (r : Reg64)
    (hfirst : ∀ k j, (countdown L r).IsInfixAt Host.prog k → j < k →
      Host.prog[j]? ≠ some (.label L))
    (s : MachineData) (hs : s.regs.get64 r ≠ 0)
    (Q : MachineData → Prop) (E : Int64 → MachineData → Prop) (hQ : Q (countdownFinal s r)) :
    Program.wp (countdown L r) Q E s := by
  intro k hk
  have hpos : (s.regs.get64 r).toNat ≠ 0 := fun h => hs (BitVec.eq_of_toNat_eq (by simpa using h))
  obtain ⟨m, hm⟩ : ∃ m, (s.regs.get64 r).toNat = m + 1 := ⟨(s.regs.get64 r).toNat - 1, by omega⟩
  exact eventually_countdown hk (fun j hj => hfirst k j hk hj) m s hm (.done _ (Or.inl ⟨rfl, hQ⟩))

/-! ## Side conditions: what `Host` already provides -/

/-- A direct jump is not inert, so under `Host` its size is positive. This is why K2 needs no
positive-size hypothesis (and `Host.eventually_of_interp` never asks for one). -/
theorem not_inert_jmpTo (L : Label) : ¬ (jmpTo L).Inert := by
  intro h
  have h' := (@h ⟨fun _ => 0⟩ {} ⟨0, 0⟩ (fun _ => .unimplemented "") (fun a s => .done ⟨s, a⟩)
    (fun _ => True)).mp
  simp [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp, Effects.All] at h'

theorem size_pos_of_jmp [Host] {i : Nat} {L : Label} (hi : Host.prog[i]? = some (jmpTo L)) :
    0 < Kraken.Layout.size Instr i :=
  Nat.pos_of_ne_zero fun hz => not_inert_jmpTo L (Host.inert_of_getElem? hi hz)

theorem exists_status (cc : CondCode) : ∃ st : StatusFlags, cc.interp st = true := by
  cases cc
  all_goals first
    | exact ⟨⟨false, false, false, false, false, false⟩, rfl⟩
    | exact ⟨⟨true, true, true, true, true, true⟩, rfl⟩
    | exact ⟨⟨false, false, false, false, true, false⟩, rfl⟩

/-- A conditional jump is not inert either (there are flags under which it jumps). -/
theorem not_inert_jccTo (cc : CondCode) (L : Label) : ¬ (jccTo cc L).Inert := by
  intro h
  obtain ⟨st, hst⟩ := exists_status cc
  have h' := (@h ⟨fun _ => 0⟩ { status := st } ⟨0, 0⟩ (fun _ => .unimplemented "")
    (fun a s => .done ⟨s, a⟩) (fun _ => True)).mp
  simp [Directive.interp, Instr.interp, Operation.interp, Effects.All, hst] at h'

theorem size_pos_of_jcc [Host] {i : Nat} {cc : CondCode} {L : Label}
    (hi : Host.prog[i]? = some (jccTo cc L)) : 0 < Kraken.Layout.size Instr i :=
  Nat.pos_of_ne_zero fun hz => not_inert_jccTo cc L (Host.inert_of_getElem? hi hz)

/-- Labels are inert, so a layout may give them size zero. -/
theorem inert_label (l : Label) : Directive.Inert (.label l) := fun _ _ _ _ _ => Iff.rfl

/-! ## K1 under global label uniqueness -/

/-- No label is defined twice in the host program. `Host` does not provide this. -/
def LabelsUnique [Host] : Prop :=
  ∀ (i j : Nat) (l : Label),
    Host.prog[i]? = some (.label l) → Host.prog[j]? = some (.label l) → i = j

theorem label_eq_addrOf_of_unique [Host] (hu : LabelsUnique) {l : Label} {k : Nat}
    (hk : Host.prog[k]? = some (.label l)) : Labels.label l = Host.addrOf k :=
  label_eq_addrOf' hk fun j hj h => Nat.ne_of_lt hj (hu j k l h hk)

/-! ## K4: `call L` to `L: ret` composes -/

/--
`call L` at index `i`, with `L: ret` at index `k`: control comes back to `Host.addrOf (i + 1)` with
all registers (including `rsp`) restored; the 8 bytes below the stack pointer now hold the return
address and the frame `R` is preserved.
-/
theorem eventually_call_ret [Host] {i k : Nat} {L : Label} {post : @Post MachineState}
    {s : MachineData} {old : List UInt8} {R : DataMem → Prop}
    (hi : Host.prog[i]? = some (callTo L))
    (hk : Host.prog[k]? = some (.label L))
    (hret : Host.prog[k + 1]? = some retD)
    (hfirst : ∀ j, j < k → Host.prog[j]? ≠ some (.label L))
    (hlen : old.length = 8)
    (hmem : s.dmem =⋆ Eq (old.At (s.regs.rsp.toBitVec - 8#64)) ⋆ R)
    (h : ∀ m' : DataMem,
      (m' =⋆ Eq ((Host.addrOf (i + 1)).toUInt64.At (s.regs.rsp.toBitVec - 8#64)) ⋆ R) →
      Eventually (step1 Host.exe) post ⟨{ s with dmem := m' }, Host.addrOf (i + 1)⟩) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf i⟩ := by
  apply eventually_call hi hk hfirst hlen hmem
  intro m' hm'
  apply eventually_label hk
  apply eventually_ret (ra := Host.addrOf (i + 1)) (R := R) hret
  · exact hm'
  · simpa only [UInt64.sub_add_cancel] using h m' hm'

/-! ## Beyond K5: the sequencing rules a compiler needs at the `Program.wp` level

`Kraken/X64/WP/Basic.lean` has `Program.wp_cons` and `Program.wp_mono` only.
-/

theorem wp_nil [Host] {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : Q s) : Program.wp [] Q E s :=
  fun _ _ => .done _ (Or.inl ⟨rfl, h⟩)

theorem wp_label [Host] {l : Label} {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    {s : MachineData} (h : Q s) : Program.wp [.label l] Q E s :=
  fun _ hk => eventually_label (isInfixAt_singleton.mp hk) (.done _ (Or.inl ⟨rfl, h⟩))

theorem wp_append [Host] {p q : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : Program.wp p (fun s' => Program.wp q Q E s') E s) : Program.wp (p ++ q) Q E s := by
  intro k hk
  obtain ⟨hp, hq⟩ := List.IsInfixAt.append hk
  refine eventually_trans _ _ _ _ (h k hp) ?_
  rintro ⟨s', a⟩ (⟨ha, hrun⟩ | hE)
  · dsimp only at ha hrun
    subst ha
    refine eventually_trans _ _ _ _ (hrun (k + p.length) hq) fun _ hb => Eventually.done _ ?_
    rcases hb with ⟨hend, hq'⟩ | hE
    · exact Or.inl ⟨by rw [hend, List.length_append, Nat.add_assoc], hq'⟩
    · exact Or.inr hE
  · exact Eventually.done _ (Or.inr hE)

/--
Function call at the `Program.wp` level. The callee is known through a host-level specification
that is quantified over the return address `ra`: started at its label with `ra` on the stack, it
eventually reaches `ra` in a state satisfying `Q`.
-/
theorem wp_call [Host] {L : Label} {kf : Nat} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData} {old : List UInt8} {R : DataMem → Prop}
    (hkf : Host.prog[kf]? = some (.label L))
    (hfirst : ∀ j, j < kf → Host.prog[j]? ≠ some (.label L))
    (hlen : old.length = 8)
    (hmem : s.dmem =⋆ Eq (old.At (s.regs.rsp.toBitVec - 8#64)) ⋆ R)
    (hcallee : ∀ (ra : Int64) (m' : DataMem),
      (m' =⋆ Eq (ra.toUInt64.At (s.regs.rsp.toBitVec - 8#64)) ⋆ R) →
      Eventually (step1 Host.exe) (fun st => st.pc = ra ∧ Q st.data)
        ⟨{ s with regs := { s.regs with rsp := s.regs.rsp - 8 }, dmem := m' }, Host.addrOf kf⟩) :
    Program.wp [callTo L] Q E s := by
  intro k hk
  apply eventually_call (isInfixAt_singleton.mp hk) hkf hfirst hlen hmem
  intro m' hm'
  refine eventually_weaken _ _ _ _ ?_ (hcallee (Host.addrOf (k + 1)) m' hm')
  rintro st ⟨hpc, hq⟩
  exact Or.inl ⟨hpc, hq⟩

/-! ## Beyond K5: a loop rule for an arbitrary body, at the `Program.wp` level -/

/-- `L: body; jcc L` for an arbitrary `body`. -/
def doWhile (L : Label) (body : Program) (cc : CondCode) : Program :=
  .label L :: (body ++ [jccTo cc L])

/--
Do-while rule. `inv n` is an invariant indexed by a measure `n` that decreases on every iteration.
The body is known only through its `Program.wp`. Needs: before any occurrence of the loop in the
host there is no other definition of `L`.
-/
theorem wp_doWhile [Host] {L : Label} {body : Program} {cc : CondCode}
    (hfirst : ∀ k j, (doWhile L body cc).IsInfixAt Host.prog k → j < k →
      Host.prog[j]? ≠ some (.label L))
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    (inv : Nat → MachineData → Prop)
    (hbody : ∀ n s, inv n s →
      Program.wp body (fun s' => if cc.interp s'.status then ∃ m, m < n ∧ inv m s' else Q s') E s)
    {n : Nat} {s : MachineData} (h : inv n s) :
    Program.wp (doWhile L body cc) Q E s := by
  intro k hk
  have h0 : Host.prog[k]? = some (.label L) := hk.cons.1
  obtain ⟨hb, hj⟩ := List.IsInfixAt.append hk.cons.2
  have hjcc : Host.prog[k + 1 + body.length]? = some (jccTo cc L) := isInfixAt_singleton.mp hj
  have hfirst' := fun j hj => hfirst k j hk hj
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    apply eventually_label h0
    refine eventually_trans _ _ _ _ (hbody n s h (k + 1) hb) ?_
    rintro ⟨s', a⟩ (⟨ha, hq⟩ | hE)
    · dsimp only at ha hq
      subst ha
      apply eventually_jcc hjcc h0 hfirst'
      cases hc : cc.interp s'.status with
      | true =>
        simp only [hc, ↓reduceIte] at hq ⊢
        obtain ⟨m, hm, hinv⟩ := hq
        exact ih m hm hinv
      | false =>
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at hq ⊢
        refine .done _ (Or.inl ⟨congrArg Host.addrOf ?_, hq⟩)
        simp [doWhile]
        omega
    · exact .done _ (Or.inr hE)

/-- `Program.wp` of the single instruction `dec %r`. -/
theorem wp_dec64 [Host] {r : Reg64} {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    {s : MachineData} (h : Q (decState s r)) : Program.wp [dec64 r] Q E s := by
  intro k hk
  exact eventually_dec64 (isInfixAt_singleton.mp hk) (.done _ (Or.inl ⟨rfl, h⟩))

/-- K5 again, this time derived from the generic rule `wp_doWhile`. -/
theorem countdown_wp' [Host] (L : Label) (r : Reg64)
    (hfirst : ∀ k j, (countdown L r).IsInfixAt Host.prog k → j < k →
      Host.prog[j]? ≠ some (.label L))
    (s : MachineData) (hs : s.regs.get64 r ≠ 0)
    (Q : MachineData → Prop) (E : Int64 → MachineData → Prop) (hQ : Q (countdownFinal s r)) :
    Program.wp (countdown L r) Q E s := by
  have hpos : (s.regs.get64 r).toNat ≠ 0 := fun h => hs (BitVec.eq_of_toNat_eq (by simpa using h))
  refine wp_doWhile (body := [dec64 r]) (cc := .nz) hfirst
    (fun n s' => (s'.regs.get64 r).toNat = n + 1 ∧ countdownFinal s' r = countdownFinal s r) ?_
    (n := (s.regs.get64 r).toNat - 1) ⟨by omega, rfl⟩
  intro n s' ⟨hn, hfin⟩
  apply wp_dec64
  cases n with
  | zero =>
    have ha : s'.regs.get64 r = 1#64 := BitVec.eq_of_toNat_eq (by simpa using hn)
    rw [decState_of_one s' r ha, hfin]
    exact hQ
  | succ n =>
    have hv : (s'.regs.get64 r - 1#64).toNat = n + 1 := toNat_sub_one _ _ hn
    have hne : s'.regs.get64 r - 1#64 ≠ 0#64 := fun h0 => by rw [h0] at hv; simp at hv
    have hcc : CondCode.nz.interp (decState s' r).status = true := by
      simp [CondCode.interp, decState, StatusFlags.from_result, hne]
    simp only [hcc, ↓reduceIte]
    refine ⟨n, Nat.lt_succ_self n, ?_, ?_⟩
    · simpa [decState, get64_set64_same] using hv
    · rw [← hfin]
      simp [countdownFinal, decState, set64_set64_same, StatusFlags.from_result]

/-! ## Beyond K5: if-then-else for arbitrary branches (forward `jcc`, `jmp`, two labels) -/

/-- `jcc Lelse; t; jmp Lend; Lelse: e; Lend:` for arbitrary `t` and `e`. -/
def ifThenElse (cc : CondCode) (Lelse Lend : Label) (t e : Program) : Program :=
  jccTo cc Lelse :: (t ++ (jmpTo Lend :: .label Lelse :: (e ++ [.label Lend])))

/--
If-then-else rule: `e` runs if `cc` holds on entry, `t` otherwise. The branches are known only
through their `Program.wp`. Needs: for every occurrence in the host, neither label is defined
before its definition in this occurrence.
-/
theorem wp_ifThenElse [Host] {cc : CondCode} {Lelse Lend : Label} {t e : Program}
    (hfirstElse : ∀ k j, (ifThenElse cc Lelse Lend t e).IsInfixAt Host.prog k →
      j < k + 1 + t.length + 1 → Host.prog[j]? ≠ some (.label Lelse))
    (hfirstEnd : ∀ k j, (ifThenElse cc Lelse Lend t e).IsInfixAt Host.prog k →
      j < k + 1 + t.length + 1 + 1 + e.length → Host.prog[j]? ≠ some (.label Lend))
    {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    (ht : cc.interp s.status = false → Program.wp t Q E s)
    (he : cc.interp s.status = true → Program.wp e Q E s) :
    Program.wp (ifThenElse cc Lelse Lend t e) Q E s := by
  intro k hk
  have h_jcc := hk.cons.1
  obtain ⟨ht_at, h2⟩ := List.IsInfixAt.append hk.cons.2
  have h_jmp := h2.cons.1
  have h_lelse := h2.cons.2.cons.1
  obtain ⟨he_at, h5⟩ := List.IsInfixAt.append h2.cons.2.cons.2
  have h_lend := isInfixAt_singleton.mp h5
  have hlen : k + (ifThenElse cc Lelse Lend t e).length
      = k + 1 + t.length + 1 + 1 + e.length + 1 := by
    simp [ifThenElse]
    omega
  rw [hlen]
  apply eventually_jcc h_jcc h_lelse (fun j hj => hfirstElse k j hk hj)
  cases hc : cc.interp s.status with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine eventually_trans _ _ _ _ (ht hc (k + 1) ht_at) ?_
    rintro ⟨s', a⟩ (⟨ha, hq⟩ | hE)
    · dsimp only at ha hq
      subst ha
      apply eventually_jmp h_jmp h_lend (fun j hj => hfirstEnd k j hk hj)
      apply eventually_label h_lend
      exact .done _ (Or.inl ⟨rfl, hq⟩)
    · exact .done _ (Or.inr hE)
  | true =>
    simp only [↓reduceIte]
    apply eventually_label h_lelse
    refine eventually_trans _ _ _ _ (he hc (k + 1 + t.length + 1 + 1) he_at) ?_
    rintro ⟨s', a⟩ (⟨ha, hq⟩ | hE)
    · dsimp only at ha hq
      subst ha
      apply eventually_label h_lend
      exact .done _ (Or.inl ⟨rfl, hq⟩)
    · exact .done _ (Or.inr hE)

/-! ## The structured rules under global label uniqueness

One host-level hypothesis, `LabelsUnique`, discharges all the "first definition" side conditions.
-/

theorem wp_doWhile_of_unique [Host] (hu : LabelsUnique) {L : Label} {body : Program}
    {cc : CondCode} {Q : MachineData → Prop} {E : Int64 → MachineData → Prop}
    (inv : Nat → MachineData → Prop)
    (hbody : ∀ n s, inv n s →
      Program.wp body (fun s' => if cc.interp s'.status then ∃ m, m < n ∧ inv m s' else Q s') E s)
    {n : Nat} {s : MachineData} (h : inv n s) :
    Program.wp (doWhile L body cc) Q E s :=
  wp_doWhile (fun k j hk hj hl => Nat.ne_of_lt hj (hu j k L hl hk.cons.1)) inv hbody h

theorem wp_ifThenElse_of_unique [Host] (hu : LabelsUnique) {cc : CondCode} {Lelse Lend : Label}
    {t e : Program} {Q : MachineData → Prop} {E : Int64 → MachineData → Prop} {s : MachineData}
    (ht : cc.interp s.status = false → Program.wp t Q E s)
    (he : cc.interp s.status = true → Program.wp e Q E s) :
    Program.wp (ifThenElse cc Lelse Lend t e) Q E s := by
  refine wp_ifThenElse (fun k j hk hj hl => ?_) (fun k j hk hj hl => ?_) ht he
  · have h2 := (List.IsInfixAt.append hk.cons.2).2
    exact Nat.ne_of_lt hj (hu j _ Lelse hl h2.cons.2.cons.1)
  · have h2 := (List.IsInfixAt.append hk.cons.2).2
    have h5 := (List.IsInfixAt.append h2.cons.2.cons.2).2
    exact Nat.ne_of_lt hj (hu j _ Lend hl (isInfixAt_singleton.mp h5))

/-! ## Non-vacuity: a concrete `Host` containing the loop -/

theorem sizeBefore_le_total (e : Executable) (j : Nat) :
    e.sizeBefore j ≤ e.sizeBefore e.program.length := by
  rcases Nat.le_total j e.program.length with h | h
  · exact e.sizeBefore_mono h
  · simp [Kraken.Executable.sizeBefore, List.take_of_length_le h]

/-- If the whole executable is smaller than `2 ^ 64` bytes, addresses determine offsets. -/
theorem addr_determines_offset_of_lt (e : Executable)
    (hsmall : e.sizeBefore e.program.length < 2 ^ 64) (j k : Nat)
    (h : e.addrOf j = e.addrOf k) : e.sizeBefore j = e.sizeBefore k := by
  have hj := sizeBefore_le_total e j
  have hk := sizeBefore_le_total e k
  unfold Kraken.Executable.addrOf at h
  have h' : Int64.ofNat (e.sizeBefore j) = Int64.ofNat (e.sizeBefore k) :=
    (Int64.add_right_inj _).mp h
  have h'' := congrArg (fun x => x.toBitVec.toNat) h'
  simp only [Int64.toBitVec_ofNat', BitVec.toNat_ofNat] at h''
  omega

namespace Demo

def prog : Program := countdown "L" .rcx ++ [retD]

@[instance_reducible] def layout : Layout := { start := 0x1000, size := fun i => if i = 0 then 0 else 2 }

@[reducible] def host : Host where
  prog := prog
  layout := layout
  zero_inert := by
    intro i d hd hz
    have hz' : (if i = 0 then 0 else 2) = 0 := hz
    have hi : i = 0 := by
      by_cases hne : i = 0
      · exact hne
      · simp [hne] at hz'
    subst hi
    simp only [prog, countdown, List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at hd
    subst hd
    exact @inert_label "L"
  addr_determines_offset := addr_determines_offset_of_lt _ (by decide)

attribute [local instance] host in
/-- K5 instantiated on a concrete host: the hypotheses of `countdown_spec` are satisfiable. -/
theorem demo (s : MachineData) (n : Nat) (hn : 0 < n) (hs : s.regs.rcx.toNat = n) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = Host.addrOf 3 ∧ st.data.regs.get64 .rcx = 0 ∧
        st.data = countdownFinal s .rcx)
      ⟨s, Host.addrOf 0⟩ :=
  countdown_spec "L" .rcx 0 ⟨[retD], rfl⟩ (fun j hj => absurd hj (Nat.not_lt_zero j)) n hn s hs

end Demo

/-! ## The first-definition hypothesis of K2 is necessary: a machine-checked counterexample -/

/-- One step at a positive-size directive is exactly the interpretation of that directive
(the converse direction of `Host.eventually_of_interp`, needed to refute an `Eventually`). -/
theorem step1_iff_interp [Host] {k : Nat} {d : Directive} (hd : Host.prog[k]? = some d)
    (hz : 0 < Kraken.Layout.size Instr k) {post : @Post MachineState} {s : MachineData} :
    step1 Host.exe ⟨s, Host.addrOf k⟩ post ↔
      (d.interp s ⟨Host.addrOf k, Host.addrOf (k + 1)⟩
        (fun s' => .done ⟨s', Host.addrOf (k + 1)⟩) (fun a s' => .done ⟨s', a⟩)).All post := by
  have hd' : Host.exe.program[k]? =
      some { directive := d, size := Kraken.Layout.size Instr k : Kraken.Sized Directive } := by
    rw [Host.exe_getElem?, hd]
    rfl
  obtain ⟨pre, hat, hpre⟩ := Host.directivesAtAddress_addrOf hd' hz
  have hinert : ∀ c ∈ pre, c.size = 0 ∧ c.directive.Inert := fun c hc =>
    ⟨hpre c hc, Host.inert_of_size_zero (hpre c hc ▸
      Kraken.Executable.mem_of_mem_directivesAtAddress (hat ▸ List.mem_append_left _ hc))⟩
  rw [Host.addrOf_succ hd]
  unfold step1 Executable.step
  change (Directives.interp (Host.exe.directivesAtAddress (Host.addrOf k)) s (Host.addrOf k)
    _).All post ↔ _
  rw [hat]
  exact Directives.interp_inert_append hinert _ _ _ _

namespace Counter

/-- `L` is defined twice. The jump at index 1 sits between the two definitions. -/
def prog : Program := [.label "L", jmpTo "L", .label "L"]

@[instance_reducible] def layout : Layout :=
  { start := 0x1000, size := fun i => if i = 1 then 2 else 0 }

@[reducible] def host : Host where
  prog := prog
  layout := layout
  zero_inert := by
    intro i d hd hz
    have hz' : (if i = 1 then 2 else 0) = 0 := hz
    rcases i with _ | _ | _ | i
    · simp only [prog, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      exact @inert_label "L"
    · simp at hz'
    · simp only [prog, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      exact @inert_label "L"
    · simp [prog] at hd
  addr_determines_offset := addr_determines_offset_of_lt _ (by decide)

attribute [local instance] host in
/--
K2 without its first-definition hypothesis is false. In this host, index 1 is `jmp L` and index 2
is `.label L`, but not the first one. From the label at index 2 the postcondition "pc is at index 2"
holds at once; from the jump it is never reached, because the jump goes to the first `L`, which has
the same address as the jump itself.
-/
theorem jmp_needs_first_definition :
    Host.prog[1]? = some (jmpTo "L") ∧ Host.prog[2]? = some (.label "L") ∧
    ∃ (post : @Post MachineState) (s : MachineData),
      Eventually (step1 Host.exe) post ⟨s, Host.addrOf 2⟩ ∧
      ¬ Eventually (step1 Host.exe) post ⟨s, Host.addrOf 1⟩ := by
  refine ⟨rfl, rfl, fun st => st.pc = Host.addrOf 2, {}, .done _ rfl, ?_⟩
  have h01 : Host.addrOf 0 = Host.addrOf 1 := by decide
  have h12 : Host.addrOf 1 ≠ Host.addrOf 2 := by decide
  have hlab : Labels.label "L" = Host.addrOf 0 :=
    label_eq_addrOf' (k := 0) rfl (fun j hj => absurd hj (Nat.not_lt_zero j))
  have key : ∀ st, Eventually (step1 Host.exe) (fun st => st.pc = Host.addrOf 2) st →
      st.pc = Host.addrOf 1 → False := by
    intro st h
    induction h with
    | done st hp => exact fun hpc => h12 (hpc ▸ hp)
    | step st mid_p ht _ ih =>
      intro hpc
      obtain ⟨data, pc⟩ := st
      dsimp only at hpc
      subst hpc
      have hstep := (step1_iff_interp (k := 1) (d := jmpTo "L") rfl (by decide)).mp ht
      simp only [Directive.interp, Instr.interp, Operation.interp, RelRegOrMem.interp,
        ConstExpr.interp, Effects.All] at hstep
      rw [hlab, Int64.ofBitVec_toBitVec, Int64.add_comm, Int64.sub_add_cancel] at hstep
      exact ih _ hstep h01
  exact fun h => key _ h rfl

end Counter

end SpikeK

#print axioms SpikeK.label_eq_addrOf
#print axioms SpikeK.label_eq_addrOf'
#print axioms SpikeK.eventually_of_interp_cps
#print axioms SpikeK.eventually_label
#print axioms SpikeK.eventually_jmp
#print axioms SpikeK.eventually_jcc
#print axioms SpikeK.eventually_jcc_taken
#print axioms SpikeK.eventually_jcc_fallthrough
#print axioms SpikeK.eventually_call
#print axioms SpikeK.eventually_ret
#print axioms SpikeK.eventually_call_ret
#print axioms SpikeK.eventually_dec64
#print axioms SpikeK.eventually_countdown
#print axioms SpikeK.countdown_spec
#print axioms SpikeK.countdown_wp
#print axioms SpikeK.size_pos_of_jmp
#print axioms SpikeK.label_eq_addrOf_of_unique
#print axioms SpikeK.Demo.demo
#print axioms SpikeK.wp_doWhile
#print axioms SpikeK.countdown_wp'
#print axioms SpikeK.wp_ifThenElse
#print axioms SpikeK.wp_doWhile_of_unique
#print axioms SpikeK.wp_ifThenElse_of_unique
#print axioms SpikeK.size_pos_of_jcc
#print axioms SpikeK.wp_nil
#print axioms SpikeK.wp_label
#print axioms SpikeK.wp_append
#print axioms SpikeK.wp_call
#print axioms SpikeK.step1_iff_interp
#print axioms SpikeK.Counter.jmp_needs_first_definition
