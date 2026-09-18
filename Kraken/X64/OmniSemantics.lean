/-
Kraken - Proof Tactics

Core tactics and theorems for stepping through assembly proofs.
Compatible with Lean 4.22.0+.

For semantics, see Kraken/Semantics.lean.
For advanced tactics (SymM), see kraken-experimental/KrakenExp/Tactics.lean.
-/

import Kraken.X64.Semantics

-- PROOF INFRASTRUCTURE

abbrev Post {State : Type} := State → Prop

def Effects.All (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ _ cont => (cont ()).All post
  | .require_write_access _ _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

theorem MachineData.load_mono {s : MachineData} {addr : BitVec 64} {w : Width}
    {ret₁ ret₂ : w.type → MachineData → Effects} {post₁ post₂ : MachineState → Prop}
    (hret : ∀ v s', (ret₁ v s').All post₁ → (ret₂ v s').All post₂)
    (h : (s.load addr w ret₁).All post₁) :
    (s.load addr w ret₂).All post₂ := by
  dsimp [MachineData.load, Effects.All] at *
  split at h
  · exact hret _ _ h
  · contradiction

theorem MachineData.loadAvx_mono {s : MachineData} {addr : BitVec 64} {w : AvxWidth}
    {ret₁ ret₂ : w.type → MachineData → Effects} {post₁ post₂ : MachineState → Prop}
    (hret : ∀ v s', (ret₁ v s').All post₁ → (ret₂ v s').All post₂)
    (h : (s.loadAvx addr w ret₁).All post₁) :
    (s.loadAvx addr w ret₂).All post₂ := by
  dsimp [MachineData.loadAvx, Effects.All] at *
  split at h
  · exact hret _ _ h
  · contradiction

theorem MachineData.store_mono {s : MachineData} {addr : BitVec 64} {w : Width} {v : w.type}
    {ret₁ ret₂ : MachineData → Effects} {post₁ post₂ : MachineState → Prop}
    (hret : ∀ s', (ret₁ s').All post₁ → (ret₂ s').All post₂)
    (h : (s.store addr v ret₁).All post₁) :
    (s.store addr v ret₂).All post₂ := by
  dsimp [MachineData.store, Effects.All] at *
  split at h
  · exact hret _ h
  · contradiction

theorem MachineData.storeAvx_mono {s : MachineData} {addr : BitVec 64} {w : AvxWidth} {v : w.type}
    {ret₁ ret₂ : MachineData → Effects} {post₁ post₂ : MachineState → Prop}
    (hret : ∀ s', (ret₁ s').All post₁ → (ret₂ s').All post₂)
    (h : (s.storeAvx addr v ret₁).All post₁) :
    (s.storeAvx addr v ret₂).All post₂ := by
  dsimp [MachineData.storeAvx, Effects.All] at *
  split at h
  · exact hret _ h
  · contradiction

theorem Reg.interp_mono {w : Width}
    (r : Reg w) (s : MachineData) (p : Std.Rco Int64)
    {ret₁ ret₂ : w.type → MachineData → Effects} {post₁ post₂ : MachineState → Prop}
    (hret : ∀ v s', (ret₁ v s').All post₁ → (ret₂ v s').All post₂)
    (h : (r.interp s p ret₁).All post₁) :
    (r.interp s p ret₂).All post₂ :=
  hret _ _ h

theorem RegOrMem.interp_mono {w : Width} [Labels] [AddressSize]
    (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64)
    {ret₁ ret₂ : w.type → MachineData → Effects} {post₁ post₂ : MachineState → Prop}
    (hret : ∀ v s', (ret₁ v s').All post₁ → (ret₂ v s').All post₂)
    (h : (o.interp s p ret₁).All post₁) :
    (o.interp s p ret₂).All post₂ := by
  cases o with
  | reg r => exact hret _ _ h
  | mem a => exact MachineData.load_mono hret h

theorem AvxRegOrMem.interp_mono {w : AvxWidth} [Labels] [AddressSize]
    (o : AvxRegOrMem w) (s : MachineData) (p : Std.Rco Int64)
    {ret₁ ret₂ : w.type → MachineData → Effects} {post₁ post₂ : MachineState → Prop}
    (hret : ∀ v s', (ret₁ v s').All post₁ → (ret₂ v s').All post₂)
    (h : (o.interp s p ret₁).All post₁) :
    (o.interp s p ret₂).All post₂ := by
  cases o with
  | avx r => exact hret _ _ h
  | mem a => exact MachineData.loadAvx_mono hret h

theorem Operand.interp_mono {w : Width} [Labels] [AddressSize]
    (o : Operand w) (s : MachineData) (p : Std.Rco Int64)
    {ret₁ ret₂ : w.type → MachineData → Effects} {post₁ post₂ : MachineState → Prop}
    (hret : ∀ v s', (ret₁ v s').All post₁ → (ret₂ v s').All post₂)
    (h : (o.interp s p ret₁).All post₁) :
    (o.interp s p ret₂).All post₂ := by
  cases o with
  | regOrMem rm => exact RegOrMem.interp_mono rm s p hret h
  | imm i => exact hret _ _ h

theorem RelRegOrMem.interp_mono [Labels] [AddressSize]
    (o : RelRegOrMem) (s : MachineData) (p : Std.Rco Int64)
    {ret₁ ret₂ : BitVec 64 → MachineData → Effects} {post₁ post₂ : MachineState → Prop}
    (hret : ∀ v s', (ret₁ v s').All post₁ → (ret₂ v s').All post₂)
    (h : (o.interp s p ret₁).All post₁) :
    (o.interp s p ret₂).All post₂ := by
  cases o with
  | rel c => exact hret _ _ h
  | reg r => exact hret _ _ h
  | mem a => exact MachineData.load_mono hret h

theorem MachineData.set_mono {w : Width} [Labels] [AddressSize]
    (s : MachineData) (d : Dst w) (v : w.type) (p : Std.Rco Int64)
    {ret₁ ret₂ : MachineData → Effects} {post₁ post₂ : MachineState → Prop}
    (hret : ∀ s', (ret₁ s').All post₁ → (ret₂ s').All post₂)
    (h : (s.set d v p ret₁).All post₁) :
    (s.set d v p ret₂).All post₂ := by
  cases d with
  | reg r => exact hret _ h
  | mem a => exact MachineData.store_mono hret h

theorem MachineData.setAvx_mono {aw : AvxWidth} [Labels] [AddressSize]
    (s : MachineData) (d : AvxDst aw) (v : aw.type) (p : Std.Rco Int64)
    {ret₁ ret₂ : MachineData → Effects} {post₁ post₂ : MachineState → Prop}
    (hret : ∀ s', (ret₁ s').All post₁ → (ret₂ s').All post₂)
    (h : (s.setAvx d v p ret₁).All post₁) :
    (s.setAvx d v p ret₂).All post₂ := by
  cases d with
  | avx r => exact hret _ h
  | mem a => exact MachineData.storeAvx_mono hret h

theorem MachineData.setAvxLegacy_mono {w : AvxWidth} [Labels] [AddressSize]
    (s : MachineData) (d : AvxDst w) (v : w.type) (p : Std.Rco Int64)
    {ret₁ ret₂ : MachineData → Effects} {post₁ post₂ : MachineState → Prop}
    (hret : ∀ s', (ret₁ s').All post₁ → (ret₂ s').All post₂)
    (h : (s.setAvxLegacy d v p ret₁).All post₁) :
    (s.setAvxLegacy d v p ret₂).All post₂ := by
  cases d with
  | avx r => exact hret _ h
  | mem a => exact MachineData.storeAvx_mono hret h

theorem AvxOperation.interp_mono [Labels] [AddressSize] {w : AvxWidth}
    (i : AvxOperation w) (p : Std.Rco Int64) (s : MachineData)
    {next₁ next₂ : MachineData → Effects} {post₁ post₂ : MachineState → Prop}
    (hnext : ∀ s', (next₁ s').All post₁ → (next₂ s').All post₂)
    (h : (AvxOperation.interp i p s next₁).All post₁) :
    (AvxOperation.interp i p s next₂).All post₂ := by
  cases i with
  | movups dst src =>
    exact AvxRegOrMem.interp_mono src s p (fun val s' => MachineData.setAvxLegacy_mono s' dst val p hnext) h
  | vmovups dst src =>
    exact AvxRegOrMem.interp_mono src s p (fun val s' => MachineData.setAvx_mono s' dst val p hnext) h

set_option maxHeartbeats 2000000 in
theorem Operation.interp_mono [Labels] [AddressSize] {w : Width}
    (i : Operation w) (p : Std.Rco Int64) (s : MachineData)
    {next₁ next₂ : MachineData → Effects}
    {jmp₁ jmp₂ : Int64 → MachineData → Effects}
    {post₁ post₂ : MachineState → Prop}
    (hnext : ∀ s', (next₁ s').All post₁ → (next₂ s').All post₂)
    (hjmp : ∀ pc' s', (jmp₁ pc' s').All post₁ → (jmp₂ pc' s').All post₂)
    (h : (Operation.interp i p s next₁ jmp₁).All post₁) :
    (Operation.interp i p s next₂ jmp₂).All post₂ := by
  dsimp [Operation.interp] at *
  cases i with
  | mov dst src =>
    exact Operand.interp_mono src s p (fun val s' => MachineData.set_mono s' dst val p hnext) h
  | movsx dst src =>
    exact RegOrMem.interp_mono src s p (fun val s' => MachineData.set_mono s' dst _ p hnext) h
  | movzx dst src =>
    exact RegOrMem.interp_mono src s p (fun val s' => MachineData.set_mono s' dst _ p hnext) h
  | push src =>
    exact Operand.interp_mono src s p (fun v s' => MachineData.store_mono hnext) h
  | pop dst =>
    exact MachineData.load_mono (fun val s' => MachineData.set_mono _ dst val p hnext) h
  | setcc cc dst =>
    exact MachineData.set_mono s dst _ p hnext h
  | cmovcc cc dst src =>
    exact RegOrMem.interp_mono src s p (fun src' s' => hnext _) h
  | lea dst src =>
    exact hnext _ h
  | add dst src =>
    exact Operand.interp_mono src s p (fun a s' => RegOrMem.interp_mono dst s' p (fun b s'' => MachineData.set_mono _ dst _ p hnext)) h
  | adc dst src =>
    exact Operand.interp_mono src s p (fun a s' => RegOrMem.interp_mono dst s' p (fun b s'' => MachineData.set_mono _ dst _ p hnext)) h
  | adcx dst src =>
    exact RegOrMem.interp_mono src s p (fun a s' => Reg.interp_mono dst s' p (fun b s'' => hnext _)) h
  | adox dst src =>
    exact RegOrMem.interp_mono src s p (fun a s' => Reg.interp_mono dst s' p (fun b s'' => hnext _)) h
  | inc dst =>
    exact RegOrMem.interp_mono dst s p (fun a s' => MachineData.set_mono _ dst _ p hnext) h
  | dec dst =>
    exact RegOrMem.interp_mono dst s p (fun a s' => MachineData.set_mono _ dst _ p hnext) h
  | neg dst =>
    exact RegOrMem.interp_mono dst s p (fun a s' => MachineData.set_mono _ dst _ p hnext) h
  | sub dst src =>
    exact Operand.interp_mono src s p (fun a s' => RegOrMem.interp_mono dst s' p (fun b s'' => MachineData.set_mono _ dst _ p hnext)) h
  | sbb dst src =>
    exact Operand.interp_mono src s p (fun a s' => RegOrMem.interp_mono dst s' p (fun b s'' => MachineData.set_mono _ dst _ p hnext)) h
  | cmp a b =>
    exact RegOrMem.interp_mono a s p (fun a' s' => Operand.interp_mono b s' p (fun b' s'' => hnext _)) h
  | mul src =>
    apply RegOrMem.interp_mono src s p _ h; intro b s' h_inner sf zf af pf
    exact hnext _ (h_inner sf zf af pf)
  | mulx r_hi r_lo src1 =>
    exact RegOrMem.interp_mono src1 s p (fun a s' => hnext _) h
  | imul1 src =>
    apply RegOrMem.interp_mono src s p _ h; intro b s' h_inner sf zf af pf
    exact hnext _ (h_inner sf zf af pf)
  | imul dst src1 src2 =>
    apply RegOrMem.interp_mono src1 s p _ h; intro a s'
    apply Operand.interp_mono src2 s' p; intro b s''
    apply MachineData.set_mono _ _ _ p; intro s''' h_inner sf zf af pf
    exact hnext _ (h_inner sf zf af pf)
  | test a b =>
    apply RegOrMem.interp_mono a s p _ h; intro a' s'
    apply Operand.interp_mono b s' p; intro b' s'' h_inner af
    exact hnext _ (h_inner af)
  | and dst src =>
    apply RegOrMem.interp_mono dst s p _ h; intro a s'
    apply Operand.interp_mono src s' p; intro b s'' h_inner af
    exact MachineData.set_mono _ dst _ p hnext (h_inner af)
  | or dst src =>
    apply RegOrMem.interp_mono dst s p _ h; intro a s'
    apply Operand.interp_mono src s' p; intro b s'' h_inner af
    exact MachineData.set_mono _ dst _ p hnext (h_inner af)
  | xor dst src =>
    apply RegOrMem.interp_mono dst s p _ h; intro a s'
    apply Operand.interp_mono src s' p; intro b s'' h_inner af
    exact MachineData.set_mono _ dst _ p hnext (h_inner af)
  | not dst =>
    exact RegOrMem.interp_mono dst s p (fun a s' => MachineData.set_mono _ dst _ p hnext) h
  | shl dst count =>
    apply RegOrMem.interp_mono dst s p _ h; intro a s' h_inner
    if h0 : (count.interpMasked s' p w == 0) = true then
      simp [h0] at *; exact hnext _ h_inner
    else
      simp [h0] at *; intro af
      have h_inner' : Effects.All _ _ := h_inner af
      if hbits : count.interpMasked s' p w < w.bits then
        simp [hbits] at *
        split at h_inner' <;> split <;> try contradiction
        · exact MachineData.set_mono _ dst _ p hnext h_inner'
        · intro of; exact MachineData.set_mono _ dst _ p hnext (h_inner' of)
      else
        simp [hbits] at *; intro cf
        have h_inner'' : Effects.All _ _ := h_inner' cf
        split at h_inner'' <;> split <;> try contradiction
        · exact MachineData.set_mono _ dst _ p hnext h_inner''
        · intro of; exact MachineData.set_mono _ dst _ p hnext (h_inner'' of)
  | shr dst count =>
    apply RegOrMem.interp_mono dst s p _ h; intro a s' h_inner
    if h0 : (count.interpMasked s' p w == 0) = true then
      simp [h0] at *; exact hnext _ h_inner
    else
      simp [h0] at *; intro af
      have h_inner' : Effects.All _ _ := h_inner af
      if hbits : count.interpMasked s' p w < w.bits then
        simp [hbits] at *
        split at h_inner' <;> split <;> try contradiction
        · exact MachineData.set_mono _ dst _ p hnext h_inner'
        · intro of; exact MachineData.set_mono _ dst _ p hnext (h_inner' of)
      else
        simp [hbits] at *; intro cf
        have h_inner'' : Effects.All _ _ := h_inner' cf
        split at h_inner'' <;> split <;> try contradiction
        · exact MachineData.set_mono _ dst _ p hnext h_inner''
        · intro of; exact MachineData.set_mono _ dst _ p hnext (h_inner'' of)
  | sar dst count =>
    apply RegOrMem.interp_mono dst s p _ h; intro a s' h_inner
    if h0 : (count.interpMasked s' p w == 0) = true then
      simp [h0] at *; exact hnext _ h_inner
    else
      simp [h0] at *; intro af
      have h_inner' : Effects.All _ _ := h_inner af
      if hbits : count.interpMasked s' p w < w.bits then
        simp [hbits] at *
        split at h_inner' <;> split <;> try contradiction
        · exact MachineData.set_mono _ dst _ p hnext h_inner'
        · intro of; exact MachineData.set_mono _ dst _ p hnext (h_inner' of)
      else
        simp [hbits] at *; intro cf
        have h_inner'' : Effects.All _ _ := h_inner' cf
        split at h_inner'' <;> split <;> try contradiction
        · exact MachineData.set_mono _ dst _ p hnext h_inner''
        · intro of; exact MachineData.set_mono _ dst _ p hnext (h_inner'' of)
  | shrd dst src count =>
    apply RegOrMem.interp_mono dst s p _ h; intro a s'
    apply Reg.interp_mono src s' p; intro b s'' h_inner
    if h0 : (count.interpMasked s'' p w == 0) = true then
      simp [h0] at *; exact hnext _ h_inner
    else
      simp [h0] at *
      if h64 : count.interpMasked s'' p w ≥ w.bits then
        simp [h64] at *; intro status; exact MachineData.set_mono _ dst _ p hnext (h_inner status)
      else
        simp [h64] at *; intro af
        have h_inner' : Effects.All _ _ := h_inner af
        split at h_inner' <;> split <;> try contradiction
        · exact MachineData.set_mono _ dst _ p hnext h_inner'
        · intro of; exact MachineData.set_mono _ dst _ p hnext (h_inner' of)
  | shld dst src count =>
    apply RegOrMem.interp_mono dst s p _ h; intro a s'
    apply Reg.interp_mono src s' p; intro b s'' h_inner
    if h0 : (count.interpMasked s'' p w == 0) = true then
      simp [h0] at *; exact hnext _ h_inner
    else
      simp [h0] at *
      if h64 : count.interpMasked s'' p w ≥ w.bits then
        simp [h64] at *; intro status; exact MachineData.set_mono _ dst _ p hnext (h_inner status)
      else
        simp [h64] at *; intro af
        have h_inner' : Effects.All _ _ := h_inner af
        split at h_inner' <;> split <;> try contradiction
        · exact MachineData.set_mono _ dst _ p hnext h_inner'
        · intro of; exact MachineData.set_mono _ dst _ p hnext (h_inner' of)
  | rol dst count =>
    apply RegOrMem.interp_mono dst s p _ h; intro a s' h_inner
    if h0 : (count.interpMasked s' p w == 0) = true then
      simp [h0] at *; exact hnext _ h_inner
    else
      simp [h0] at *
      split at h_inner <;> split <;> try contradiction
      · exact MachineData.set_mono _ dst _ p hnext h_inner
      · intro of; exact MachineData.set_mono _ dst _ p hnext (h_inner of)
  | ror dst count =>
    apply RegOrMem.interp_mono dst s p _ h; intro a s' h_inner
    if h0 : (count.interpMasked s' p w == 0) = true then
      simp [h0] at *; exact hnext _ h_inner
    else
      simp [h0] at *
      split at h_inner <;> split <;> try contradiction
      · exact MachineData.set_mono _ dst _ p hnext h_inner
      · intro of; exact MachineData.set_mono _ dst _ p hnext (h_inner of)
  | rcr dst count =>
    apply RegOrMem.interp_mono dst s p _ h; intro a s' h_inner
    if h0 : (count.interpMasked s' p w == 0) = true then
      simp [h0] at *; exact hnext _ h_inner
    else
      simp [h0] at *
      split at h_inner <;> split <;> try contradiction
      · exact MachineData.set_mono _ dst _ p hnext h_inner
      · intro of; exact MachineData.set_mono _ dst _ p hnext (h_inner of)
  | rcl dst count =>
    apply RegOrMem.interp_mono dst s p _ h; intro a s' h_inner
    if h0 : (count.interpMasked s' p w == 0) = true then
      simp [h0] at *; exact hnext _ h_inner
    else
      simp [h0] at *
      split at h_inner <;> split <;> try contradiction
      · exact MachineData.set_mono _ dst _ p hnext h_inner
      · intro of; exact MachineData.set_mono _ dst _ p hnext (h_inner of)
  | bswap dst =>
    dsimp [Operation.interp] at *
    split at h
    · exact hnext _ h
    · exact hnext _ h
    · intro v; exact hnext _ (h v)
  | jcc cc l =>
    dsimp [Operation.interp] at *; split at h <;> split <;> try contradiction
    · exact hjmp _ _ h
    · exact hnext _ h
  | jmp tgt =>
    exact RelRegOrMem.interp_mono tgt s p (fun a s' => hjmp (.ofBitVec a) s') h
  | call tgt =>
    exact RelRegOrMem.interp_mono tgt s p (fun a s' => MachineData.store_mono (fun s'' => hjmp (.ofBitVec a) s'')) h
  | ret =>
    exact MachineData.load_mono (fun ra s' => hjmp (.ofBitVec ra) _) h
  | nop _ | nopalign _ _ =>
    exact hnext _ h

theorem Instr.interp_mono [Labels]
    (i : Instr) (s : MachineData) (p : Std.Rco Int64)
    {next₁ next₂ : MachineData → Effects}
    {jmp₁ jmp₂ : Int64 → MachineData → Effects}
    {post₁ post₂ : MachineState → Prop}
    (hnext : ∀ s', (next₁ s').All post₁ → (next₂ s').All post₂)
    (hjmp : ∀ pc' s', (jmp₁ pc' s').All post₁ → (jmp₂ pc' s').All post₂)
    (h : (Instr.interp i s p next₁ jmp₁).All post₁) :
    (Instr.interp i s p next₂ jmp₂).All post₂ := by
  cases i with
  | regular addr_sz op_sz op =>
    dsimp [Instr.interp, Effects.All] at *
    let _ : AddressSize := ⟨addr_sz⟩
    exact Operation.interp_mono op p s hnext hjmp h
  | avx addr_sz op_sz op =>
    dsimp [Instr.interp, Effects.All] at *
    let _ : AddressSize := ⟨addr_sz⟩
    exact AvxOperation.interp_mono op p s hnext h

theorem Directive.interp_mono [Labels]
    (d : Directive) (s : MachineData) (p : Std.Rco Int64)
    {next₁ next₂ : MachineData → Effects}
    {jmp₁ jmp₂ : Int64 → MachineData → Effects}
    {post₁ post₂ : MachineState → Prop}
    (hnext : ∀ s', (next₁ s').All post₁ → (next₂ s').All post₂)
    (hjmp : ∀ pc' s', (jmp₁ pc' s').All post₁ → (jmp₂ pc' s').All post₂)
    (h : (Directive.interp d s p next₁ jmp₁).All post₁) :
    (Directive.interp d s p next₂ jmp₂).All post₂ := by
  cases d with
  | label _ =>
    exact hnext s h
  | instr i =>
    exact Instr.interp_mono i s p hnext hjmp h
  | byteArray _ =>
    contradiction

theorem Directives.interp_mono [Labels]
    (ds : List (Directive × Nat)) (s : MachineData) (pc : Int64)
    {ret₁ ret₂ : Int64 → MachineData → Effects}
    {post₁ post₂ : MachineState → Prop}
    (hret : ∀ pc' s', (ret₁ pc' s').All post₁ → (ret₂ pc' s').All post₂)
    (h : (Directives.interp ds s pc ret₁).All post₁) :
    (Directives.interp ds s pc ret₂).All post₂ := by
  induction ds generalizing s pc with
  | nil =>
    exact hret pc s h
  | cons head tail ih =>
    obtain ⟨d, sz⟩ := head
    dsimp [Directives.interp] at *
    exact Directive.interp_mono d s (.mk pc (pc + .ofNat sz))
      (fun s' => ih s' (pc + .ofNat sz))
      hret
      h

theorem Directives.interp_step_all [Labels]
    (ds : List (Directive × Nat)) (s : MachineData) (pc : Int64)
    (cont : Int64 → MachineData → Effects)
    (post₁ post₂ : MachineState → Prop)
    (hcont : ∀ pc' s', post₁ (s', pc') → (cont pc' s').All post₂)
    (h : (Directives.interp ds s pc (fun pc' s' => Effects.done (s', pc'))).All post₁) :
    (Directives.interp ds s pc cont).All post₂ := by
  apply Directives.interp_mono ds s pc (fun pc' s' (h_ret : (Effects.done (s', pc')).All post₁) => by
    dsimp [Effects.All] at h_ret
    exact hcont pc' s' h_ret) h


-- NOTE: 'initial' cannot be moved to the left of the colon as a parameter
-- because it varies in the recursive call in the 'step' constructor (it becomes 'mid').
inductive Eventually {State : Type} (trans : State → Post → Prop) (post : Post) : Post
  | done (initial: State):
      post initial →
      Eventually trans post initial
  | step (initial: State):
      (mid_p: Post) →
      trans initial mid_p →
      (forall (mid: State), mid_p mid → Eventually trans post mid) →
      Eventually trans post initial

theorem step_cps {State : Type} (trans : State → Post → Prop) (post : Post) (initial : State) :
  trans initial (fun mid => Eventually trans post mid) → Eventually trans post initial :=
  by
    intro h
    exact .step initial _ h (fun _ => id)

theorem eventually_trans {State : Type} (trans : State → Post → Prop) (p q : Post) (initial : State)
  (e : Eventually trans p initial)
  (h : ∀ s, p s → Eventually trans q s) :
    Eventually trans q initial
  := by
    induction e with
    | done initial hp => exact h initial hp
    | step initial mid_p ht _ ih => exact .step initial mid_p ht ih

theorem eventually_weaken {State : Type} (trans : State → Post → Prop) (p q : Post) (initial : State)
  (h : ∀ s, p s → q s) :
    Eventually trans p initial → Eventually trans q initial
  := by
    exact fun hp => eventually_trans trans p q initial hp fun s hs => .done s (h s hs)

-- A loop down to 0
theorem reg_dec_loop {State : Type} (trans : State → Post → Prop) (post : Post) (initial : State) (invariant : Nat → Post) (n : Nat) :
  -- if:
  -- invariant holds before entering the loop
  invariant n initial ∧
  -- final iteration allows proving `post`
  (∀ state, invariant 0 state → Eventually trans post state) ∧
  -- while iterating, we eventually re-establish the invariant
  (∀ state k, k ≠ 0 → invariant k state → Eventually trans (invariant (k - 1)) state) →
  -- then: we can prove the post
  Eventually trans post initial
  := by
    rintro ⟨hinv, hzero, hnz⟩
    if h : n = 0 then
      exact hzero initial (h ▸ hinv)
    else
      exact eventually_trans trans (invariant (n - 1)) post initial
        (hnz initial n h hinv) fun s hs =>
          reg_dec_loop trans post s invariant (n - 1) ⟨hs, hzero, hnz⟩

def step1 [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.step e s .done).All post

def straightlineStep [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.straightline e s .done).All post

theorem directivesAtFromPrefix (e: Executable) (a: Int64):
  let starts_at_a := e.withAddresses.dropWhile (·.1 ≠ a)
  e.directivesFromAddress a = e.directivesAtAddress a ++ (starts_at_a.dropWhile (·.1 = a)).map (·.2)
:= by
  dsimp [Executable.directivesFromAddress, Executable.directivesAtAddress]
  rw [← List.map_append]
  rw [List.takeWhile_append_dropWhile]

theorem Directives.interp_append [Labels]
    (ds1 ds2 : List (Directive × Nat)) (s : MachineData) (pc : Int64)
    (ret : Int64 → MachineData → Effects)
    {post : MachineState → Prop}
    (hjmp : ∀ pc' s', (Directives.interp ds2 s' pc' ret).All post → (ret pc' s').All post)
    (h : (Directives.interp ds1 s pc (fun pc' s' => Directives.interp ds2 s' pc' ret)).All post) :
    (Directives.interp (ds1 ++ ds2) s pc ret).All post := by
  induction ds1 generalizing s pc with
  | nil =>
    dsimp [Directives.interp] at *
    exact h
  | cons head tail ih =>
    obtain ⟨d, sz⟩ := head
    dsimp [Directives.interp] at *
    apply Directive.interp_mono (jmp₁ := fun pc' s' => Directives.interp ds2 s' pc' ret) (jmp₂ := ret)
      d s (.mk pc (pc + .ofNat sz))
      (fun s' => ih s' (pc + .ofNat sz))
      hjmp
      h

theorem Directives.interp_split [Labels]
    (ds1 ds2 : List (Directive × Nat)) (s : MachineData) (pc : Int64)
    (ret₁ ret₂ : Int64 → MachineData → Effects)
    {post₁ post₂ : MachineState → Prop}
    (hjmp : ∀ pc' s', (ret₁ pc' s').All post₁ → (ret₂ pc' s').All post₂)
    (hnext : ∀ s',
      (Directives.interp ds2 s' (ds1.foldl (fun p (_, sz) => p + .ofNat sz) pc) ret₁).All post₁ →
      (ret₂ (ds1.foldl (fun p (_, sz) => p + .ofNat sz) pc) s').All post₂)
    (h : (Directives.interp (ds1 ++ ds2) s pc ret₁).All post₁) :
    (Directives.interp ds1 s pc ret₂).All post₂ := by
  induction ds1 generalizing s pc with
  | nil =>
    dsimp [Directives.interp] at *
    exact hnext s h
  | cons head tail ih =>
    obtain ⟨d, sz⟩ := head
    dsimp [Directives.interp] at *
    exact Directive.interp_mono d s (.mk pc (pc + .ofNat sz))
      (fun s' => ih s' (pc + .ofNat sz) hnext)
      hjmp
      h

private theorem withAddresses_foldl_aux (ds : List (Directive × Nat)) (currAddr : Int64)
    (acc : List (Int64 × Directive × Nat)) :
    (ds.foldl (fun (currAddr, acc) (d, z) => (currAddr + .ofNat z, (currAddr, d, z) :: acc)) (currAddr, acc)).2.reverse =
      acc.reverse ++ (ds.foldl (fun (currAddr, acc) (d, z) => (currAddr + .ofNat z, (currAddr, d, z) :: acc)) (currAddr, [])).2.reverse := by
  induction ds generalizing currAddr acc with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨d, z⟩ := hd
    simp only [List.foldl_cons]
    rw [ih (currAddr + .ofNat z) ((currAddr, d, z) :: acc)]
    rw [ih (currAddr + .ofNat z) [(currAddr, d, z)]]
    simp

@[simp]
theorem Executable.withAddresses_nil (a : Int64) :
    Executable.withAddresses (a, []) = [] := rfl

@[simp]
theorem Executable.withAddresses_cons (a : Int64) (d : Directive) (z : Nat) (ds : List (Directive × Nat)) :
    Executable.withAddresses (a, (d, z) :: ds) = (a, d, z) :: Executable.withAddresses (a + .ofNat z, ds) := by
  dsimp [Executable.withAddresses]
  rw [withAddresses_foldl_aux ds (a + .ofNat z) [(a, d, z)]]
  rfl

theorem withAddresses_dropWhile_eq (start_addr : Int64) (ds : List (Directive × Nat))
    (p : (Int64 × Directive × Nat) → Bool) {x : Int64 × Directive × Nat} {xs : List (Int64 × Directive × Nat)}
    (h : (Executable.withAddresses (start_addr, ds)).dropWhile p = x :: xs) :
    p x = false ∧ ∃ ds', x :: xs = Executable.withAddresses (x.1, ds') := by
  induction ds generalizing start_addr with
  | nil =>
    rw [Executable.withAddresses_nil] at h
    contradiction
  | cons head tail ih =>
    obtain ⟨d, sz⟩ := head
    rw [Executable.withAddresses_cons] at h
    simp only [List.dropWhile_cons] at h
    split at h
    · exact ih (start_addr + .ofNat sz) h
    · rename_i hp
      injection h with hx hxs
      subst hx hxs
      refine ⟨Bool.eq_false_iff.mpr hp, (d, sz) :: tail, ?_⟩
      rw [Executable.withAddresses_cons]

theorem withAddresses_takeWhile_foldl (start_addr : Int64) (ds : List (Directive × Nat))
    (p : (Int64 × Directive × Nat) → Bool) {y : Int64 × Directive × Nat} {ys : List (Int64 × Directive × Nat)}
    (h : (Executable.withAddresses (start_addr, ds)).dropWhile p = y :: ys) :
    (((Executable.withAddresses (start_addr, ds)).takeWhile p).map (·.2)).foldl
      (fun a (_, sz) => a + .ofNat sz) start_addr = y.1 := by
  induction ds generalizing start_addr with
  | nil =>
    rw [Executable.withAddresses_nil] at h
    contradiction
  | cons head tail ih =>
    obtain ⟨d, sz⟩ := head
    rw [Executable.withAddresses_cons] at h ⊢
    simp only [List.dropWhile_cons, List.takeWhile_cons] at h ⊢
    split at h
    · rename_i hp
      simp [hp]
      exact ih (start_addr + .ofNat sz) h
    · rename_i hp
      simp [hp]
      injection h with hy _
      rw [← hy]

def Executable.WellFormed (e : Executable) : Prop :=
  ∀ a y ys,
    (e.withAddresses.dropWhile (·.1 ≠ a)).dropWhile (·.1 = a) = y :: ys →
    e.withAddresses.dropWhile (·.1 ≠ y.1) = y :: ys

theorem eventually_step [Layout] (e: Executable) (hwf : e.WellFormed) (st: MachineState) (post: @Post MachineState):
    straightlineStep e st post →
    Eventually (step1 e) post st
    := by
  intro h
  let _ : Labels := e.labels
  let s := st.1
  let pc := st.2
  apply step_cps (step1 e) post (s, pc)
  dsimp [step1, straightlineStep, Executable.step, Executable.straightline] at *
  rw [directivesAtFromPrefix e pc] at h
  apply Directives.interp_split (e.directivesAtAddress pc) _ s pc
    (fun pc' s' => Effects.done (s', pc'))
    (fun pc' s' => Effects.done (s', pc'))
    (fun pc' s' hp => Eventually.done (s', pc') hp)
    _ h
  intro s' h_after
  dsimp [Effects.All]
  generalize h_drop : (e.withAddresses.dropWhile (·.1 ≠ pc)).dropWhile (·.1 = pc) = after_pc at h_after
  cases after_pc with
  | nil =>
    dsimp [Directives.interp, Effects.All] at h_after
    exact Eventually.done _ h_after
  | cons y ys =>
    have h_starts_ne : e.withAddresses.dropWhile (·.1 ≠ pc) ≠ [] := by
      intro h_nil
      rw [h_nil] at h_drop
      contradiction
    obtain ⟨x, xs, h_starts⟩ := List.exists_cons_of_ne_nil h_starts_ne
    have h_starts' : (Executable.withAddresses (e.1, e.2)).dropWhile (·.1 ≠ pc) = x :: xs := h_starts
    obtain ⟨hx_eq, ds', h_ds'⟩ := withAddresses_dropWhile_eq e.1 e.2 (·.1 ≠ pc) h_starts'
    have hx_pc : x.1 = pc := by simpa using hx_eq
    rw [hx_pc] at h_ds'
    have h_fold : (e.directivesAtAddress pc).foldl (fun p (_, sz) => p + .ofNat sz) pc = y.1 := by
      dsimp [Executable.directivesAtAddress]
      rw [h_starts, h_ds'] at h_drop ⊢
      exact withAddresses_takeWhile_foldl pc ds' (·.1 = pc) h_drop
    rw [h_fold] at h_after ⊢
    have h_next_from : e.withAddresses.dropWhile (·.1 ≠ y.1) = y :: ys := hwf pc y ys h_drop
    have h_straightline_next : straightlineStep e (s', y.1) post := by
      dsimp [straightlineStep, Executable.straightline, Executable.directivesFromAddress]
      rw [h_next_from]
      exact h_after
    have h_len : (e.withAddresses.dropWhile (·.1 ≠ y.1)).length < (e.withAddresses.dropWhile (·.1 ≠ pc)).length := by
      rw [h_next_from]
      have h_split := List.takeWhile_append_dropWhile (p := (·.1 = pc)) (l := e.withAddresses.dropWhile (·.1 ≠ pc))
      have h_len_eq := congrArg List.length h_split
      rw [List.length_append, h_drop] at h_len_eq
      have h_take_pos : 0 < ((e.withAddresses.dropWhile (·.1 ≠ pc)).takeWhile (·.1 = pc)).length := by
        rw [h_starts, List.takeWhile_cons]
        simp [hx_pc]
      omega
    exact eventually_step e hwf (s', y.1) post h_straightline_next
termination_by (e.withAddresses.dropWhile (·.1 ≠ st.2)).length
decreasing_by exact h_len

private theorem int64_add_ofNat_assoc (a : Int64) (m n : Nat) :
    a + Int64.ofNat m + Int64.ofNat n = a + Int64.ofNat (m + n) := by
  rw [Int64.add_assoc, ← Int64.ofNat_add]

private theorem int64_add_ofNat_ne_self (a : Int64) {k : Nat} (hk_pos : 0 < k) (hk_lt : k < 2 ^ 64) :
    a + Int64.ofNat k ≠ a := by
  intro h
  have hbv : ((a + Int64.ofNat k).toBitVec - a.toBitVec).toNat = (a.toBitVec - a.toBitVec).toNat :=
    congrArg (fun x : Int64 => (x.toBitVec - a.toBitVec).toNat) h
  simp at hbv
  omega

private theorem withAddresses_dropWhile_eq_offset (cur a : Int64) (ds : List (Directive × Nat))
    {y : Int64 × Directive × Nat} {ys : List (Int64 × Directive × Nat)}
    (h : (Executable.withAddresses (cur, ds)).dropWhile (·.1 = a) = y :: ys) :
    y.1 ≠ a ∧ ∃ k ≤ (ds.map (·.2)).sum, y.1 = cur + Int64.ofNat k := by
  induction ds generalizing cur with
  | nil =>
    rw [Executable.withAddresses_nil] at h
    contradiction
  | cons hd tl ih =>
    obtain ⟨d, sz⟩ := hd
    rw [Executable.withAddresses_cons, List.dropWhile_cons] at h
    split at h
    · obtain ⟨hne, k', hk', hy⟩ := ih (cur + Int64.ofNat sz) h
      have hle : sz + k' ≤ (((d, sz) :: tl).map (·.2)).sum := by
        simp only [List.map_cons, List.sum_cons]
        omega
      refine ⟨hne, sz + k', hle, ?_⟩
      rw [hy, int64_add_ofNat_assoc]
    · rename_i hp
      injection h with hy _
      subst hy
      have hne : cur ≠ a := by simpa using hp
      refine ⟨hne, 0, Nat.zero_le _, ?_⟩
      simp

private theorem withAddresses_dropWhile_offset (start_addr a : Int64) (ds : List (Directive × Nat))
    {y : Int64 × Directive × Nat} {ys : List (Int64 × Directive × Nat)}
    (h : ((Executable.withAddresses (start_addr, ds)).dropWhile (·.1 ≠ a)).dropWhile (·.1 = a) = y :: ys) :
    ∃ k, 0 < k ∧ k ≤ (ds.map (·.2)).sum ∧ y.1 = start_addr + Int64.ofNat k := by
  induction ds generalizing start_addr with
  | nil =>
    rw [Executable.withAddresses_nil] at h
    contradiction
  | cons hd tl ih =>
    obtain ⟨d, sz⟩ := hd
    rw [Executable.withAddresses_cons, List.dropWhile_cons] at h
    split at h
    · obtain ⟨k', hk'_pos, hk'_le, hy⟩ := ih (start_addr + Int64.ofNat sz) h
      have hpos : 0 < sz + k' := by omega
      have hle : sz + k' ≤ (((d, sz) :: tl).map (·.2)).sum := by
        simp only [List.map_cons, List.sum_cons]
        omega
      refine ⟨sz + k', hpos, hle, ?_⟩
      rw [hy, int64_add_ofNat_assoc]
    · rename_i hp
      have h_eq : start_addr = a := by simpa using hp
      subst h_eq
      have h' : (Executable.withAddresses (start_addr, (d, sz) :: tl)).dropWhile (·.1 = start_addr) = y :: ys := by
        rw [Executable.withAddresses_cons]
        exact h
      obtain ⟨hne, k, hk_le, hy⟩ := withAddresses_dropWhile_eq_offset start_addr start_addr ((d, sz) :: tl) h'
      have hk_pos : 0 < k := by
        cases k with
        | zero =>
          simp at hy
          exact absurd hy hne
        | succ n => omega
      exact ⟨k, hk_pos, hk_le, hy⟩

theorem Executable.wellFormed_of_sum_lt (e : Executable)
    (hsum : (e.2.map (·.2)).sum < 2 ^ 64) :
    e.WellFormed := by
  obtain ⟨start_addr, ds⟩ := e
  intro a y ys h
  induction ds generalizing start_addr with
  | nil =>
    rw [Executable.withAddresses_nil] at h
    contradiction
  | cons hd tl ih =>
    obtain ⟨d, sz⟩ := hd
    simp only [List.map_cons, List.sum_cons] at hsum
    have hsum_tl : (tl.map (·.2)).sum < 2 ^ 64 := by omega
    obtain ⟨k, hk_pos, hk_le, hy_eq⟩ := withAddresses_dropWhile_offset start_addr a ((d, sz) :: tl) h
    simp only [List.map_cons, List.sum_cons] at hk_le
    have hk_lt : k < 2 ^ 64 := by omega
    have h_ne_y : (start_addr ≠ y.1) = True := eq_true (by
      rw [hy_eq]
      exact Ne.symm (int64_add_ofNat_ne_self start_addr hk_pos hk_lt))
    rw [Executable.withAddresses_cons, List.dropWhile_cons]
    simp only [decide_eq_true_eq, h_ne_y, ↓reduceIte]
    rw [Executable.withAddresses_cons, List.dropWhile_cons] at h
    split at h
    · exact ih (start_addr + Int64.ofNat sz) hsum_tl h
    · rename_i hp
      have h_eq : start_addr = a := by simpa using hp
      subst h_eq
      simp only [List.dropWhile_cons, decide_true, ↓reduceIte] at h
      by_cases h_next : start_addr + Int64.ofNat sz = start_addr
      · rw [h_next] at h ⊢
        cases tl with
        | nil =>
          rw [Executable.withAddresses_nil] at h
          contradiction
        | cons hd2 tl2 =>
          have h_drop_start : (Executable.withAddresses (start_addr, hd2 :: tl2)).dropWhile (·.1 ≠ start_addr) =
              Executable.withAddresses (start_addr, hd2 :: tl2) := by
            obtain ⟨d2, sz2⟩ := hd2
            rw [Executable.withAddresses_cons, List.dropWhile_cons]
            simp
          rw [← h_drop_start] at h
          exact ih start_addr hsum_tl h
      · cases h_tl : Executable.withAddresses (start_addr + Int64.ofNat sz, tl) with
        | nil =>
          rw [h_tl] at h
          contradiction
        | cons z zs =>
          have hz : z.1 = start_addr + Int64.ofNat sz := by
            cases tl with
            | nil => rw [Executable.withAddresses_nil] at h_tl; contradiction
            | cons hd2 tl2 =>
              obtain ⟨d2, sz2⟩ := hd2
              rw [Executable.withAddresses_cons] at h_tl
              injection h_tl with hz_eq _
              rw [← hz_eq]
          rw [h_tl, List.dropWhile_cons] at h
          simp only [hz, decide_eq_true_eq, h_next, ↓reduceIte] at h
          rw [h, List.dropWhile_cons]
          simp

theorem eventually_step_of_sum_lt [Layout] (e : Executable)
    (hsum : (e.2.map (·.2)).sum < 2 ^ 64)
    (st : MachineState) (post : @Post MachineState) :
    straightlineStep e st post →
    Eventually (step1 e) post st :=
  eventually_step e (Executable.wellFormed_of_sum_lt e hsum) st post

theorem eventually_step_cps [Layout] (e : Executable) (hwf : e.WellFormed)
    (st : MachineState) (post : @Post MachineState) :
    straightlineStep e st (fun mid => Eventually (step1 e) post mid) →
    Eventually (step1 e) post st := by
  intro h
  exact eventually_trans (step1 e) (fun mid => Eventually (step1 e) post mid) post st
    (eventually_step e hwf st _ h) (fun _ => id)

theorem eventually_step_cps_of_sum_lt [Layout] (e : Executable)
    (hsum : (e.2.map (·.2)).sum < 2 ^ 64)
    (st : MachineState) (post : @Post MachineState) :
    straightlineStep e st (fun mid => Eventually (step1 e) post mid) →
    Eventually (step1 e) post st :=
  eventually_step_cps e (Executable.wellFormed_of_sum_lt e hsum) st post


