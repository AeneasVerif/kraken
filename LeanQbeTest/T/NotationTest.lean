module

public import LeanQbe.T.Flat
import LeanQbe.T.Notation
public import LeanQbe.T.Wf
public import LeanQbeTest.T.Examples
public import LeanQbeTest.T.Smoke
import LeanQbe.T.FlatLemmas
meta import Lean
meta import LeanQbe.T.Notation

/-!
# Typed IR Notation Tests (`tqbe`)

Covers:
1. Kernel definitional equality (`rfl`) between `tqbe` notation and hand-written `LeanQbe.T` terms
   (`add128`, `mulByAdd`, `qrStep` with lane-wise `[16, 16, 16, 16]` and `splat 16`, `vumin`,
   `evenOdd`, `readLeb128T`, and `lbCheckPrf` modeled after `LeanQbe/T/Examples/LratBytes.lean`).
2. `Func.Wf` via `t_wf_reify` (and `t_wf_tac` for polymorphic `vumin k`) plus `checkTFlat`.
3. Structured sugar forms (`loop`/`break`/`continue`/`check`/`switch`), multi-result ops
   (`addc`/`subb`/`umulw`/`smulw`), `pair` ops (`mkpair`/`unpair`/`fst`/`snd`), lane-wise vector
   immediates, float/cast/SIMD/memory/call/exit/hlt ops, nested groups, `tqbe ->`, `tqbe $sym`,
   and `tqbe_def`.
4. Executable 2000-instruction scaling test (`def sl2000`, NOT `noncomputable`) with `t_wf_reify`
   and `t_kernel_rfl`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.NotationTest

open LeanQbe.T LeanQbe.T.Notation

abbrev u128 : Ty := LeanQbe.T.Examples.u128

/-! ## 1. Parity (`rfl`) against hand-written `LeanQbe.T` examples -/

def add128 : Func [u128, u128] [u128, Ty.bool] := tqbe(%a:u128, %b:u128) -> (u128, b) {
  %a0, %a1 = unpair %a
  %b0, %b1 = unpair %b
  %s0, %c0 =l addc %a0, %b0, false
  %s1, %c1 =l addc %a1, %b1, %c0
  %s =(l,l) mkpair %s0, %s1
  ret %s, %c1
}

theorem add128_eq_rfl : add128 = LeanQbe.T.Examples.add128 := rfl
theorem add128_wf : Func.Wf add128 := by t_wf_reify
theorem add128_check : Func.checkTFlat add128 = true := by decide

def mulByAdd : Func [i64, i64] [i64, i64] := tqbe(%n:l, %b:l) -> (l, l) {
  loop @loop(%i:l = %n, %lo:l = 0, %hi:l = 0) {
    %z =b ceql %i, 0
    jnz %z, {
      ret %lo, %hi
    }, {
      %lo', %c =l addc %lo, %b, false
      %hi', %_ =l addc %hi, 0, %c
      %i' =l sub %i, 1
      continue @loop(%i', %lo', %hi')
    }
  }
}

theorem mulByAdd_eq_rfl : mulByAdd = LeanQbe.T.Examples.mulByAdd := rfl
theorem mulByAdd_wf : Func.Wf mulByAdd := by t_wf_reify
theorem mulByAdd_check : Func.checkTFlat mulByAdd = true := by decide

def qrStepLanes : Func [v4i32, v4i32, v4i32] [v4i32, v4i32] :=
  tqbe(%a:v4i32, %b:v4i32, %d:v4i32) -> (v4i32, v4i32) {
    %a' =v4i32 add %a, %b
    %x =v4i32 xor %d, %a'
    %d' =v4i32 rotl %x, [16, 16, 16, 16]
    ret %a', %d'
  }

def qrStepSplat : Func [v4i32, v4i32, v4i32] [v4i32, v4i32] :=
  tqbe(%a:v4i32, %b:v4i32, %d:v4i32) -> (v4i32, v4i32) {
    %a' =v4i32 add %a, %b
    %x =v4i32 xor %d, %a'
    %d' =v4i32 rotl %x, splat 16
    ret %a', %d'
  }

theorem qrStep_lanes_eq_rfl : qrStepLanes = LeanQbe.T.Examples.qrStep := rfl
theorem qrStep_splat_eq_rfl : qrStepSplat = LeanQbe.T.Examples.qrStep := rfl
theorem qrStep_wf : Func.Wf qrStepLanes := by t_wf_reify
theorem qrStep_check : Func.checkTFlat qrStepLanes = true := by decide

def vumin (k : Nat) : Func [Ty.vec k i32, Ty.vec k i32] [Ty.vec k i32] :=
  tqbe(%a:vec k w, %b:vec k w) -> vec k w {
    %c = ult %a, %b
    %r = blend %c, %a, %b
    ret %r
  }

theorem vumin_eq_rfl (k : Nat) : vumin k = LeanQbe.T.Examples.vumin k := rfl
theorem vumin_wf (k : Nat) : Func.Wf (vumin k) := by t_wf_tac

def evenOdd : Func [i64] [i32] := tqbe(%n:l) -> w {
  @even(%x:l) {
    %c =b cultl 0, %x
    jnz %c, {
      %y =l sub %x, 1
      jmp @odd(%y)
    }, {
      ret 1
    }
  }
  @odd(%x:l) {
    %c =b cultl 0, %x
    jnz %c, {
      %y =l sub %x, 1
      jmp @even(%y)
    }, {
      ret 0
    }
  }
  {
    jmp @even(%n)
  }
}

theorem evenOdd_eq_rfl : evenOdd = LeanQbe.T.Smoke.evenOdd := rfl
theorem evenOdd_wf : Func.Wf evenOdd := by t_wf_reify
theorem evenOdd_check : Func.checkTFlat evenOdd = true := by decide

/-! ## 2. `lbCheckPrf` from `LratBytes.lean` in typed IR notation + `rfl` parity -/

def readLeb128T {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (fail : L []) (cur pend : V i64) (done : V i64 → V i64 → Expr V L rs) : Expr V L rs :=
  tqbe {
    @done_leb(%u:l, %res:l) {
      ⟨done u res⟩
    }
    {
      loop @leb(%p:l = %cur, %acc:l = 0, %sh:l = 0) {
        %eof =b ceql %p, %pend
        jnz %eof, @fail, {
          %b8 =i8 load %p
          %b =l extub %b8
          %p1 =l add %p, 1
          %lo =l and %b, 127
          %sl =l shl %lo, %sh
          %acc2 =l or %acc, %sl
          %hi =l and %b, 128
          %more =b cnel %hi, 0
          jnz %more, {
            %sh2 =l add %sh, 7
            %oksh =b cultl %sh2, 28
            check %oksh else @fail
            continue @leb(%p1, %acc2, %sh2)
          }, @done_leb(%acc2, %p1)
        }
      }
    }
  }

def readLeb128THand {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (fail : L []) (cur pend : V i64) (done : V i64 → V i64 → Expr V L rs) : Expr V L rs :=
  Expr.group (sig := [[i64, i64]])
    (fun _ => Blocks.cons (fun (u, res, _) => done u res) Blocks.nil)
    fun (done_leb, _) =>
      Expr.group (sig := [[i64, i64, i64]])
        (fun (leb, _) =>
          Blocks.cons (fun (p, acc, sh, _) =>
            Expr.let_ (op2 (OpCode.eq i64) (Arg.var p) (Arg.var pend)) fun (eof, _) =>
            Expr.jnz (Arg.var eof) (Expr.jump fail ())
              (Expr.load i8 (Arg.var p) fun b8 =>
              Expr.let_ (op1 (OpCode.zext 8 64) (Arg.var b8)) fun (b, _) =>
              Expr.let_ (op2 (OpCode.add i64) (Arg.var p) (Arg.imm 1)) fun (p1, _) =>
              Expr.let_ (op2 (OpCode.and i64) (Arg.var b) (Arg.imm 127)) fun (lo, _) =>
              Expr.let_ (op2 (OpCode.shl i64) (Arg.var lo) (Arg.var sh)) fun (sl, _) =>
              Expr.let_ (op2 (OpCode.or i64) (Arg.var acc) (Arg.var sl)) fun (acc2, _) =>
              Expr.let_ (op2 (OpCode.and i64) (Arg.var b) (Arg.imm 128)) fun (hi, _) =>
              Expr.let_ (op2 (OpCode.ne i64) (Arg.var hi) (Arg.imm 0)) fun (more, _) =>
              Expr.jnz (Arg.var more)
                (Expr.let_ (op2 (OpCode.add i64) (Arg.var sh) (Arg.imm 7)) fun (sh2, _) =>
                Expr.let_ (op2 (OpCode.ult i64) (Arg.var sh2) (Arg.imm 28)) fun (oksh, _) =>
                Expr.jnz (Arg.var oksh)
                  (Expr.jump leb (Arg.var p1, Arg.var acc2, Arg.var sh2, ()))
                  (Expr.jump fail ()))
                (Expr.jump done_leb (Arg.var acc2, Arg.var p1, ()))))
            Blocks.nil)
        fun (leb, _) => Expr.jump leb (Arg.var cur, Arg.imm 0, Arg.imm 0, ())

theorem readLeb128T_eq_hand : @readLeb128T = @readLeb128THand := rfl

/-- Typed IR transliteration of `LeanQbe.Examples.LratBytes.lbCheckPrf` using `tqbe` notation:
`switch` on proof tag `'a'` (97) / `'d'` (100), `check ... else @fail`, nested `loop @del_loop`,
cross-loop `continue @rec_loop`, and macro call `<- readLeb128T(...)`. -/
def lbCheckPrf : Func [i64, i64] [i64] := tqbe(%hdr:l, %prf_end:l) -> l {
  %p8 =l add %hdr, 8
  %nc =l load %p8
  %p16 =l add %hdr, 16
  %cap =l load %p16
  %p48 =l add %hdr, 48
  %cb =l load %p48
  %p64 =l add %hdr, 64
  %p72 =l add %hdr, 72
  @fail() {
    ret 0
  }
  {
    loop @rec_loop() {
      %cur =l load %p72
      %ok_eof =b cnel %cur, %prf_end
      check %ok_eof else @fail
      %tag8 =i8 load %cur
      %tag =l extub %tag8
      %cur1 =l add %cur, 1
      switch %tag {
        97 => {
          %uid:l, %cur2:l <- readLeb128T(@fail, %cur1, %prf_end)
          %odd =l and %uid, 1
          %ok_even =b ceql %odd, 0
          check %ok_even else @fail
          %id =l lshr %uid, 1
          %gt_nc =b cultl %nc, %id
          check %gt_nc else @fail
          %lt_cap =b cultl %id, %cap
          check %lt_cap else @fail
          %off =l shl %id, 3
          %slot =l add %cb, %off
          %old =l load %slot
          %ok_unused =b ceql %old, 0
          check %ok_unused else @fail
          store %cur2, %p72
          %c_ptr =l load %p64
          %lstat =l call $lb_read_add_lits(%hdr, %prf_end)
          %lok =b cnel %lstat, 0
          check %lok else @fail
          %rok =l call $lb_rup_check(%hdr, %id, %c_ptr, %prf_end)
          %rok_nz =b cnel %rok, 0
          check %rok_nz else @fail
          %is_emp =b ceql %lstat, 2
          jnz %is_emp, { ret 1 }, {
            store %c_ptr, %slot
            continue
          }
        },
        100 => {
          loop @del_loop(%dcur:l = %cur1) {
            %u:l, %dcur2:l <- readLeb128T(@fail, %dcur, %prf_end)
            %uz =b ceql %u, 0
            jnz %uz, {
              store %dcur2, %p72
              continue @rec_loop
            }, {
              %odd =l and %u, 1
              %ok_even =b ceql %odd, 0
              check %ok_even else @fail
              %did =l lshr %u, 1
              %dnz =b cnel %did, 0
              check %dnz else @fail
              %lt_cap =b cultl %did, %cap
              check %lt_cap else @fail
              %off =l shl %did, 3
              %slot =l add %cb, %off
              %old =l load %slot
              %act =b cnel %old, 0
              check %act else @fail
              store l 0, %slot
              continue @del_loop(%dcur2)
            }
          }
        },
        _ => @fail
      }
    }
  }
}

def lbCheckPrfHand : Func [i64, i64] [i64] := fun _ _ (hdr, prf_end, _) =>
  Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr) (Arg.imm 8)) fun (p8, _) =>
  Expr.load i64 (Arg.var p8) fun nc =>
  Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr) (Arg.imm 16)) fun (p16, _) =>
  Expr.load i64 (Arg.var p16) fun cap =>
  Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr) (Arg.imm 48)) fun (p48, _) =>
  Expr.load i64 (Arg.var p48) fun cb =>
  Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr) (Arg.imm 64)) fun (p64, _) =>
  Expr.let_ (op2 (OpCode.add i64) (Arg.var hdr) (Arg.imm 72)) fun (p72, _) =>
  Expr.group (sig := [[]])
    (fun _ => Blocks.cons (fun _ => Expr.ret (Arg.imm 0, ())) Blocks.nil)
    fun (fail, _) =>
      Expr.group (sig := [[]])
        (fun (rec_loop, _) =>
          Blocks.cons (fun _ =>
            Expr.load i64 (Arg.var p72) fun cur =>
            Expr.let_ (op2 (OpCode.ne i64) (Arg.var cur) (Arg.var prf_end)) fun (ok_eof, _) =>
            Expr.jnz (Arg.var ok_eof)
              (Expr.load i8 (Arg.var cur) fun tag8 =>
              Expr.let_ (op1 (OpCode.zext 8 64) (Arg.var tag8)) fun (tag, _) =>
              Expr.let_ (op2 (OpCode.add i64) (Arg.var cur) (Arg.imm 1)) fun (cur1, _) =>
              Expr.let_ (op2 (OpCode.eq i64) (Arg.var tag) (Arg.imm 97)) fun (_cmp1, _) =>
              Expr.jnz (Arg.var _cmp1)
                (readLeb128THand fail cur1 prf_end fun uid cur2 =>
                  Expr.let_ (op2 (OpCode.and i64) (Arg.var uid) (Arg.imm 1)) fun (odd, _) =>
                  Expr.let_ (op2 (OpCode.eq i64) (Arg.var odd) (Arg.imm 0)) fun (ok_even, _) =>
                  Expr.jnz (Arg.var ok_even)
                    (Expr.let_ (op2 (OpCode.lshr i64) (Arg.var uid) (Arg.imm 1)) fun (id, _) =>
                    Expr.let_ (op2 (OpCode.ult i64) (Arg.var nc) (Arg.var id)) fun (gt_nc, _) =>
                    Expr.jnz (Arg.var gt_nc)
                      (Expr.let_ (op2 (OpCode.ult i64) (Arg.var id) (Arg.var cap))
                        fun (lt_cap, _) =>
                      Expr.jnz (Arg.var lt_cap)
                        (Expr.let_ (op2 (OpCode.shl i64) (Arg.var id) (Arg.imm 3)) fun (off, _) =>
                        Expr.let_ (op2 (OpCode.add i64) (Arg.var cb) (Arg.var off)) fun (slot, _) =>
                        Expr.load i64 (Arg.var slot) fun old =>
                        Expr.let_ (op2 (OpCode.eq i64) (Arg.var old) (Arg.imm 0))
                          fun (ok_unused, _) =>
                        Expr.jnz (Arg.var ok_unused)
                          (Expr.store (Arg.var cur2) (Arg.var p72)
                            (Expr.load i64 (Arg.var p64) fun c_ptr =>
                            Expr.call (as := [i64, i64]) (bs := [i64]) "lb_read_add_lits"
                              (Arg.var hdr, Arg.var prf_end, ()) fun (lstat, _) =>
                            Expr.let_ (op2 (OpCode.ne i64) (Arg.var lstat) (Arg.imm 0))
                              fun (lok, _) =>
                            Expr.jnz (Arg.var lok)
                              (Expr.call (as := [i64, i64, i64, i64]) (bs := [i64]) "lb_rup_check"
                                (Arg.var hdr, Arg.var id, Arg.var c_ptr, Arg.var prf_end, ())
                                fun (rok, _) =>
                              Expr.let_ (op2 (OpCode.ne i64) (Arg.var rok) (Arg.imm 0))
                                fun (rok_nz, _) =>
                              Expr.jnz (Arg.var rok_nz)
                                (Expr.let_ (op2 (OpCode.eq i64) (Arg.var lstat) (Arg.imm 2))
                                  fun (is_emp, _) =>
                                Expr.jnz (Arg.var is_emp)
                                  (Expr.ret (Arg.imm 1, ()))
                                  (Expr.store (Arg.var c_ptr) (Arg.var slot)
                                    (Expr.jump rec_loop ())))
                                (Expr.jump fail ()))
                              (Expr.jump fail ())))
                          (Expr.jump fail ()))
                        (Expr.jump fail ()))
                      (Expr.jump fail ()))
                    (Expr.jump fail ()))
                (Expr.let_ (op2 (OpCode.eq i64) (Arg.var tag) (Arg.imm 100)) fun (_cmp2, _) =>
                Expr.jnz (Arg.var _cmp2)
                  (Expr.group (sig := [[i64]])
                    (fun (del_loop, _) =>
                      Blocks.cons (fun (dcur, _) =>
                        readLeb128THand fail dcur prf_end fun u dcur2 =>
                          Expr.let_ (op2 (OpCode.eq i64) (Arg.var u) (Arg.imm 0)) fun (uz, _) =>
                          Expr.jnz (Arg.var uz)
                            (Expr.store (Arg.var dcur2) (Arg.var p72) (Expr.jump rec_loop ()))
                            (Expr.let_ (op2 (OpCode.and i64) (Arg.var u) (Arg.imm 1))
                              fun (odd, _) =>
                            Expr.let_ (op2 (OpCode.eq i64) (Arg.var odd) (Arg.imm 0))
                              fun (ok_even, _) =>
                            Expr.jnz (Arg.var ok_even)
                              (Expr.let_ (op2 (OpCode.lshr i64) (Arg.var u) (Arg.imm 1))
                                fun (did, _) =>
                              Expr.let_ (op2 (OpCode.ne i64) (Arg.var did) (Arg.imm 0))
                                fun (dnz, _) =>
                              Expr.jnz (Arg.var dnz)
                                (Expr.let_ (op2 (OpCode.ult i64) (Arg.var did) (Arg.var cap))
                                  fun (lt_cap, _) =>
                                Expr.jnz (Arg.var lt_cap)
                                  (Expr.let_ (op2 (OpCode.shl i64) (Arg.var did) (Arg.imm 3))
                                    fun (off, _) =>
                                  Expr.let_ (op2 (OpCode.add i64) (Arg.var cb) (Arg.var off))
                                    fun (slot, _) =>
                                  Expr.load i64 (Arg.var slot) fun old =>
                                  Expr.let_ (op2 (OpCode.ne i64) (Arg.var old) (Arg.imm 0))
                                    fun (act, _) =>
                                  Expr.jnz (Arg.var act)
                                    (Expr.store (Arg.imm (t := i64) 0) (Arg.var slot)
                                      (Expr.jump del_loop (Arg.var dcur2, ())))
                                    (Expr.jump fail ()))
                                  (Expr.jump fail ()))
                                (Expr.jump fail ()))
                              (Expr.jump fail ())))
                        Blocks.nil)
                    fun (del_loop, _) => Expr.jump del_loop (Arg.var cur1, ()))
                  (Expr.jump fail ())))
              (Expr.jump fail ()))
            Blocks.nil)
        fun (rec_loop, _) => Expr.jump rec_loop ()

theorem lbCheckPrf_eq_hand : lbCheckPrf = lbCheckPrfHand := rfl
theorem lbCheckPrf_wf : Func.Wf lbCheckPrf := by t_wf_reify
theorem lbCheckPrf_check : Func.checkTFlat lbCheckPrf = true := by decide

/-! ## 3. Sugar coverage: `loop`/`break`/`continue`/`check`/`switch`, nested groups, macros -/

def loopBreak : Func [i64] [i64] := tqbe(%n:l) -> l {
  %sum:l <- loop (%i:l = 0, %acc:l = 0) {
    %lt =b cultl %i, %n
    check %lt else break(%acc)
    %acc' =l add %acc, %i
    %i' =l add %i, 1
    continue (%i', %acc')
  }
  ret %sum
}

theorem loopBreak_wf : Func.Wf loopBreak := by t_wf_reify
theorem loopBreak_check : Func.checkTFlat loopBreak = true := by decide

def bumpK {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (exitLbl : L [i64]) (x : V i64) (k : Expr V L rs) : Expr V L rs := tqbe {
  %ok =b cnel %x, 99
  check %ok else @exitLbl(%x)
  ⟨k⟩
}

def namedBreak : Func [i64] [i64] := tqbe(%x:l) -> l {
  @outer_done(%v:l) {
    %v2 =l add %v, 1
    ret %v2
  }
  {
    loop @lp(%i:l = %x, %s:l = 0) -> @after(%res:l) {
      use bumpK(@outer_done, %i)
      %is0 =b ceql %i, 0
      jnz %is0, { break @after(%s) }, {
        %s' =l add %s, %i
        %i' =l sub %i, 1
        continue (%i', %s')
      }
    }
    switch %res {
      0 => { ret 42 },
      7 => @outer_done(7),
      _ => { ret %res }
    }
  }
}

theorem namedBreak_wf : Func.Wf namedBreak := by t_wf_reify
theorem namedBreak_check : Func.checkTFlat namedBreak = true := by decide

/-! ## 4. Comprehensive opcode, pair, multi-result, vector immediate, float, cast & `Fn` coverage -/

def pairAndMulti : Func [i64, i64, i32, Ty.bits 16] [Ty.pair i64 i64, i64, i32] :=
  tqbe(%a:l, %b:l, %w0:w, %h0:i16) -> (pair i64 i64, i64, i32) {
    %s, %c =l addc %a, %b, true
    %d, %bw =l subb %s, %b, %c
    %lo, %hi =l umulw %d, %a
    %slo, %shi =w smulw %w0, 3
    %p =(l,l) mkpair %lo, %hi
    %q = mkpair %slo, %shi
    %p0 = fst %p
    %p1 = snd %p
    %u0, %u1 = unpair %q
    %wsum =w add %u0, %u1
    %hz =w zext %h0
    %hs =l sext %hz
    %ht =w trunc %hs
    %fb =l ofBool %bw
    %bs =l bswap %p0
    %lz =l clz %bs
    %cs =l cls %lz
    %rb =l rbit %cs
    %tz =l ctz %rb
    %pc =l popcnt %tz
    %fs =l fshl %pc, %p1, 5
    %fr =l fshr %fs, %fb, 3
    %tl =l ternlog %fr, %a, %b, 202
    %sel =l select %c, %tl, %lo
    %c0:l, %c1:w = call $helper(%sel, %wsum)
    call $notify(%c0)
    %resPair =(l,l) mkpair %c0, %hi
    %wfinal =w add %c1, %ht
    ret %resPair, %d, %wfinal
  }

theorem pairAndMulti_wf : Func.Wf pairAndMulti := by t_wf_reify
theorem pairAndMulti_check : Func.checkTFlat pairAndMulti = true := by decide

def vecImmOps : Func [v4i32, v8i32, v2i64, v4f32] [v4i32, v8i32, v2i64, v4f32] :=
  tqbe(%v4:v4i32, %v8:v8i32, %v2:v2i64, %vf:v4f32) -> (v4i32, v8i32, v2i64, v4f32) {
    %v4a =v4i32 add %v4, [1, 2, 3, -4]
    %shd =v4i32 shufd %v4a, 27
    %shb =v4i32 shufb %shd, splat 0
    %al =v4i32 alignr %shd, %shb, 4
    %bw =v4i32 blendw %al, %v4a, 170
    %s1 =v4i32 sha256msg1 %bw, %v4a
    %s2 =v4i32 sha256msg2 %s1, %v4a
    %sr =v4i32 sha256rnds2 %s2, %v4a, %shd
    %m4 = ult %sr, splat 10
    %v4out =v4i32 blend %m4, %sr, [10, 20, 30, 40]
    %v4masked =v4i32 blend [true, false, true, false]:mask v4i32, %v4out, %v4
    %v8out =v8i32 add %v8, [1, 2, 3, 4, 5, 6, 7, 8]
    %v2out =v2i64 xor %v2, [-1, 42]
    %vfz =v4f32 fadd %vf, splat imm ⟨0x00000000#32⟩
    %vfout =v4f32 ffma %vfz, %vf, splat imm ⟨0x3f800000#32⟩
    ret %v4masked, %v8out, %v2out, %vfout
  }

theorem vecImmOps_wf : Func.Wf vecImmOps := by t_wf_reify
theorem vecImmOps_check : Func.checkTFlat vecImmOps = true := by decide

def floatCastAndTerms : Func [f32, f64, i64] [f64, i64] :=
  tqbe(%fs:s, %fd:d, %n:l) -> (d, l) {
    %ns =s fneg %fs
    %as =s fabs %ns
    %sq =s fsqrt %as
    %c =b flts %sq, %fs
    jnz %c, {
      %d1 =d fcvt %sq
      %d2 =d fadd %d1, %fd
      %d3 =d fsub %d2, imm ⟨0x3ff0000000000000#64⟩
      %d4 =d fmul %d3, imm ⟨0x4000000000000000#64⟩
      %d5 =d fdiv %d4, imm ⟨0x4008000000000000#64⟩
      %u1 =l fptoui %d5
      %s1 =l fptosi %d5
      %df =d sitofp %n
      %uf =d uitofp %n
      %bs1 =l bitcast %df
      %bs2 =l bitcast %uf
      %sum =l add %u1, %s1
      %res =l xor %sum, %bs1
      %res2 =l or %res, %bs2
      store %res2, %n
      %loaded =l load %n
      ret %df, %loaded
    }, {
      %bad =b ceql %n, 0
      jnz %bad, { exit $abort_fn(%n) }, { hlt }
    }
  }

theorem floatCastAndTerms_wf : Func.Wf floatCastAndTerms := by t_wf_reify
theorem floatCastAndTerms_check : Func.checkTFlat floatCastAndTerms = true := by decide

def fragEmptyRet : Func [] [] := tqbe -> () {
  ret
}

theorem fragEmptyRet_wf : Func.Wf fragEmptyRet := by t_wf_reify

def namedFn : Fn := tqbe $sample_fn(%x:l, %y:w) -> (l, w) {
  %y64 =l extsw %y
  %s =l add %x, %y64
  %p =(l,w) mkpair %s, %y
  %s2, %y2 = unpair %p
  ret %s2, %y2
}

theorem namedFn_wf : Fn.Wf namedFn := by t_wf_reify

tqbe_def tqbeDefFn : Func [i64] [i64] := tqbe(%x:l) -> l {
  %y =l neg %x
  %z =l not %y
  %q, %r =l subb %z, %x, false
  %m =b feqd imm ⟨0x0000000000000000#64⟩, imm ⟨0x0000000000000000#64⟩
  %out =l select %m, %q, 0
  %d =l udiv %out, 3
  %rem =l srem %d, 5
  %z0 =l udiv0 %rem, %x
  %s0 =l sdiv0 %z0, %x
  %sx =l extsb 7:i8
  %res =l add %s0, %sx
  ret %res
}

theorem tqbeDefFn_wf : Func.Wf tqbeDefFn := by t_wf_reify

/-! ## 5. Scaling acceptance test: executable `def` 2000-instruction function in `tqbe` notation -/

meta section
open Lean Elab Command in
set_option maxRecDepth 16384 in
run_cmd do
  let mut lines := #["def sl2000 : Func [i64] [i64] := tqbe(%a:l) -> l {"]
  let mut cur := "a"
  for i in [0:2000] do
    let nxt := s!"x{i}"
    lines := lines.push s!"  %{nxt} =l add %{cur}, %a"
    cur := nxt
  lines := lines.push s!"  ret %{cur}"
  lines := lines.push "}"
  let src := "\n".intercalate lines.toList
  match Parser.runParserCategory (← getEnv) `command src "<gen_tqbe_sl>" with
  | .ok stx => elabCommand stx
  | .error e => throwError e
end

theorem sl2000_wf : Func.Wf sl2000 := by t_wf_reify
theorem sl2000_check : Func.checkTFlat sl2000 = true := by t_kernel_rfl

/-! ## 6. Regression & negative elaboration tests (`#guard_msgs`) -/

def storePairImm : Func [i64] [] := tqbe(%p:l) -> () {
  store (1:l, 2:w), %p
  ret
}
theorem storePairImm_wf : Func.Wf storePairImm := by t_wf_reify

def loadLhsTyped : Func [i64] [i64] := tqbe(%p:l) -> l {
  %x:l = load %p
  ret %x
}
theorem loadLhsTyped_wf : Func.Wf loadLhsTyped := by t_wf_reify

def loopBrkNoParens : Func [i64] [i64] := tqbe(%n:l) -> l {
  loop (%i:l = 0) -> @done {
    %z =b ceql %i, %n
    check %z else break
    %i' =l add %i, 1
    continue(%i')
  }
  ret %n
}
theorem loopBrkNoParens_wf : Func.Wf loopBrkNoParens := by t_wf_reify

def shadowUseHelper {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (lbl : L []) (v : V i64) (k : Expr V L rs) : Expr V L rs :=
  Expr.jnz (Arg.var v |> fun _ => Arg.imm true) k (Expr.jump lbl ())

def shadowContHelper {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (lbl : L []) (v : V i64) (k : V i64 → Expr V L rs) : Expr V L rs :=
  Expr.jnz (Arg.imm true) (k v) (Expr.jump lbl ())

def shadowCollision : Func [i64] [i64] := tqbe(%foo:l) -> l {
  @foo() { ret 0 }
  {
    use shadowUseHelper(@foo, %foo)
    %r:l <- shadowContHelper(@foo, %foo)
    ret %r
  }
}
theorem shadowCollision_wf : Func.Wf shadowCollision := by t_wf_reify

def bitcastSym (n m : Nat) :
    Func [Ty.pair (Ty.bits n) (Ty.bits m)] [Ty.pair (Ty.bits m) (Ty.bits n)] :=
  tqbe(%x:pair (bits ⟨n⟩) (bits ⟨m⟩)) -> pair (bits ⟨m⟩) (bits ⟨n⟩) {
    %y =pair (bits ⟨m⟩) (bits ⟨n⟩) bitcast %x
    ret %y
  }
theorem bitcastSym_wf (n m : Nat) : Func.Wf (bitcastSym n m) := by t_wf_tac

/-! ### Nested loop label roles (`break`/`continue @L`), `rfl` parity, and `Func.wp` semantics -/

def nestedLoopAnon : Func [i64] [i64] := tqbe(%n:l) -> l {
  %r:l <- loop @o(%i:l = 0) {
    %s:l <- loop @inr(%j:l = %i) {
      %z =b ceql %j, %n
      check %z else break(%j)
      continue(%n)
    }
    %c =b ceql %s, 0
    check %c else break(%s)
    continue(%s)
  }
  ret %r
}

theorem nestedLoopAnon_eq_hand : nestedLoopAnon = fun _ _ (n, _) =>
  Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun (r, _) => .ret (.var r, ())) .nil)
    fun (obrk, _) =>
      Expr.group (sig := [[i64]]) (fun (o, _) => Blocks.cons (fun (i, _) =>
        Expr.group (sig := [[i64]])
          (fun _ => Blocks.cons (fun (s, _) =>
            .let_ (op2 (.eq i64) (.var s) (.imm 0)) fun (c, _) =>
            .jnz (.var c) (.jump o (.var s, ())) (.jump obrk (.var s, ()))) .nil)
          fun (ibrk, _) =>
            Expr.group (sig := [[i64]]) (fun (inr, _) => Blocks.cons (fun (j, _) =>
              .let_ (op2 (.eq i64) (.var j) (.var n)) fun (z, _) =>
              .jnz (.var z) (.jump inr (.var n, ())) (.jump ibrk (.var j, ()))) .nil)
              fun (inr, _) => .jump inr (.var i, ())) .nil)
        fun (o, _) => .jump o (.imm 0, ()) := rfl

theorem nestedLoopAnon_wf : Func.Wf nestedLoopAnon := by t_wf_reify
theorem nestedLoopAnon_check : Func.checkTFlat nestedLoopAnon = true := by decide

def nestedLoopNamed : Func [i64] [i64] := tqbe(%n:l) -> l {
  loop @outer(%i:l = 0, %acc:l = 0) -> @done(%res:l) {
    %done0 =b ceql %i, %n
    jnz %done0, { break @done(%acc) }, {
      loop @inner(%j:l = 0, %s:l = %acc) {
        %done1 =b ceql %j, %i
        jnz %done1, {
          %i' =l add %i, 1
          continue @outer(%i', %s)
        }, {
          %s' =l add %s, 1
          %j' =l add %j, 1
          continue @inner(%j', %s')
        }
      }
    }
  }
  ret %res
}

theorem nestedLoopNamed_eq_hand : nestedLoopNamed = fun _ _ (n, _) =>
  Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun (res, _) => .ret (.var res, ())) .nil)
    fun (done, _) =>
      Expr.group (sig := [[i64, i64]]) (fun (outer, _) => Blocks.cons (fun (i, acc, _) =>
        .let_ (op2 (.eq i64) (.var i) (.var n)) fun (done0, _) =>
        .jnz (.var done0) (.jump done (.var acc, ()))
          (Expr.group (sig := [[i64, i64]]) (fun (inner, _) => Blocks.cons (fun (j, s, _) =>
            .let_ (op2 (.eq i64) (.var j) (.var i)) fun (done1, _) =>
            .jnz (.var done1)
              (.let_ (op2 (.add i64) (.var i) (.imm 1)) fun (i', _) =>
                .jump outer (.var i', .var s, ()))
              (.let_ (op2 (.add i64) (.var s) (.imm 1)) fun (s', _) =>
               .let_ (op2 (.add i64) (.var j) (.imm 1)) fun (j', _) =>
               .jump inner (.var j', .var s', ()))) .nil)
            fun (inner, _) => .jump inner (.imm 0, .var acc, ()))) .nil)
        fun (outer, _) => .jump outer (.imm 0, .imm 0, ()) := rfl

theorem nestedLoopNamed_wf : Func.Wf nestedLoopNamed := by t_wf_reify
theorem nestedLoopNamed_check : Func.checkTFlat nestedLoopNamed = true := by decide

theorem nestedLoopNamed_three (Γ : Env) (X : XPost) (m : Mem 64) :
    Func.wp Γ nestedLoopNamed (3#64, ()) m (fun (r, ()) m' => r = 3#64 ∧ m' = m) X := by
  simp only [Func.wp, nestedLoopNamed, wp]
  intro JsDone hcDone
  simp only [Closed, and_true] at hcDone
  have hDone : JsDone.1 (3#64, ()) m := by
    refine hcDone _ _ ?_
    simp only [wp_ret, vals, Arg.val_var]
    exact ⟨trivial, trivial⟩
  intro JsOuter hcOuter
  simp only [Closed, and_true] at hcOuter
  have step3 : JsOuter.1 (3#64, 3#64, ()) m := by
    refine hcOuter _ _ ?_
    simp only [wp_let, Op.wp, wp_jnz, wp_jump, OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true,
      ↓reduceIte, liftCmp, CmpOp.evalBits, cast_eq, vals, Arg.val_var]
    exact ⟨fun _ => hDone, fun h => absurd h (by decide)⟩
  have step2 : JsOuter.1 (2#64, 1#64, ()) m := by
    refine hcOuter _ _ ?_
    simp only [wp_let, Op.wp, wp_jnz, wp_jump, OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true,
      ↓reduceIte, liftCmp, CmpOp.evalBits, cast_eq, vals, Arg.val_var]
    refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
    simp only [wp]
    intro JsInner hcInner
    simp only [Closed, and_true] at hcInner
    have in2 : JsInner.1 (2#64, 3#64, ()) m := by
      refine hcInner _ _ ?_
      simp only [wp_let, Op.wp, wp_jnz, wp_jump, OpCode.wp_cmp, OpCode.wp_add, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte, liftCmp, lift2, CmpOp.evalBits, cast_eq, vals,
        Arg.val_var, Arg.val_imm]
      refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      simpa [show (2#64 + 1#64 : BitVec 64) = 3#64 by decide] using step3
    have in1 : JsInner.1 (1#64, 2#64, ()) m := by
      refine hcInner _ _ ?_
      simp only [wp_let, Op.wp, wp_jnz, wp_jump, OpCode.wp_cmp, OpCode.wp_add, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte, liftCmp, lift2, CmpOp.evalBits, cast_eq, vals,
        Arg.val_var, Arg.val_imm]
      refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
      simpa [show (2#64 + 1#64 : BitVec 64) = 3#64 by decide,
             show (1#64 + 1#64 : BitVec 64) = 2#64 by decide] using in2
    have in0 : JsInner.1 (0#64, 1#64, ()) m := by
      refine hcInner _ _ ?_
      simp only [wp_let, Op.wp, wp_jnz, wp_jump, OpCode.wp_cmp, OpCode.wp_add, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte, liftCmp, lift2, CmpOp.evalBits, cast_eq, vals,
        Arg.val_var, Arg.val_imm]
      refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
      simpa [show (1#64 + 1#64 : BitVec 64) = 2#64 by decide,
             show (0#64 + 1#64 : BitVec 64) = 1#64 by decide] using in1
    simpa [wp_jump, vals, Arg.val_var, Arg.val_imm] using in0
  have step1 : JsOuter.1 (1#64, 0#64, ()) m := by
    refine hcOuter _ _ ?_
    simp only [wp_let, Op.wp, wp_jnz, wp_jump, OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true,
      ↓reduceIte, liftCmp, CmpOp.evalBits, cast_eq, vals, Arg.val_var]
    refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
    simp only [wp]
    intro JsInner hcInner
    simp only [Closed, and_true] at hcInner
    have in1 : JsInner.1 (1#64, 1#64, ()) m := by
      refine hcInner _ _ ?_
      simp only [wp_let, Op.wp, wp_jnz, wp_jump, OpCode.wp_cmp, OpCode.wp_add, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte, liftCmp, lift2, CmpOp.evalBits, cast_eq, vals,
        Arg.val_var, Arg.val_imm]
      refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      simpa [show (1#64 + 1#64 : BitVec 64) = 2#64 by decide] using step2
    have in0 : JsInner.1 (0#64, 0#64, ()) m := by
      refine hcInner _ _ ?_
      simp only [wp_let, Op.wp, wp_jnz, wp_jump, OpCode.wp_cmp, OpCode.wp_add, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte, liftCmp, lift2, CmpOp.evalBits, cast_eq, vals,
        Arg.val_var, Arg.val_imm]
      refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
      simpa [show (0#64 + 1#64 : BitVec 64) = 1#64 by decide] using in1
    simpa [wp_jump, vals, Arg.val_var, Arg.val_imm] using in0
  have step0 : JsOuter.1 (0#64, 0#64, ()) m := by
    refine hcOuter _ _ ?_
    simp only [wp_let, Op.wp, wp_jnz, wp_jump, OpCode.wp_cmp, Ty.hasFloat, Bool.false_eq_true,
      ↓reduceIte, liftCmp, CmpOp.evalBits, cast_eq, vals, Arg.val_var]
    refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
    simp only [wp]
    intro JsInner hcInner
    simp only [Closed, and_true] at hcInner
    have in0 : JsInner.1 (0#64, 0#64, ()) m := by
      refine hcInner _ _ ?_
      simp only [wp_let, Op.wp, wp_jnz, wp_jump, OpCode.wp_cmp, OpCode.wp_add, Ty.hasFloat,
        Bool.false_eq_true, ↓reduceIte, liftCmp, lift2, CmpOp.evalBits, cast_eq, vals,
        Arg.val_var, Arg.val_imm]
      refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      simpa [show (0#64 + 1#64 : BitVec 64) = 1#64 by decide] using step1
    simpa [wp_jump, vals, Arg.val_var, Arg.val_imm] using in0
  simpa [wp_jump, vals, Arg.val_imm] using step0

def nestedShadowBreak : Func [i64] [i64] := tqbe(%n:l) -> l {
  loop @outer(%i:l = %n) -> @done(%x:l) {
    loop @inner(%j:l = %i) -> @done(%y:l) {
      break @done(%j)
    }
    break @done(%y)
  }
  ret %x
}

theorem nestedShadowBreak_eq_hand : nestedShadowBreak = fun _ _ (n, _) =>
  Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun (x, _) => .ret (.var x, ())) .nil)
    fun (outerDone, _) =>
      Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun (i, _) =>
        Expr.group (sig := [[i64]])
          (fun _ => Blocks.cons (fun (y, _) => .jump outerDone (.var y, ())) .nil)
          fun (innerDone, _) =>
            Expr.group (sig := [[i64]])
              (fun _ => Blocks.cons (fun (j, _) => .jump innerDone (.var j, ())) .nil)
              fun (inner, _) => .jump inner (.var i, ())) .nil)
        fun (outer, _) => .jump outer (.var n, ()) := rfl

theorem nestedShadowBreak_wf : Func.Wf nestedShadowBreak := by t_wf_reify

/-! ### Hygienic synthesised binders (`_cmp`, `_loop`, `_break` never pollute user scope) -/

def switchShadowCmp : Func [i64, Ty.bool] [Ty.bool] := tqbe(%x:l, %_cmp:b) -> b {
  switch %x {
    5 => { ret %_cmp },
    _ => { ret false }
  }
}

theorem switchShadowCmp_eq_hand : switchShadowCmp = fun _ _ (x, _cmp, _) =>
  .let_ (op2 (.eq i64) (.var x) (.imm 5)) fun (g, _) =>
  .jnz (.var g) (.ret (.var _cmp, ())) (.ret (.imm false, ())) := rfl

theorem switchShadowCmp_wf : Func.Wf switchShadowCmp := by t_wf_reify
theorem switchShadowCmp_check : Func.checkTFlat switchShadowCmp = true := by decide

def switchScrutCmp : Func [Ty.bool] [i64] := tqbe(%_cmp:b) -> l {
  switch %_cmp {
    false => { ret 1 },
    true => { ret 2 },
    _ => { ret 3 }
  }
}

theorem switchScrutCmp_eq_hand : switchScrutCmp = fun _ _ (s, _) =>
  .let_ (op2 (.eq .bool) (.var s) (.imm false)) fun (g1, _) =>
  .jnz (.var g1) (.ret (.imm 1, ()))
    (.let_ (op2 (.eq .bool) (.var s) (.imm true)) fun (g2, _) =>
      .jnz (.var g2) (.ret (.imm 2, ())) (.ret (.imm 3, ()))) := rfl

theorem switchScrutCmp_wf : Func.Wf switchScrutCmp := by t_wf_reify
theorem switchScrutCmp_check : Func.checkTFlat switchScrutCmp = true := by decide

def userLoopLabel : Func [i64] [i64] := tqbe(%n:l) -> l {
  @_loop(%v:l) { ret %v }
  {
    loop (%i:l = %n) {
      jmp @_loop(%i)
    }
  }
}

theorem userLoopLabel_eq_hand : userLoopLabel = fun _ _ (n, _) =>
  Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun (v, _) => .ret (.var v, ())) .nil)
    fun (uLoop, _) =>
      Expr.group (sig := [[i64]])
        (fun _ => Blocks.cons (fun (i, _) => .jump uLoop (.var i, ())) .nil)
        fun (lp, _) => .jump lp (.var n, ()) := rfl

theorem userLoopLabel_wf : Func.Wf userLoopLabel := by t_wf_reify
theorem userLoopLabel_check : Func.checkTFlat userLoopLabel = true := by decide

def userBreakLabel : Func [i64] [i64] := tqbe(%n:l) -> l {
  @_break(%v:l) { ret %v }
  {
    %r:l <- loop (%i:l = %n) {
      jmp @_break(%i)
    }
    ret %r
  }
}

theorem userBreakLabel_eq_hand : userBreakLabel = fun _ _ (n, _) =>
  Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun (v, _) => .ret (.var v, ())) .nil)
    fun (uBreak, _) =>
      Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun (r, _) => .ret (.var r, ())) .nil)
        fun _ =>
          Expr.group (sig := [[i64]])
            (fun _ => Blocks.cons (fun (i, _) => .jump uBreak (.var i, ())) .nil)
            fun (lp, _) => .jump lp (.var n, ()) := rfl

theorem userBreakLabel_wf : Func.Wf userBreakLabel := by t_wf_reify
theorem userBreakLabel_check : Func.checkTFlat userBreakLabel = true := by decide

/-! ### Immediate boundary checks, `%_` loop parameter, and defaultless `switch` -/

def immBoundaries : Func [Ty.bits 8, i32, i64] [Ty.bits 8, i32, i64] :=
  tqbe(%a:i8, %b:w, %c:l) -> (i8, w, l) {
    %x =i8 add %a, -128
    %y =i8 add %x, 255
    %z =w add %b, 4294967295
    %w =w add %z, -2147483648
    %t =l ternlog %c, %c, %c, 255
    switch %y {
      -128 => { ret %y, %w, %t },
      255 => { ret 0, %w, %t },
      _ => { ret 1, %w, %t }
    }
  }

theorem immBoundaries_wf : Func.Wf immBoundaries := by t_wf_reify
theorem immBoundaries_check : Func.checkTFlat immBoundaries = true := by decide

def loopWildcardParam : Func [i64] [i64] := tqbe(%n:l) -> l {
  loop (%_:l = 0, %i:l = %n) {
    %done =b ceql %i, 0
    jnz %done, { ret %i }, {
      %i' =l sub %i, 1
      continue(99, %i')
    }
  }
}

theorem loopWildcardParam_eq_hand : loopWildcardParam = fun _ _ (n, _) =>
  Expr.group (sig := [[i64, i64]])
    (fun (lp, _) => Blocks.cons (fun (_, i, _) =>
      .let_ (op2 (.eq i64) (.var i) (.imm 0)) fun (done, _) =>
      .jnz (.var done) (.ret (.var i, ()))
        (.let_ (op2 (.sub i64) (.var i) (.imm 1)) fun (i', _) =>
          .jump lp (.imm 99, .var i', ()))) .nil)
    fun (lp, _) => .jump lp (.imm 0, .var n, ()) := rfl

theorem loopWildcardParam_wf : Func.Wf loopWildcardParam := by t_wf_reify
theorem loopWildcardParam_check : Func.checkTFlat loopWildcardParam = true := by decide

def switchNoDefault : Func [Ty.bool] [i64] := tqbe(%b:b) -> l {
  switch %b {
    true => { ret 1 },
    false => { ret 0 }
  }
}

theorem switchNoDefault_eq_hand : switchNoDefault = fun _ _ (b, _) =>
  .let_ (op2 (.eq .bool) (.var b) (.imm true)) fun (c1, _) =>
  .jnz (.var c1) (.ret (.imm 1, ()))
    (.let_ (op2 (.eq .bool) (.var b) (.imm false)) fun (c2, _) =>
      .jnz (.var c2) (.ret (.imm 0, ())) .hlt) := rfl

theorem switchNoDefault_wf : Func.Wf switchNoDefault := by t_wf_reify
theorem switchNoDefault_check : Func.checkTFlat switchNoDefault = true := by decide

def floatImmForms : Func [i64, f64, v4f32] [f64, v4f32] :=
  tqbe(%p:l, %x:d, %vf:v4f32) -> (d, v4f32) {
    %y =d fadd %x, imm ⟨0x3ff8000000000000#64⟩ : d
    store imm ⟨0x0000000000000000#64⟩ : d, %p
    store splat imm ⟨0x3f800000#32⟩ : v4f32, %p
    %z =v4f32 fmul %vf,
      [imm ⟨0x3f800000#32⟩, imm ⟨0x40000000#32⟩, imm ⟨0x40400000#32⟩, imm ⟨0x40800000#32⟩]
    ret %y, %z
  }

theorem floatImmForms_wf : Func.Wf floatImmForms := by t_wf_reify
theorem floatImmForms_check : Func.checkTFlat floatImmForms = true := by decide

def bitsSymZero (n : Nat) : Func [Ty.bits n] [Ty.bits n] :=
  tqbe(%x:bits ⟨n⟩) -> bits ⟨n⟩ {
    %y =bits ⟨n⟩ add %x, 0
    ret %y
  }

theorem bitsSymZero_wf (n : Nat) : Func.Wf (bitsSymZero n) := by t_wf_tac

def nestedBreakOuter : Func [i64] [i64] := tqbe(%n:l) -> l {
  loop @outer(%i:l = 0) -> @done(%r:l) {
    loop @inner(%j:l = %i) {
      %c =b ceql %j, %n
      jnz %c, { break @done(%j) }, {
        %j' =l add %j, 1
        continue @inner(%j')
      }
    }
  }
  ret %r
}

theorem nestedBreakOuter_eq_hand : nestedBreakOuter = fun _ _ (n, _) =>
  Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun (r, _) => .ret (.var r, ())) .nil)
    fun (done, _) =>
      Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun (i, _) =>
        Expr.group (sig := [[i64]]) (fun (inner, _) => Blocks.cons (fun (j, _) =>
          .let_ (op2 (.eq i64) (.var j) (.var n)) fun (c, _) =>
          .jnz (.var c) (.jump done (.var j, ()))
            (.let_ (op2 (.add i64) (.var j) (.imm 1)) fun (j', _) =>
              .jump inner (.var j', ()))) .nil)
          fun (inner, _) => .jump inner (.var i, ())) .nil)
        fun (outer, _) => .jump outer (.imm 0, ()) := rfl

theorem nestedBreakOuter_wf : Func.Wf nestedBreakOuter := by t_wf_reify
theorem nestedBreakOuter_check : Func.checkTFlat nestedBreakOuter = true := by decide

def loopInitLeanCap {V : Ty → Type} {L : List Ty → Type} (done : V i64) : Expr V L [i64] :=
  tqbe {
    loop @lp(%i:l = ⟨Arg.var done⟩) -> @done(%r:l) {
      break(%i)
    }
    ret %r
  }

theorem loopInitLeanCap_eq_hand {V : Ty → Type} {L : List Ty → Type} (done : V i64) :
    loopInitLeanCap (V := V) (L := L) done =
      Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun (r, _) => .ret (.var r, ())) .nil)
        fun (brk, _) =>
          Expr.group (sig := [[i64]])
            (fun _ => Blocks.cons (fun (i, _) => .jump brk (.var i, ())) .nil)
            fun (lp, _) => .jump lp (.var done, ()) := rfl

def switchNestedCmp : Func [i64, Ty.bool] [Ty.bool] := tqbe(%x:l, %_cmp:b) -> b {
  switch %x {
    1 => {
      switch %_cmp {
        true => { ret %_cmp },
        false => { ret false }
      }
    },
    _ => { ret %_cmp }
  }
}

theorem switchNestedCmp_eq_hand : switchNestedCmp = fun _ _ (x, _cmp, _) =>
  .let_ (op2 (.eq i64) (.var x) (.imm 1)) fun (g1, _) =>
  .jnz (.var g1)
    (.let_ (op2 (.eq .bool) (.var _cmp) (.imm true)) fun (g2, _) =>
      .jnz (.var g2) (.ret (.var _cmp, ()))
        (.let_ (op2 (.eq .bool) (.var _cmp) (.imm false)) fun (g3, _) =>
          .jnz (.var g3) (.ret (.imm false, ())) .hlt))
    (.ret (.var _cmp, ())) := rfl

theorem switchNestedCmp_wf : Func.Wf switchNestedCmp := by t_wf_reify

def immBoundaries64 : Func [i64, Ty.bits 1] [i64, Ty.bits 1] :=
  tqbe(%x:l, %y:bits 1) -> (l, bits 1) {
    %a =l add %x, 18446744073709551615
    %b =l add %a, -9223372036854775808
    %c =bits 1 add %y, -1
    %d =bits 1 add %c, 1
    ret %b, %d
  }

theorem immBoundaries64_wf : Func.Wf immBoundaries64 := by t_wf_reify
theorem immBoundaries64_check : Func.checkTFlat immBoundaries64 = true := by decide

/-! ### Negative `#guard_msgs` diagnostic tests for `tqbe` notation -/

/-- error: tqbe: `break @outerLoop` targets loop header @outerLoop, not a loop break label (use `continue @outerLoop`) -/
#guard_msgs in
example : Func [i64] [i64] := tqbe(%n:l) -> l {
  loop @outerLoop(%i:l = 0) -> @doneBreak(%r:l) {
    loop @inner(%j:l = %i) {
      break @outerLoop(%j)
    }
  }
  ret %r
}

/-- error: tqbe: `continue @doneBreak` targets loop break label @doneBreak, not a loop header (use `break @doneBreak`) -/
#guard_msgs in
example : Func [i64] [i64] := tqbe(%n:l) -> l {
  loop @outerLoop(%i:l = 0) -> @doneBreak(%r:l) {
    continue @doneBreak(%i)
  }
  ret %r
}

/-- error: tqbe: `break @normalBlk` targets non-loop label @normalBlk (use `jmp @normalBlk`) -/
#guard_msgs in
example : Func [i64] [i64] := tqbe(%n:l) -> l {
  @normalBlk(%x:l) { ret %x }
  {
    loop (%i:l = %n) -> @done(%r:l) {
      break @normalBlk(%i)
    }
    ret %r
  }
}

/-- error: tqbe: `continue @normalBlk` targets non-loop label @normalBlk (use `jmp @normalBlk`) -/
#guard_msgs in
example : Func [i64] [i64] := tqbe(%n:l) -> l {
  @normalBlk(%x:l) { ret %x }
  {
    loop (%i:l = %n) {
      continue @normalBlk(%i)
    }
  }
}

/-- error: tqbe: unknown loop break label @done -/
#guard_msgs in
example : Func [i64] [i64] := tqbe(%n:l) -> l {
  loop @lp(%i:l = %n) -> @done(%r:l) {
    break @done(%i)
  }
  break @done(%r)
}

/-- error: tqbe: bare integer literal `2` is not valid for floating-point type
  f64
(use `imm ⟨...⟩`) -/
#guard_msgs in
example : Func [f64] [f64] := tqbe(%x:d) -> d {
  %y =d fmul %x, 2
  ret %y
}

/-- error: tqbe: bare integer literal `0` is not valid for floating-point type
  f64
(use `imm ⟨...⟩`) -/
#guard_msgs in
example : Func [f64] [f64] := tqbe(%x:d) -> d {
  %y =d fadd %x, 0
  ret %y
}

/-- error: tqbe: bare integer literal `1` is not valid for floating-point type
  Ty.vec 0 f32
(use `imm ⟨...⟩`) -/
#guard_msgs in
example : Func [v4f32] [v4f32] := tqbe(%v:v4f32) -> v4f32 {
  %y =v4f32 fadd %v, splat 1 : v4f32
  ret %y
}

/-- error: tqbe: bare integer literal `1` is not valid for floating-point type
  Ty.vec 0 f32
(use `imm ⟨...⟩`) -/
#guard_msgs in
example : Func [i64] [] := tqbe(%p:l) -> () {
  store splat 1 : v4f32, %p
  ret
}

/-- error: tqbe: integer literal 256 out of range for type
  i8
(expected < 2^8) -/
#guard_msgs in
example : Func [Ty.bits 8] [Ty.bits 8] := tqbe(%x:i8) -> i8 {
  %y =i8 add %x, 256:i8
  ret %y
}

/-- error: tqbe: negative literal -129 out of range for type
  i8
(expected 1 ≤ k ≤ 2^7) -/
#guard_msgs in
example : Func [Ty.bits 8] [Ty.bits 8] := tqbe(%x:i8) -> i8 {
  %y =i8 add %x, -129:i8
  ret %y
}

/-- error: tqbe: negative literal -0 not valid for type
  i8 -/
#guard_msgs in
example : Func [Ty.bits 8] [Ty.bits 8] := tqbe(%x:i8) -> i8 {
  %y =i8 add %x, -0:i8
  ret %y
}

/-- error: tqbe: negative literal -1 not valid for type
  Ty.bool -/
#guard_msgs in
example : Func [Ty.bool] [Ty.bool] := tqbe(%b:b) -> b {
  %y =b and %b, -1:b
  ret %y
}

/-- error: tqbe: integer literal 4294967297 out of range for type
  i32
(expected < 2^32) -/
#guard_msgs in
example : Func [i32] [i32] := tqbe(%x:w) -> w {
  %y =w add %x, 4294967297:w
  ret %y
}

/-- error: tqbe: 8-bit immediate 300 out of range (expected < 256) -/
#guard_msgs in
example : Func [i64] [i64] := tqbe(%x:l) -> l {
  %y =l ternlog %x, %x, %x, 300
  ret %y
}

/-- error: tqbe: integer literal 256 out of range for type
  Ty.bits 8
(expected < 2^8) -/
#guard_msgs in
example : Func [Ty.bits 8] [i64] := tqbe(%x:i8) -> l {
  switch %x {
    256 => { ret 1 },
    0 => { ret 2 }
  }
}

/-- error: tqbe: duplicate `switch` arm literal -/
#guard_msgs in
example : Func [Ty.bits 8] [i64] := tqbe(%x:i8) -> l {
  switch %x {
    0 => { ret 1 },
    0 => { ret 2 },
    _ => { ret 3 }
  }
}

/-- error: tqbe: duplicate `switch` arm literal -/
#guard_msgs in
example : Func [Ty.bits 8] [i64] := tqbe(%x:i8) -> l {
  switch %x {
    -1 => { ret 1 },
    255 => { ret 2 },
    _ => { ret 3 }
  }
}

/-- error: tqbe: duplicate `switch` arm literal -/
#guard_msgs in
example : Func [Ty.bool] [i64] := tqbe(%b:b) -> l {
  switch %b {
    false => { ret 1 },
    0 => { ret 2 }
  }
}

/-- error: tqbe: `switch` arm pattern must be a literal (`n`, `-n`, `true`, `false`, or `_`) -/
#guard_msgs in
example : Func [i64, i64] [i64] := tqbe(%x:l, %y:l) -> l {
  switch %x {
    %y => { ret 1 },
    _ => { ret 0 }
  }
}

/-- error: tqbe: `zext` destination width (32) cannot be smaller than source width (64) -/
#guard_msgs in
example : Func [i64] [i32] := tqbe(%x:l) -> w {
  %y =w zext %x
  ret %y
}

/-- error: tqbe: `sext` destination width (32) cannot be smaller than source width (64) -/
#guard_msgs in
example : Func [i64] [i32] := tqbe(%x:l) -> w {
  %y =w sext %x
  ret %y
}

/-- error: tqbe: `trunc` destination width (64) cannot exceed source width (32) -/
#guard_msgs in
example : Func [i32] [i64] := tqbe(%x:w) -> l {
  %y =l trunc %x
  ret %y
}

/-- error: tqbe: `extsw` destination width (8) cannot be smaller than source width (32) -/
#guard_msgs in
example : Func [i32] [Ty.bits 8] := tqbe(%x:w) -> i8 {
  %y =i8 extsw %x
  ret %y
}

/-- error: tqbe: integer literal 1 out of range for type
  Ty.bits 0
(expected < 2^0) -/
#guard_msgs in
example : Func [Ty.bits 0] [Ty.bits 0] := tqbe(%x:bits 0) -> bits 0 {
  %y =bits 0 add %x, 1
  ret %y
}

/-- error: tqbe: negative literal -1 not valid for 0-bit type
  Ty.bits 0 -/
#guard_msgs in
example : Func [Ty.bits 0] [Ty.bits 0] := tqbe(%x:bits 0) -> bits 0 {
  %y =bits 0 add %x, -1
  ret %y
}

/-- error: tqbe: integer literal 256 out of range for type
  Ty.bits (4 + 4)
(expected < 2^8) -/
#guard_msgs in
example : Func [Ty.bits 8] [Ty.bits 8] := tqbe(%x:i8) -> i8 {
  %y =bits ⟨4 + 4⟩ add %x, 256
  ret %y
}

/-- error: tqbe: `switch` arm pattern must be a literal (`n`, `-n`, `true`, `false`, or `_`) -/
#guard_msgs in
example : Func [i64] [i64] := tqbe(%x:l) -> l {
  switch %x {
    imm ⟨0#64⟩ => { ret 1 },
    _ => { ret 0 }
  }
}

/-- error: tqbe: type mismatch: expected
  i64
but got
  i32 -/
#guard_msgs in
example : Func [i64, i64] [i64, Ty.bool] := tqbe(%a:l, %b:l) -> (l, b) {
  %s:w, %c:b =l addc %a, %b, false
  ret %s, %c
}

/-- error: tqbe: type mismatch: expected
  i64
but got
  i32 -/
#guard_msgs in
example : Func [] [i64, i64] := tqbe -> (l, l) {
  %x:w, %y:w =(l, l) unpair (1, 2)
  ret %x, %y
}

/-- error: tqbe: cannot jump without arguments to symbolic label @lbl of type
  ts -/
#guard_msgs in
example {V : Ty → Type} {L : List Ty → Type} (ts : List Ty) (lbl : L ts) : Expr V L [] :=
  tqbe { jmp @lbl }

/-- error: tqbe: `switch` does not support floating-point scrutinee
  f32 -/
#guard_msgs in
example : Func [f32] [i64] := tqbe(%f:s) -> l {
  switch %f {
    0 => { ret 1 },
    _ => { ret 0 }
  }
}

/-- error: tqbe: duplicate label @a in group -/
#guard_msgs in
example : Func [] [i64] := tqbe -> l {
  @a() { ret 1 }
  @a() { ret 2 }
  { jmp @a }
}

/-- error: tqbe: duplicate binder name `%x` -/
#guard_msgs in
example : Func [i64, i64] [i64] := tqbe(%x:l, %x:l) -> l { ret %x }

/-- error: tqbe: loop label @done and break label @done cannot have the same name -/
#guard_msgs in
example : Func [i64] [i64] := tqbe(%n:l) -> l {
  loop @done(%i:l = 0) -> @done(%r:l) { break @done(%i) }
  ret %r
}

/-- error: tqbe: lane-wise immediate has 3 lane(s), expected 4 for
  v4i32 -/
#guard_msgs in
example : Func [v4i32] [v4i32] := tqbe(%v:v4i32) -> v4i32 {
  %x =v4i32 add %v, [1, 2, 3]
  ret %x
}

/-- error: tqbe: bitcast size mismatch between
  i32
and
  i64 -/
#guard_msgs in
example : Func [i32] [i64] := tqbe(%x:w) -> l {
  %y =l bitcast %x
  ret %y
}

/-- error: tqbe: `break` has no enclosing loop continuation (use `@label` or follow loop with statements) -/
#guard_msgs in
example : Func [] [i64] := tqbe -> l { break }

/-- error: tqbe: `continue` outside of a `loop` -/
#guard_msgs in
example : Func [] [i64] := tqbe -> l { continue }

/-- error: tqbe: statement after a terminator -/
#guard_msgs in
example : Func [] [i64] := tqbe -> l {
  ret 0
  ret 1
}

/-- error: tqbe: block does not end in a terminator (ret, jmp, jnz, switch, exit, hlt, loop, break, continue) -/
#guard_msgs in
example : Func [i64] [i64] := tqbe(%x:l) -> l {
  %y =l add %x, 1
}

/-- error: t_kernel_rfl: goal is not an equality
  True -/
#guard_msgs in
example : True := by t_kernel_rfl

/-- error: tqbe: `break @done` targets loop header @done, not a loop break label (use `continue @done`) -/
#guard_msgs in
example : Func [i64] [i64] := tqbe(%n:l) -> l {
  loop @outer(%i:l = 0) -> @done(%r:l) {
    loop @done(%j:l = %i) {
      break @done(%j)
    }
    ret %i
  }
  ret %r
}

/-- error: tqbe: `continue @lp` targets loop break label @lp, not a loop header (use `break @lp`) -/
#guard_msgs in
example : Func [i64] [i64] := tqbe(%n:l) -> l {
  loop @lp(%i:l = 0) {
    loop @inner(%j:l = %i) -> @lp(%r:l) {
      continue @lp(%j)
    }
    ret %r
  }
}

/-- error: tqbe: `break @done` targets non-loop label @done (use `jmp @done`) -/
#guard_msgs in
example : Func [i64] [i64] := tqbe(%n:l) -> l {
  loop @lp(%i:l = 0) -> @done(%r:l) {
    @done() { ret 0 }
    { break @done }
  }
  ret %r
}

/-- error: tqbe: unknown loop break label @_break -/
#guard_msgs in
example : Func [i64] [i64] := tqbe(%n:l) -> l {
  %r:l <- loop (%i:l = %n) {
    break @_break(%i)
  }
  ret %r
}

/-- error: tqbe: unknown loop header label @_loop -/
#guard_msgs in
example : Func [i64] [i64] := tqbe(%n:l) -> l {
  loop (%i:l = %n) {
    continue @_loop(%i)
  }
}

/-- error: tqbe: bare integer literal `1` is not valid for floating-point type
  Ty.vec k f32
(use `imm ⟨...⟩`) -/
#guard_msgs in
example (k : Nat) : Func [Ty.vec k f32] [Ty.vec k f32] :=
  tqbe(%x : vec k s) -> vec k s {
    %y =vec k s fadd %x, splat 1 : vec k s
    ret %y
  }

/-- error: tqbe: negative literal -0 not valid for type
  Ty.bits n -/
#guard_msgs in
example (n : Nat) : Func [Ty.bits n] [Ty.bits n] :=
  tqbe(%x : bits ⟨n⟩) -> bits ⟨n⟩ {
    %y =bits ⟨n⟩ add %x, -0
    ret %y
  }

/-- error: tqbe: integer literal 18446744073709551616 out of range for type
  i64
(expected < 2^64) -/
#guard_msgs in
example : Func [i64] [i64] := tqbe(%x:l) -> l {
  %y =l add %x, 18446744073709551616
  ret %y
}

/-- error: tqbe: negative literal -9223372036854775809 out of range for type
  i64
(expected 1 ≤ k ≤ 2^63) -/
#guard_msgs in
example : Func [i64] [i64] := tqbe(%x:l) -> l {
  %y =l add %x, -9223372036854775809
  ret %y
}

/-- error: tqbe: 8-bit immediate 256 out of range (expected < 256) -/
#guard_msgs in
example : Func [v4i32] [v4i32] := tqbe(%v:v4i32) -> v4i32 {
  %y =v4i32 shufd %v, 256
  ret %y
}

/-- error: tqbe: integer literal 256 out of range for type
  Ty.vec 0 i8
(expected < 2^8) -/
#guard_msgs in
example : Func [Ty.vec 2 i8] [Ty.vec 2 i8] := tqbe(%v:vec 2 i8) -> vec 2 i8 {
  %y =vec 2 i8 add %v, splat 256 : vec 2 i8
  ret %y
}

/-- error: tqbe: duplicate `switch` arm literal -/
#guard_msgs in
example : Func [Ty.bits 8] [i64] := tqbe(%x:i8) -> l {
  switch %x {
    -128 => { ret 1 },
    128 => { ret 2 }
  }
}

/-- error: tqbe: duplicate `switch` arm literal -/
#guard_msgs in
example : Func [Ty.bool] [i64] := tqbe(%b:b) -> l {
  switch %b {
    true => { ret 1 },
    1 => { ret 2 }
  }
}

/-- error: tqbe: negative literal -1 not valid for type
  Ty.bool -/
#guard_msgs in
example : Func [Ty.bool] [i64] := tqbe(%b:b) -> l {
  switch %b {
    -1 => { ret 1 }
  }
}

/-- error: tqbe: invalid bool literal 2 (expected true, false, 0, or 1) -/
#guard_msgs in
example : Func [Ty.bool] [i64] := tqbe(%b:b) -> l {
  switch %b {
    2 => { ret 1 }
  }
}

end LeanQbeTest.T.NotationTest
