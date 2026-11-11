module

public import Kraken.X64.Syntax
public import Lean.ToExpr
meta import Lean.Elab.Deriving.ToExpr

@[expose] public section

/-!
The instruction-set extensions an instruction needs, as reported by `cpuid`.
The processor raises #UD on an instruction whose extension it lacks.

Baseline x86-64, which includes SSE and SSE2, needs no extension.
A list holds every flag the SDM's detection procedure checks: AVX2 also needs AVX,
and every AVX-512 group also needs AVX-512F.
-/

inductive Feature
  | ssse3 | sse4_1 | sha | xsave | adx | bmi2
  | avx | avx2 | avx512f | avx512vl | avx512bw
  deriving Repr, BEq, DecidableEq, Hashable, Lean.ToExpr

/-- xmm16-31, ymm16-31 and zmm16-31 have an EVEX encoding only. -/
def RegMm.isHigh : RegMm → Bool
  | .mm0 | .mm1 | .mm2 | .mm3 | .mm4 | .mm5 | .mm6 | .mm7
  | .mm8 | .mm9 | .mm10 | .mm11 | .mm12 | .mm13 | .mm14 | .mm15 => false
  | _ => true

def AvxReg.isHigh {w} : AvxReg w → Bool
  | .xmm r | .ymm r | .zmm r => r.isHigh

def AvxRegOrMem.isHigh {w} : AvxRegOrMem w → Bool
  | .avx r => r.isHigh
  | .mem _ => false

namespace AvxOperation

/-- Some operand is one of the registers 16 to 31. -/
def usesHighReg {w} : AvxOperation w → Bool
  | .movups d x | .vmovups d x | .movaps d x | .subps d x | .addps d x
  | .movdqu d x | .movdqa d x | .paddd d x | .pxor d x | .pand d x | .pandn d x
  | .pshufb d x | .pshufd d x _ | .palignr d x _ | .pblendw d x _ | .vmovdqu d x
  | .sha256rnds2 d x | .sha256msg1 d x | .sha256msg2 d x
  | .vmovdqu32 d x | .vmovdqa32 d x | .vprord d x _ | .vpsrld d x _ | .vpslld d x _
  | .vmovdqa d x => d.isHigh || x.isHigh
  | .psrld d _ | .pslld d _ => d.isHigh
  | .vpaddd d a b | .vpternlogd d a b _ | .vpshufb d a b | .vshufps d a b _
  | .vpermi2q d a b | .vpermi2d d a b | .vpand d a b | .vpandn d a b | .vpor d a b
  | .vpxor d a b | .vpunpckldq d a b | .vpunpckhdq d a b | .vpunpcklqdq d a b
  | .vpunpckhqdq d a b | .vperm2i128 d a b _ => d.isHigh || a.isHigh || b.isHigh
  | .vinserti64x4 d a b _ => d.isHigh || a.isHigh || b.isHigh
  | .vmovIn _ d _ | .vmovOut _ _ d => d.isHigh
  | .vmovq d x => d.isHigh || x.isHigh
  | .vzeroupper => false

/-- The EVEX encoding: AVX-512F, and AVX-512VL below 512 bits. -/
def evex (w : AvxWidth) (more : List Feature := []) : List Feature :=
  .avx512f :: (if w == .W512 then more else .avx512vl :: more)

/--
A VEX instruction that also has an EVEX form, taken at 512 bits or with a register 16 to 31.
`vex` is what the VEX form needs.
-/
def vexOrEvex {w} (op : AvxOperation w) (vex : List Feature) (more : List Feature := []) :
    List Feature :=
  if w == .W512 || op.usesHighReg then evex w more else vex

/-- Integer operations need AVX2 at 256 bits. -/
def vexInt (w : AvxWidth) : List Feature :=
  if w == .W128 then [.avx] else [.avx, .avx2]

/--
The extensions the instruction needs, for the encoding the assembler picks.
A form with no encoding (legacy SSE on ymm, `vpand` on zmm) gets those of its nearest one.
-/
def features {w} (op : AvxOperation w) : List Feature :=
  match op with
  | .movups .. | .movaps .. | .subps .. | .addps .. => []
  | .movdqu .. | .movdqa .. | .paddd .. | .pxor .. | .pand .. | .pandn .. => []
  | .psrld .. | .pslld .. | .pshufd .. => []
  | .pshufb .. | .palignr .. => [.ssse3]
  | .pblendw .. => [.sse4_1]
  | .sha256rnds2 .. | .sha256msg1 .. | .sha256msg2 .. => [.sha]
  | .vzeroupper => [.avx]
  | .vperm2i128 .. => [.avx, .avx2]
  -- `vmovd` and `vmovq` exist at 128 bits only, so EVEX needs no AVX-512VL.
  | .vmovIn .. | .vmovOut .. | .vmovq .. =>
    if w == .W512 || op.usesHighReg then [.avx512f] else [.avx]
  | .vmovups .. | .vmovdqu .. | .vmovdqa .. | .vshufps .. => op.vexOrEvex [.avx]
  -- The VEX shifts by an immediate take a register source only.
  | .vpsrld _ (.mem _) _ | .vpslld _ (.mem _) _ => evex w
  | .vpaddd .. | .vpsrld .. | .vpslld .. | .vpand .. | .vpandn .. | .vpor .. | .vpxor .. =>
    op.vexOrEvex (vexInt w)
  | .vpunpckldq .. | .vpunpckhdq .. | .vpunpcklqdq .. | .vpunpckhqdq .. =>
    op.vexOrEvex (vexInt w)
  | .vpshufb .. => op.vexOrEvex (vexInt w) [.avx512bw]
  | .vmovdqu32 .. | .vmovdqa32 .. | .vprord .. | .vpternlogd .. => evex w
  | .vpermi2q .. | .vpermi2d .. | .vinserti64x4 .. => evex w

end AvxOperation

def Operation.features {w} : Operation w → List Feature
  | .adcx .. | .adox .. => [.adx]
  | .mulx .. => [.bmi2]
  | .xgetbv => [.xsave]
  | _ => []

def Instr.features : Instr → List Feature
  | .regular _ _ op => op.features
  | .avx _ _ op => op.features
