module

/-
  The extensions each instruction needs.
  Every row assembles with `as -march=generic64` plus exactly its extensions, and fails
  without any one of them.
-/

import Kraken.X64.Parser
meta import Kraken.X64.Parser
import Kraken.X64.Semantics
meta import Kraken.X64.Semantics

open Kraken.X64.Parser

/-- The extensions of the single instruction `s`. -/
def featuresOf (s : String) : Option (List Feature) :=
  match parse s with
  | .ok [.instr i] => some i.features
  | _ => none

def table : List (String × List Feature) := [
  -- baseline x86-64
  ("movq %rax, %rbx", []), ("cmovzq %rax, %rbx", []), ("rep movsb", []), ("divq %rbx", []),
  ("bswapq %rax", []), ("shldq $4, %rax, %rbx", []), ("cpuid", []),
  ("adcx %rax, %rbx", [.adx]), ("adox (%rsp), %ecx", [.adx]),
  ("mulx %rax, %rbx, %rcx", [.bmi2]), ("xgetbv", [.xsave]),
  -- SSE and SSE2 are baseline
  ("movups %xmm0, %xmm1", []), ("movaps %xmm3, %xmm4", []), ("addps (%rax), %xmm5", []),
  ("subps %xmm6, %xmm7", []), ("movdqu (%rsp), %xmm0", []), ("movdqa %xmm1, 16(%rsp)", []),
  ("paddd %xmm1, %xmm2", []), ("pxor %xmm1, %xmm2", []), ("pand %xmm1, %xmm2", []),
  ("pandn %xmm15, %xmm14", []), ("psrld $7, %xmm4", []), ("pslld $3, %xmm15", []),
  ("pshufd $0x1b, %xmm5, %xmm6", []),
  ("pshufb %xmm3, %xmm4", [.ssse3]), ("palignr $8, (%rsp), %xmm7", [.ssse3]),
  ("pblendw $0xf0, %xmm8, %xmm9", [.sse4_1]),
  ("sha256rnds2 %xmm0, %xmm2, %xmm1", [.sha]), ("sha256msg1 %xmm4, %xmm5", [.sha]),
  ("sha256msg2 16(%rsp), %xmm6", [.sha]),
  -- VEX moves and floating point: AVX at 128 and 256 bits
  ("vzeroupper", [.avx]),
  ("vmovups %xmm1, %xmm2", [.avx]), ("vmovups (%rsp), %ymm15", [.avx]),
  ("vmovdqu %ymm1, 32(%rsp)", [.avx]), ("vmovdqa %ymm2, %ymm3", [.avx]),
  ("vmovdqa (%rsp), %xmm15", [.avx]), ("vshufps $0x44, %ymm5, %ymm6, %ymm7", [.avx]),
  ("vmovd %eax, %xmm15", [.avx]), ("vmovd %xmm7, (%rsp)", [.avx]), ("vmovq %rax, %xmm8", [.avx]),
  ("vmovq %xmm10, %rbx", [.avx]), ("vmovq %xmm12, %xmm13", [.avx]),
  -- the same moves as EVEX, with a register 16 to 31 or at 512 bits
  ("vmovups %xmm16, %xmm2", [.avx512f, .avx512vl]),
  ("vmovups %ymm1, %ymm31", [.avx512f, .avx512vl]), ("vmovups %zmm1, 64(%rsp)", [.avx512f]),
  ("vshufps $0xdd, 64(%rsp), %xmm8, %xmm19", [.avx512f, .avx512vl]),
  ("vshufps $0x44, %zmm5, %zmm6, %zmm7", [.avx512f]),
  ("vmovd %eax, %xmm16", [.avx512f]), ("vmovd %xmm17, %r9d", [.avx512f]),
  ("vmovq 8(%rsp), %xmm31", [.avx512f]), ("vmovq %xmm12, %xmm16", [.avx512f]),
  -- VEX integer operations: AVX at 128 bits, AVX2 at 256
  ("vpaddd %xmm1, %xmm2, %xmm3", [.avx]), ("vpaddd (%rax), %ymm5, %ymm6", [.avx, .avx2]),
  ("vpsrld $3, %xmm9, %xmm10", [.avx]), ("vpsrld $3, %ymm9, %ymm10", [.avx, .avx2]),
  ("vpslld $3, %xmm1, %xmm2", [.avx]), ("vpslld $10, %ymm1, %ymm3", [.avx, .avx2]),
  ("vpand %xmm0, %xmm1, %xmm2", [.avx]), ("vpand %ymm0, %ymm1, %ymm2", [.avx, .avx2]),
  ("vpandn (%rax), %ymm3, %ymm4", [.avx, .avx2]), ("vpor %ymm5, %ymm6, %ymm7", [.avx, .avx2]),
  ("vpxor 32(%rsp), %xmm8, %xmm15", [.avx]),
  ("vpunpckldq %xmm0, %xmm1, %xmm2", [.avx]), ("vpunpckhdq (%rax), %ymm3, %ymm4", [.avx, .avx2]),
  ("vpunpcklqdq %ymm5, %ymm6, %ymm7", [.avx, .avx2]), ("vpunpckhqdq %xmm8, %xmm9, %xmm15", [.avx]),
  ("vpshufb %xmm1, %xmm2, %xmm3", [.avx]), ("vpshufb (%rax), %ymm3, %ymm15", [.avx, .avx2]),
  ("vperm2i128 $0x31, 32(%rsp), %ymm12, %ymm13", [.avx, .avx2]),
  -- the same operations as EVEX
  ("vpaddd %xmm16, %xmm2, %xmm3", [.avx512f, .avx512vl]),
  ("vpaddd (%rax), %ymm5, %ymm16", [.avx512f, .avx512vl]),
  ("vpaddd %zmm2, %zmm3, %zmm4", [.avx512f]),
  ("vpsrld $3, %ymm29, %ymm10", [.avx512f, .avx512vl]), ("vpsrld $3, %zmm9, %zmm10", [.avx512f]),
  ("vpslld $31, %zmm4, %zmm5", [.avx512f]),
  -- the VEX shifts by an immediate have no memory source
  ("vpslld $10, (%rsp), %ymm3", [.avx512f, .avx512vl]),
  ("vpsrld $1, (%rsp), %xmm3", [.avx512f, .avx512vl]),
  ("vpsrld $1, 64(%rsp), %zmm3", [.avx512f]),
  ("vpunpckldq %xmm0, %xmm17, %xmm2", [.avx512f, .avx512vl]),
  ("vpunpcklqdq %zmm5, %zmm6, %zmm7", [.avx512f]),
  ("vpunpckhqdq 64(%rsp), %zmm8, %zmm25", [.avx512f]),
  ("vpshufb %xmm16, %xmm2, %xmm3", [.avx512f, .avx512vl, .avx512bw]),
  ("vpshufb %ymm1, %ymm2, %ymm30", [.avx512f, .avx512vl, .avx512bw]),
  ("vpshufb %zmm0, %zmm1, %zmm2", [.avx512f, .avx512bw]),
  -- EVEX only: AVX-512F, and AVX-512VL below 512 bits
  ("vmovdqu32 (%rsp), %zmm0", [.avx512f]), ("vmovdqu32 %xmm1, %xmm2", [.avx512f, .avx512vl]),
  ("vmovdqa32 %zmm1, 64(%rsp)", [.avx512f]), ("vmovdqa32 %ymm1, %ymm2", [.avx512f, .avx512vl]),
  ("vprord $7, %zmm7, %zmm8", [.avx512f]), ("vprord $7, %xmm7, %xmm8", [.avx512f, .avx512vl]),
  ("vpternlogd $0xca, %zmm11, %zmm12, %zmm13", [.avx512f]),
  ("vpternlogd $0x96, %ymm1, %ymm2, %ymm3", [.avx512f, .avx512vl]),
  ("vpermi2q %zmm10, %zmm11, %zmm12", [.avx512f]),
  ("vpermi2q %ymm10, %ymm11, %ymm12", [.avx512f, .avx512vl]),
  ("vpermi2d (%rsp), %zmm13, %zmm24", [.avx512f]),
  ("vpermi2d %xmm1, %xmm2, %xmm3", [.avx512f, .avx512vl]),
  ("vinserti64x4 $1, %ymm14, %zmm15, %zmm16", [.avx512f]),
  ("vinserti64x4 $0, 32(%rsp), %zmm17, %zmm18", [.avx512f])
]

/-- info: [] -/
#guard_msgs in
#eval table.filter fun (s, fs) => featuresOf s != some fs

/-! A processor without the extension raises #UD; the default evaluator grants every extension. -/

def runWith (hasFeature : Feature → Bool) (asm : String) : Except String UInt64 := do
  let exe := (← (parse s!"{asm}\nend:").mapError toString).fakeLayout
  let start := (Executable.labels exe).label "_start"
  let stop := (Executable.labels exe).label "end"
  let s ← exe.eval ⟨{}, start⟩ (·.pc == stop) hasFeature
  return s.data.regs.rax

#guard (runWith (fun _ => true) "_start: movq $1, %rax\nmulx %rax, %rbx, %rcx").toOption == some 1
#guard runWith (· != .bmi2) "_start: movq $1, %rax\nmulx %rax, %rbx, %rcx" matches
  .error "#UD: missing Feature.bmi2"
#guard (runWith (· != .bmi2) "_start: movq $1, %rax\naddq %rax, %rax").toOption == some 2
#guard (runWith (· != .avx512vl) "_start: vpaddd %zmm2, %zmm3, %zmm4").toOption == some 0
#guard runWith (· != .avx512vl) "_start: vpaddd %ymm2, %ymm3, %ymm16" matches
  .error "#UD: missing Feature.avx512vl"
