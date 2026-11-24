module

public import LeanQbe.T.MainCertInline
public import LeanQbe.T.Amd64.KissatM5Cert1
public import LeanQbe.T.Amd64.KissatM5Cert2
public import LeanQbe.T.Amd64.KissatM5Cert3
public import LeanQbe.T.Amd64.KissatM5Cert4
public import LeanQbe.T.Amd64.KissatM5Cert5
public import LeanQbe.T.Amd64.KissatM5Cert6
public import LeanQbe.T.Amd64.KissatM5Cert7
public import LeanQbe.T.Amd64.KissatM5Cert8
public import LeanQbe.T.Amd64.KissatM5Cert9
public import LeanQbe.T.Amd64.KissatM5Cert10
public import LeanQbe.T.Amd64.KissatM5Cert11
public import LeanQbe.T.Amd64.KissatM5Cert12
public import LeanQbe.T.Amd64.KissatM5Cert13
public import LeanQbe.T.Amd64.KissatM5Cert14
public import LeanQbe.T.Amd64.KissatM5Cert15
public import LeanQbe.T.Amd64.KissatM5Cert16
public import LeanQbe.T.Amd64.KissatM5Cert17
public import LeanQbe.T.Amd64.KissatM5Cert18
public import LeanQbe.T.Amd64.KissatM5Cert19
public import LeanQbe.T.Amd64.KissatM5Cert20
public import LeanQbe.T.Amd64.KissatM5Cert21
public import LeanQbe.T.Amd64.KissatM5Cert22
public import LeanQbe.T.Amd64.KissatM5Cert23
public import LeanQbe.T.Amd64.KissatM5Cert24
public import LeanQbe.T.Amd64.KissatM5Cert25
public import LeanQbe.T.Amd64.KissatM5Cert26
public import LeanQbe.T.Amd64.KissatM5Cert27
public import LeanQbe.T.Amd64.KissatM5Cert28
public import LeanQbe.T.Amd64.KissatM5Cert29
public import LeanQbe.T.Amd64.KissatM5Cert30
public import LeanQbe.T.Amd64.KissatM5Cert31
public import LeanQbe.T.Amd64.KissatM5Cert32
public import LeanQbe.T.Amd64.KissatM5Cert33
public import LeanQbe.T.Amd64.KissatM5Cert34
public import LeanQbe.T.Examples.Kissat.FullM5
public import LeanQbe.T.Examples.Kissat.FullM5InlB5
meta import Lean
meta import LeanQbe.T.Amd64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM5InlB5

/-!
# KissatM5 Native Compilation Certificate on SysV x64

Combines all `34` flat 1-tier slices (`KissatM5Cert1`..`KissatM5Cert34`) via a single-shot
`checkLinkList` proof into `m5Cert` over `LeanQbe.T.Examples.Kissat.FullM5.m5Module.optInlinePolicy
InlinePolicy.b5` (`270` functions).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64.KissatM5Cert

open LeanQbe.T LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat.FullM5
open LeanQbe.T.Examples.Kissat.FullM5InlB5
open LeanQbe.T.Amd64.KissatM5Cert1 LeanQbe.T.Amd64.KissatM5Cert2 LeanQbe.T.Amd64.KissatM5Cert3
open LeanQbe.T.Amd64.KissatM5Cert4 LeanQbe.T.Amd64.KissatM5Cert5 LeanQbe.T.Amd64.KissatM5Cert6
open LeanQbe.T.Amd64.KissatM5Cert7 LeanQbe.T.Amd64.KissatM5Cert8 LeanQbe.T.Amd64.KissatM5Cert9
open LeanQbe.T.Amd64.KissatM5Cert10 LeanQbe.T.Amd64.KissatM5Cert11 LeanQbe.T.Amd64.KissatM5Cert12
open LeanQbe.T.Amd64.KissatM5Cert13 LeanQbe.T.Amd64.KissatM5Cert14 LeanQbe.T.Amd64.KissatM5Cert15
open LeanQbe.T.Amd64.KissatM5Cert16 LeanQbe.T.Amd64.KissatM5Cert17 LeanQbe.T.Amd64.KissatM5Cert18
open LeanQbe.T.Amd64.KissatM5Cert19 LeanQbe.T.Amd64.KissatM5Cert20 LeanQbe.T.Amd64.KissatM5Cert21
open LeanQbe.T.Amd64.KissatM5Cert22 LeanQbe.T.Amd64.KissatM5Cert23 LeanQbe.T.Amd64.KissatM5Cert24
open LeanQbe.T.Amd64.KissatM5Cert25 LeanQbe.T.Amd64.KissatM5Cert26 LeanQbe.T.Amd64.KissatM5Cert27
open LeanQbe.T.Amd64.KissatM5Cert28 LeanQbe.T.Amd64.KissatM5Cert29 LeanQbe.T.Amd64.KissatM5Cert30
open LeanQbe.T.Amd64.KissatM5Cert31 LeanQbe.T.Amd64.KissatM5Cert32 LeanQbe.T.Amd64.KissatM5Cert33
open LeanQbe.T.Amd64.KissatM5Cert34

private noncomputable def sufChunks34 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert34.chunks
private noncomputable def sufChunks33 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert33.chunks ++ sufChunks34
private noncomputable def sufChunks32 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert32.chunks ++ sufChunks33
private noncomputable def sufChunks31 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert31.chunks ++ sufChunks32
private noncomputable def sufChunks30 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert30.chunks ++ sufChunks31
private noncomputable def sufChunks29 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert29.chunks ++ sufChunks30
private noncomputable def sufChunks28 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert28.chunks ++ sufChunks29
private noncomputable def sufChunks27 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert27.chunks ++ sufChunks28
private noncomputable def sufChunks26 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert26.chunks ++ sufChunks27
private noncomputable def sufChunks25 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert25.chunks ++ sufChunks26
private noncomputable def sufChunks24 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert24.chunks ++ sufChunks25
private noncomputable def sufChunks23 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert23.chunks ++ sufChunks24
private noncomputable def sufChunks22 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert22.chunks ++ sufChunks23
private noncomputable def sufChunks21 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert21.chunks ++ sufChunks22
private noncomputable def sufChunks20 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert20.chunks ++ sufChunks21
private noncomputable def sufChunks19 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert19.chunks ++ sufChunks20
private noncomputable def sufChunks18 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert18.chunks ++ sufChunks19
private noncomputable def sufChunks17 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert17.chunks ++ sufChunks18
private noncomputable def sufChunks16 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert16.chunks ++ sufChunks17
private noncomputable def sufChunks15 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert15.chunks ++ sufChunks16
private noncomputable def sufChunks14 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert14.chunks ++ sufChunks15
private noncomputable def sufChunks13 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert13.chunks ++ sufChunks14
private noncomputable def sufChunks12 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert12.chunks ++ sufChunks13
private noncomputable def sufChunks11 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert11.chunks ++ sufChunks12
private noncomputable def sufChunks10 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert10.chunks ++ sufChunks11
private noncomputable def sufChunks9 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert9.chunks ++ sufChunks10
private noncomputable def sufChunks8 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert8.chunks ++ sufChunks9
private noncomputable def sufChunks7 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert7.chunks ++ sufChunks8
private noncomputable def sufChunks6 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert6.chunks ++ sufChunks7
private noncomputable def sufChunks5 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert5.chunks ++ sufChunks6
private noncomputable def sufChunks4 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert4.chunks ++ sufChunks5
private noncomputable def sufChunks3 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert3.chunks ++ sufChunks4
private noncomputable def sufChunks2 :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert2.chunks ++ sufChunks3
private noncomputable def allChunks :
    List (CompiledChunk x64Target x64LegalTarget [] 0) :=
  cert1.chunks ++ sufChunks2

private theorem allChunks_link :
    checkLinkList x64Layout [] allChunks = true := by
  t_kernel_rfl

private theorem fns_eq34 : m5InlB5Fns.drop 260 = chunksFns sufChunks34 := by
  have h := cert34.fns_eq
  dsimp only [slice34Mod] at h
  exact h
private theorem fns_eq33 : m5InlB5Fns.drop 248 = chunksFns sufChunks33 := by
  have hc := cert33.fns_eq
  dsimp only [slice33Mod] at hc
  rw [sufChunks33, chunksFns_append, ← fns_eq34, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 248 12).symm
private theorem fns_eq32 : m5InlB5Fns.drop 237 = chunksFns sufChunks32 := by
  have hc := cert32.fns_eq
  dsimp only [slice32Mod] at hc
  rw [sufChunks32, chunksFns_append, ← fns_eq33, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 237 11).symm
private theorem fns_eq31 : m5InlB5Fns.drop 228 = chunksFns sufChunks31 := by
  have hc := cert31.fns_eq
  dsimp only [slice31Mod] at hc
  rw [sufChunks31, chunksFns_append, ← fns_eq32, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 228 9).symm
private theorem fns_eq30 : m5InlB5Fns.drop 227 = chunksFns sufChunks30 := by
  have hc := cert30.fns_eq
  dsimp only [slice30Mod] at hc
  rw [sufChunks30, chunksFns_append, ← fns_eq31, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 227 1).symm
private theorem fns_eq29 : m5InlB5Fns.drop 225 = chunksFns sufChunks29 := by
  have hc := cert29.fns_eq
  dsimp only [slice29Mod] at hc
  rw [sufChunks29, chunksFns_append, ← fns_eq30, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 225 2).symm
private theorem fns_eq28 : m5InlB5Fns.drop 224 = chunksFns sufChunks28 := by
  have hc := cert28.fns_eq
  dsimp only [slice28Mod] at hc
  rw [sufChunks28, chunksFns_append, ← fns_eq29, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 224 1).symm
private theorem fns_eq27 : m5InlB5Fns.drop 217 = chunksFns sufChunks27 := by
  have hc := cert27.fns_eq
  dsimp only [slice27Mod] at hc
  rw [sufChunks27, chunksFns_append, ← fns_eq28, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 217 7).symm
private theorem fns_eq26 : m5InlB5Fns.drop 211 = chunksFns sufChunks26 := by
  have hc := cert26.fns_eq
  dsimp only [slice26Mod] at hc
  rw [sufChunks26, chunksFns_append, ← fns_eq27, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 211 6).symm
private theorem fns_eq25 : m5InlB5Fns.drop 203 = chunksFns sufChunks25 := by
  have hc := cert25.fns_eq
  dsimp only [slice25Mod] at hc
  rw [sufChunks25, chunksFns_append, ← fns_eq26, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 203 8).symm
private theorem fns_eq24 : m5InlB5Fns.drop 198 = chunksFns sufChunks24 := by
  have hc := cert24.fns_eq
  dsimp only [slice24Mod] at hc
  rw [sufChunks24, chunksFns_append, ← fns_eq25, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 198 5).symm
private theorem fns_eq23 : m5InlB5Fns.drop 188 = chunksFns sufChunks23 := by
  have hc := cert23.fns_eq
  dsimp only [slice23Mod] at hc
  rw [sufChunks23, chunksFns_append, ← fns_eq24, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 188 10).symm
private theorem fns_eq22 : m5InlB5Fns.drop 187 = chunksFns sufChunks22 := by
  have hc := cert22.fns_eq
  dsimp only [slice22Mod] at hc
  rw [sufChunks22, chunksFns_append, ← fns_eq23, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 187 1).symm
private theorem fns_eq21 : m5InlB5Fns.drop 175 = chunksFns sufChunks21 := by
  have hc := cert21.fns_eq
  dsimp only [slice21Mod] at hc
  rw [sufChunks21, chunksFns_append, ← fns_eq22, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 175 12).symm
private theorem fns_eq20 : m5InlB5Fns.drop 174 = chunksFns sufChunks20 := by
  have hc := cert20.fns_eq
  dsimp only [slice20Mod] at hc
  rw [sufChunks20, chunksFns_append, ← fns_eq21, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 174 1).symm
private theorem fns_eq19 : m5InlB5Fns.drop 164 = chunksFns sufChunks19 := by
  have hc := cert19.fns_eq
  dsimp only [slice19Mod] at hc
  rw [sufChunks19, chunksFns_append, ← fns_eq20, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 164 10).symm
private theorem fns_eq18 : m5InlB5Fns.drop 155 = chunksFns sufChunks18 := by
  have hc := cert18.fns_eq
  dsimp only [slice18Mod] at hc
  rw [sufChunks18, chunksFns_append, ← fns_eq19, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 155 9).symm
private theorem fns_eq17 : m5InlB5Fns.drop 143 = chunksFns sufChunks17 := by
  have hc := cert17.fns_eq
  dsimp only [slice17Mod] at hc
  rw [sufChunks17, chunksFns_append, ← fns_eq18, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 143 12).symm
private theorem fns_eq16 : m5InlB5Fns.drop 133 = chunksFns sufChunks16 := by
  have hc := cert16.fns_eq
  dsimp only [slice16Mod] at hc
  rw [sufChunks16, chunksFns_append, ← fns_eq17, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 133 10).symm
private theorem fns_eq15 : m5InlB5Fns.drop 122 = chunksFns sufChunks15 := by
  have hc := cert15.fns_eq
  dsimp only [slice15Mod] at hc
  rw [sufChunks15, chunksFns_append, ← fns_eq16, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 122 11).symm
private theorem fns_eq14 : m5InlB5Fns.drop 115 = chunksFns sufChunks14 := by
  have hc := cert14.fns_eq
  dsimp only [slice14Mod] at hc
  rw [sufChunks14, chunksFns_append, ← fns_eq15, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 115 7).symm
private theorem fns_eq13 : m5InlB5Fns.drop 104 = chunksFns sufChunks13 := by
  have hc := cert13.fns_eq
  dsimp only [slice13Mod] at hc
  rw [sufChunks13, chunksFns_append, ← fns_eq14, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 104 11).symm
private theorem fns_eq12 : m5InlB5Fns.drop 94 = chunksFns sufChunks12 := by
  have hc := cert12.fns_eq
  dsimp only [slice12Mod] at hc
  rw [sufChunks12, chunksFns_append, ← fns_eq13, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 94 10).symm
private theorem fns_eq11 : m5InlB5Fns.drop 87 = chunksFns sufChunks11 := by
  have hc := cert11.fns_eq
  dsimp only [slice11Mod] at hc
  rw [sufChunks11, chunksFns_append, ← fns_eq12, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 87 7).symm
private theorem fns_eq10 : m5InlB5Fns.drop 79 = chunksFns sufChunks10 := by
  have hc := cert10.fns_eq
  dsimp only [slice10Mod] at hc
  rw [sufChunks10, chunksFns_append, ← fns_eq11, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 79 8).symm
private theorem fns_eq9 : m5InlB5Fns.drop 72 = chunksFns sufChunks9 := by
  have hc := cert9.fns_eq
  dsimp only [slice9Mod] at hc
  rw [sufChunks9, chunksFns_append, ← fns_eq10, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 72 7).symm
private theorem fns_eq8 : m5InlB5Fns.drop 65 = chunksFns sufChunks8 := by
  have hc := cert8.fns_eq
  dsimp only [slice8Mod] at hc
  rw [sufChunks8, chunksFns_append, ← fns_eq9, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 65 7).symm
private theorem fns_eq7 : m5InlB5Fns.drop 53 = chunksFns sufChunks7 := by
  have hc := cert7.fns_eq
  dsimp only [slice7Mod] at hc
  rw [sufChunks7, chunksFns_append, ← fns_eq8, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 53 12).symm
private theorem fns_eq6 : m5InlB5Fns.drop 52 = chunksFns sufChunks6 := by
  have hc := cert6.fns_eq
  dsimp only [slice6Mod] at hc
  rw [sufChunks6, chunksFns_append, ← fns_eq7, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 52 1).symm
private theorem fns_eq5 : m5InlB5Fns.drop 40 = chunksFns sufChunks5 := by
  have hc := cert5.fns_eq
  dsimp only [slice5Mod] at hc
  rw [sufChunks5, chunksFns_append, ← fns_eq6, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 40 12).symm
private theorem fns_eq4 : m5InlB5Fns.drop 30 = chunksFns sufChunks4 := by
  have hc := cert4.fns_eq
  dsimp only [slice4Mod] at hc
  rw [sufChunks4, chunksFns_append, ← fns_eq5, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 30 10).symm
private theorem fns_eq3 : m5InlB5Fns.drop 18 = chunksFns sufChunks3 := by
  have hc := cert3.fns_eq
  dsimp only [slice3Mod] at hc
  rw [sufChunks3, chunksFns_append, ← fns_eq4, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 18 12).symm
private theorem fns_eq2 : m5InlB5Fns.drop 12 = chunksFns sufChunks2 := by
  have hc := cert2.fns_eq
  dsimp only [slice2Mod] at hc
  rw [sufChunks2, chunksFns_append, ← fns_eq3, ← hc]
  exact (drop_take_append_drop m5InlB5Fns 12 6).symm
private theorem allChunks_fns_eq :
    m5InlB5Mod.fns = chunksFns allChunks := by
  have hc := cert1.fns_eq
  dsimp only [slice1Mod] at hc
  have h1 : m5InlB5Fns = chunksFns allChunks := by
    dsimp only [allChunks]
    rw [chunksFns_append, ← fns_eq2, ← hc]
    exact (List.take_append_drop 12 m5InlB5Fns).symm
  exact h1

private theorem maxB34 :
    chunksMaxBound sufChunks34 ≤ 2048 :=
  cert34.maxBound_le
private theorem maxB33 : chunksMaxBound sufChunks33 ≤ 2048 := by
  rw [sufChunks33]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert33.maxBound_le maxB34
private theorem maxB32 : chunksMaxBound sufChunks32 ≤ 2048 := by
  rw [sufChunks32]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert32.maxBound_le maxB33
private theorem maxB31 : chunksMaxBound sufChunks31 ≤ 2048 := by
  rw [sufChunks31]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert31.maxBound_le maxB32
private theorem maxB30 : chunksMaxBound sufChunks30 ≤ 2048 := by
  rw [sufChunks30]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert30.maxBound_le maxB31
private theorem maxB29 : chunksMaxBound sufChunks29 ≤ 2048 := by
  rw [sufChunks29]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert29.maxBound_le maxB30
private theorem maxB28 : chunksMaxBound sufChunks28 ≤ 2048 := by
  rw [sufChunks28]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert28.maxBound_le maxB29
private theorem maxB27 : chunksMaxBound sufChunks27 ≤ 2048 := by
  rw [sufChunks27]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert27.maxBound_le maxB28
private theorem maxB26 : chunksMaxBound sufChunks26 ≤ 2048 := by
  rw [sufChunks26]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert26.maxBound_le maxB27
private theorem maxB25 : chunksMaxBound sufChunks25 ≤ 2048 := by
  rw [sufChunks25]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert25.maxBound_le maxB26
private theorem maxB24 : chunksMaxBound sufChunks24 ≤ 2048 := by
  rw [sufChunks24]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert24.maxBound_le maxB25
private theorem maxB23 : chunksMaxBound sufChunks23 ≤ 2048 := by
  rw [sufChunks23]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert23.maxBound_le maxB24
private theorem maxB22 : chunksMaxBound sufChunks22 ≤ 2048 := by
  rw [sufChunks22]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert22.maxBound_le maxB23
private theorem maxB21 : chunksMaxBound sufChunks21 ≤ 2048 := by
  rw [sufChunks21]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert21.maxBound_le maxB22
private theorem maxB20 : chunksMaxBound sufChunks20 ≤ 2048 := by
  rw [sufChunks20]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert20.maxBound_le maxB21
private theorem maxB19 : chunksMaxBound sufChunks19 ≤ 2048 := by
  rw [sufChunks19]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert19.maxBound_le maxB20
private theorem maxB18 : chunksMaxBound sufChunks18 ≤ 2048 := by
  rw [sufChunks18]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert18.maxBound_le maxB19
private theorem maxB17 : chunksMaxBound sufChunks17 ≤ 2048 := by
  rw [sufChunks17]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert17.maxBound_le maxB18
private theorem maxB16 : chunksMaxBound sufChunks16 ≤ 2048 := by
  rw [sufChunks16]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert16.maxBound_le maxB17
private theorem maxB15 : chunksMaxBound sufChunks15 ≤ 2048 := by
  rw [sufChunks15]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert15.maxBound_le maxB16
private theorem maxB14 : chunksMaxBound sufChunks14 ≤ 2048 := by
  rw [sufChunks14]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert14.maxBound_le maxB15
private theorem maxB13 : chunksMaxBound sufChunks13 ≤ 2048 := by
  rw [sufChunks13]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert13.maxBound_le maxB14
private theorem maxB12 : chunksMaxBound sufChunks12 ≤ 2048 := by
  rw [sufChunks12]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert12.maxBound_le maxB13
private theorem maxB11 : chunksMaxBound sufChunks11 ≤ 2048 := by
  rw [sufChunks11]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert11.maxBound_le maxB12
private theorem maxB10 : chunksMaxBound sufChunks10 ≤ 2048 := by
  rw [sufChunks10]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert10.maxBound_le maxB11
private theorem maxB9 : chunksMaxBound sufChunks9 ≤ 2048 := by
  rw [sufChunks9]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert9.maxBound_le maxB10
private theorem maxB8 : chunksMaxBound sufChunks8 ≤ 2048 := by
  rw [sufChunks8]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert8.maxBound_le maxB9
private theorem maxB7 : chunksMaxBound sufChunks7 ≤ 2048 := by
  rw [sufChunks7]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert7.maxBound_le maxB8
private theorem maxB6 : chunksMaxBound sufChunks6 ≤ 2048 := by
  rw [sufChunks6]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert6.maxBound_le maxB7
private theorem maxB5 : chunksMaxBound sufChunks5 ≤ 2048 := by
  rw [sufChunks5]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert5.maxBound_le maxB6
private theorem maxB4 : chunksMaxBound sufChunks4 ≤ 2048 := by
  rw [sufChunks4]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert4.maxBound_le maxB5
private theorem maxB3 : chunksMaxBound sufChunks3 ≤ 2048 := by
  rw [sufChunks3]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert3.maxBound_le maxB4
private theorem maxB2 : chunksMaxBound sufChunks2 ≤ 2048 := by
  rw [sufChunks2]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert2.maxBound_le maxB3
private theorem allChunks_maxBound : chunksMaxBound allChunks ≤ 2048 := by
  rw [allChunks]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert1.maxBound_le maxB2

/-- Full kernel-checked cert covering all `270` functions in `m5InlB5Mod` on SysV x64. -/
private noncomputable def m5InlCert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean m5InlB5Mod [] [] 0 2048 :=
  { chunks := allChunks
    linkCheck := allChunks_link
    fns_eq := allChunks_fns_eq
    supportsAll := supportsAll_of_eq allChunks_fns_eq (supportsAll_of_chunks allChunks)
    maxBound_le := allChunks_maxBound }

/-- Full kernel-checked inlined cert over `m5Module.optInlinePolicy InlinePolicy.b5` on SysV x64,
transported in O(1) via `LinkedCert.castModule m5InlB5Mod.eq`. -/
noncomputable def m5Cert :
    LinkedCert x64Target x64Layout x64LegalTarget x64LabelClean
      (m5Module.optInlinePolicy InlinePolicy.b5) [] [] 0 2048 :=
  m5InlCert.castModule m5InlB5Mod.eq

#print axioms m5Cert

end LeanQbe.T.Amd64.KissatM5Cert
