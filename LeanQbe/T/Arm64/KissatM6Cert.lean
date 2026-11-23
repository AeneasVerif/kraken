module

public import LeanQbe.T.MainCertInline
public import LeanQbe.T.Arm64.KissatM6Cert1
public import LeanQbe.T.Arm64.KissatM6Cert2
public import LeanQbe.T.Arm64.KissatM6Cert3
public import LeanQbe.T.Arm64.KissatM6Cert4
public import LeanQbe.T.Arm64.KissatM6Cert5
public import LeanQbe.T.Arm64.KissatM6Cert6
public import LeanQbe.T.Arm64.KissatM6Cert7
public import LeanQbe.T.Arm64.KissatM6Cert8
public import LeanQbe.T.Arm64.KissatM6Cert9
public import LeanQbe.T.Arm64.KissatM6Cert10
public import LeanQbe.T.Arm64.KissatM6Cert11
public import LeanQbe.T.Arm64.KissatM6Cert12
public import LeanQbe.T.Arm64.KissatM6Cert13
public import LeanQbe.T.Arm64.KissatM6Cert14
public import LeanQbe.T.Arm64.KissatM6Cert15
public import LeanQbe.T.Arm64.KissatM6Cert16
public import LeanQbe.T.Arm64.KissatM6Cert17
public import LeanQbe.T.Arm64.KissatM6Cert18
public import LeanQbe.T.Arm64.KissatM6Cert19
public import LeanQbe.T.Arm64.KissatM6Cert20
public import LeanQbe.T.Arm64.KissatM6Cert21
public import LeanQbe.T.Arm64.KissatM6Cert22
public import LeanQbe.T.Arm64.KissatM6Cert23
public import LeanQbe.T.Arm64.KissatM6Cert24
public import LeanQbe.T.Arm64.KissatM6Cert25
public import LeanQbe.T.Arm64.KissatM6Cert26
public import LeanQbe.T.Arm64.KissatM6Cert27
public import LeanQbe.T.Arm64.KissatM6Cert28
public import LeanQbe.T.Arm64.KissatM6Cert29
public import LeanQbe.T.Arm64.KissatM6Cert30
public import LeanQbe.T.Arm64.KissatM6Cert31
public import LeanQbe.T.Arm64.KissatM6Cert32
public import LeanQbe.T.Arm64.KissatM6Cert33
public import LeanQbe.T.Arm64.KissatM6Cert34
public import LeanQbe.T.Arm64.KissatM6Cert35
public import LeanQbe.T.Arm64.KissatM6Cert36
public import LeanQbe.T.Arm64.KissatM6Cert37
public import LeanQbe.T.Arm64.KissatM6Cert38
public import LeanQbe.T.Arm64.KissatM6Cert39
public import LeanQbe.T.Arm64.KissatM6Cert40
public import LeanQbe.T.Arm64.KissatM6Cert41
public import LeanQbe.T.Arm64.KissatM6Cert42
public import LeanQbe.T.Arm64.KissatM6Cert43
public import LeanQbe.T.Arm64.KissatM6Cert44
public import LeanQbe.T.Arm64.KissatM6Cert45
public import LeanQbe.T.Arm64.KissatM6Cert46
public import LeanQbe.T.Arm64.KissatM6Cert47
public import LeanQbe.T.Arm64.KissatM6Cert48
public import LeanQbe.T.Arm64.KissatM6Cert49
public import LeanQbe.T.Arm64.KissatM6Cert50
public import LeanQbe.T.Arm64.KissatM6Cert51
public import LeanQbe.T.Examples.Kissat.FullM6
public import LeanQbe.T.Examples.Kissat.FullM6InlPolicy
public import LeanQbe.T.Examples.Kissat.FullM6Inl
meta import Lean
meta import LeanQbe.T.Arm64.Targ
meta import LeanQbe.T.Examples.Kissat.FullM6Inl

/-!
# KissatM6 Native Compilation Certificate on AAPCS64 Arm64

Combines all `51` flat 1-tier slices (`KissatM6Cert1`..`KissatM6Cert51`) via a single-shot
`checkLinkList` proof into `m6Cert` over `LeanQbe.T.Examples.Kissat.FullM6.m6Module.optInlinePolicy
m6InlPolicy` (`382` functions).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64.KissatM6Cert

open LeanQbe.T LeanQbe.T.Arm64 LeanQbe.T.Examples.Kissat.FullM6 LeanQbe.T.Examples.Kissat.FullM6Inl
open LeanQbe.T.Examples.Kissat.FullM6InlPolicy
open LeanQbe.T.Arm64.KissatM6Cert1 LeanQbe.T.Arm64.KissatM6Cert2 LeanQbe.T.Arm64.KissatM6Cert3
open LeanQbe.T.Arm64.KissatM6Cert4 LeanQbe.T.Arm64.KissatM6Cert5 LeanQbe.T.Arm64.KissatM6Cert6
open LeanQbe.T.Arm64.KissatM6Cert7 LeanQbe.T.Arm64.KissatM6Cert8 LeanQbe.T.Arm64.KissatM6Cert9
open LeanQbe.T.Arm64.KissatM6Cert10 LeanQbe.T.Arm64.KissatM6Cert11 LeanQbe.T.Arm64.KissatM6Cert12
open LeanQbe.T.Arm64.KissatM6Cert13 LeanQbe.T.Arm64.KissatM6Cert14 LeanQbe.T.Arm64.KissatM6Cert15
open LeanQbe.T.Arm64.KissatM6Cert16 LeanQbe.T.Arm64.KissatM6Cert17 LeanQbe.T.Arm64.KissatM6Cert18
open LeanQbe.T.Arm64.KissatM6Cert19 LeanQbe.T.Arm64.KissatM6Cert20 LeanQbe.T.Arm64.KissatM6Cert21
open LeanQbe.T.Arm64.KissatM6Cert22 LeanQbe.T.Arm64.KissatM6Cert23 LeanQbe.T.Arm64.KissatM6Cert24
open LeanQbe.T.Arm64.KissatM6Cert25 LeanQbe.T.Arm64.KissatM6Cert26 LeanQbe.T.Arm64.KissatM6Cert27
open LeanQbe.T.Arm64.KissatM6Cert28 LeanQbe.T.Arm64.KissatM6Cert29 LeanQbe.T.Arm64.KissatM6Cert30
open LeanQbe.T.Arm64.KissatM6Cert31 LeanQbe.T.Arm64.KissatM6Cert32 LeanQbe.T.Arm64.KissatM6Cert33
open LeanQbe.T.Arm64.KissatM6Cert34 LeanQbe.T.Arm64.KissatM6Cert35 LeanQbe.T.Arm64.KissatM6Cert36
open LeanQbe.T.Arm64.KissatM6Cert37 LeanQbe.T.Arm64.KissatM6Cert38 LeanQbe.T.Arm64.KissatM6Cert39
open LeanQbe.T.Arm64.KissatM6Cert40 LeanQbe.T.Arm64.KissatM6Cert41 LeanQbe.T.Arm64.KissatM6Cert42
open LeanQbe.T.Arm64.KissatM6Cert43 LeanQbe.T.Arm64.KissatM6Cert44 LeanQbe.T.Arm64.KissatM6Cert45
open LeanQbe.T.Arm64.KissatM6Cert46 LeanQbe.T.Arm64.KissatM6Cert47 LeanQbe.T.Arm64.KissatM6Cert48
open LeanQbe.T.Arm64.KissatM6Cert49 LeanQbe.T.Arm64.KissatM6Cert50 LeanQbe.T.Arm64.KissatM6Cert51

private noncomputable def sufChunks51 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert51.chunks
private noncomputable def sufChunks50 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert50.chunks ++ sufChunks51
private noncomputable def sufChunks49 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert49.chunks ++ sufChunks50
private noncomputable def sufChunks48 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert48.chunks ++ sufChunks49
private noncomputable def sufChunks47 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert47.chunks ++ sufChunks48
private noncomputable def sufChunks46 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert46.chunks ++ sufChunks47
private noncomputable def sufChunks45 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert45.chunks ++ sufChunks46
private noncomputable def sufChunks44 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert44.chunks ++ sufChunks45
private noncomputable def sufChunks43 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert43.chunks ++ sufChunks44
private noncomputable def sufChunks42 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert42.chunks ++ sufChunks43
private noncomputable def sufChunks41 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert41.chunks ++ sufChunks42
private noncomputable def sufChunks40 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert40.chunks ++ sufChunks41
private noncomputable def sufChunks39 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert39.chunks ++ sufChunks40
private noncomputable def sufChunks38 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert38.chunks ++ sufChunks39
private noncomputable def sufChunks37 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert37.chunks ++ sufChunks38
private noncomputable def sufChunks36 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert36.chunks ++ sufChunks37
private noncomputable def sufChunks35 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert35.chunks ++ sufChunks36
private noncomputable def sufChunks34 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert34.chunks ++ sufChunks35
private noncomputable def sufChunks33 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert33.chunks ++ sufChunks34
private noncomputable def sufChunks32 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert32.chunks ++ sufChunks33
private noncomputable def sufChunks31 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert31.chunks ++ sufChunks32
private noncomputable def sufChunks30 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert30.chunks ++ sufChunks31
private noncomputable def sufChunks29 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert29.chunks ++ sufChunks30
private noncomputable def sufChunks28 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert28.chunks ++ sufChunks29
private noncomputable def sufChunks27 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert27.chunks ++ sufChunks28
private noncomputable def sufChunks26 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert26.chunks ++ sufChunks27
private noncomputable def sufChunks25 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert25.chunks ++ sufChunks26
private noncomputable def sufChunks24 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert24.chunks ++ sufChunks25
private noncomputable def sufChunks23 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert23.chunks ++ sufChunks24
private noncomputable def sufChunks22 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert22.chunks ++ sufChunks23
private noncomputable def sufChunks21 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert21.chunks ++ sufChunks22
private noncomputable def sufChunks20 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert20.chunks ++ sufChunks21
private noncomputable def sufChunks19 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert19.chunks ++ sufChunks20
private noncomputable def sufChunks18 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert18.chunks ++ sufChunks19
private noncomputable def sufChunks17 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert17.chunks ++ sufChunks18
private noncomputable def sufChunks16 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert16.chunks ++ sufChunks17
private noncomputable def sufChunks15 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert15.chunks ++ sufChunks16
private noncomputable def sufChunks14 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert14.chunks ++ sufChunks15
private noncomputable def sufChunks13 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert13.chunks ++ sufChunks14
private noncomputable def sufChunks12 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert12.chunks ++ sufChunks13
private noncomputable def sufChunks11 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert11.chunks ++ sufChunks12
private noncomputable def sufChunks10 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert10.chunks ++ sufChunks11
private noncomputable def sufChunks9 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert9.chunks ++ sufChunks10
private noncomputable def sufChunks8 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert8.chunks ++ sufChunks9
private noncomputable def sufChunks7 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert7.chunks ++ sufChunks8
private noncomputable def sufChunks6 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert6.chunks ++ sufChunks7
private noncomputable def sufChunks5 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert5.chunks ++ sufChunks6
private noncomputable def sufChunks4 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert4.chunks ++ sufChunks5
private noncomputable def sufChunks3 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert3.chunks ++ sufChunks4
private noncomputable def sufChunks2 :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert2.chunks ++ sufChunks3
private noncomputable def allChunks :
    List (CompiledChunk armTarget armLegalTarget [] 0) :=
  cert1.chunks ++ sufChunks2

private theorem allChunks_link :
    checkLinkList armLayout [] allChunks = true := by
  t_kernel_rfl

private theorem fns_eq51 : m6InlFns.drop 375 = chunksFns sufChunks51 := by
  have h := cert51.fns_eq
  dsimp only [slice51Mod] at h
  exact h
private theorem fns_eq50 : m6InlFns.drop 368 = chunksFns sufChunks50 := by
  have hc := cert50.fns_eq
  dsimp only [slice50Mod] at hc
  rw [sufChunks50, chunksFns_append, ← fns_eq51, ← hc]
  exact (drop_take_append_drop m6InlFns 368 7).symm
private theorem fns_eq49 : m6InlFns.drop 356 = chunksFns sufChunks49 := by
  have hc := cert49.fns_eq
  dsimp only [slice49Mod] at hc
  rw [sufChunks49, chunksFns_append, ← fns_eq50, ← hc]
  exact (drop_take_append_drop m6InlFns 356 12).symm
private theorem fns_eq48 : m6InlFns.drop 355 = chunksFns sufChunks48 := by
  have hc := cert48.fns_eq
  dsimp only [slice48Mod] at hc
  rw [sufChunks48, chunksFns_append, ← fns_eq49, ← hc]
  exact (drop_take_append_drop m6InlFns 355 1).symm
private theorem fns_eq47 : m6InlFns.drop 346 = chunksFns sufChunks47 := by
  have hc := cert47.fns_eq
  dsimp only [slice47Mod] at hc
  rw [sufChunks47, chunksFns_append, ← fns_eq48, ← hc]
  exact (drop_take_append_drop m6InlFns 346 9).symm
private theorem fns_eq46 : m6InlFns.drop 339 = chunksFns sufChunks46 := by
  have hc := cert46.fns_eq
  dsimp only [slice46Mod] at hc
  rw [sufChunks46, chunksFns_append, ← fns_eq47, ← hc]
  exact (drop_take_append_drop m6InlFns 339 7).symm
private theorem fns_eq45 : m6InlFns.drop 336 = chunksFns sufChunks45 := by
  have hc := cert45.fns_eq
  dsimp only [slice45Mod] at hc
  rw [sufChunks45, chunksFns_append, ← fns_eq46, ← hc]
  exact (drop_take_append_drop m6InlFns 336 3).symm
private theorem fns_eq44 : m6InlFns.drop 335 = chunksFns sufChunks44 := by
  have hc := cert44.fns_eq
  dsimp only [slice44Mod] at hc
  rw [sufChunks44, chunksFns_append, ← fns_eq45, ← hc]
  exact (drop_take_append_drop m6InlFns 335 1).symm
private theorem fns_eq43 : m6InlFns.drop 333 = chunksFns sufChunks43 := by
  have hc := cert43.fns_eq
  dsimp only [slice43Mod] at hc
  rw [sufChunks43, chunksFns_append, ← fns_eq44, ← hc]
  exact (drop_take_append_drop m6InlFns 333 2).symm
private theorem fns_eq42 : m6InlFns.drop 332 = chunksFns sufChunks42 := by
  have hc := cert42.fns_eq
  dsimp only [slice42Mod] at hc
  rw [sufChunks42, chunksFns_append, ← fns_eq43, ← hc]
  exact (drop_take_append_drop m6InlFns 332 1).symm
private theorem fns_eq41 : m6InlFns.drop 320 = chunksFns sufChunks41 := by
  have hc := cert41.fns_eq
  dsimp only [slice41Mod] at hc
  rw [sufChunks41, chunksFns_append, ← fns_eq42, ← hc]
  exact (drop_take_append_drop m6InlFns 320 12).symm
private theorem fns_eq40 : m6InlFns.drop 311 = chunksFns sufChunks40 := by
  have hc := cert40.fns_eq
  dsimp only [slice40Mod] at hc
  rw [sufChunks40, chunksFns_append, ← fns_eq41, ← hc]
  exact (drop_take_append_drop m6InlFns 311 9).symm
private theorem fns_eq39 : m6InlFns.drop 303 = chunksFns sufChunks39 := by
  have hc := cert39.fns_eq
  dsimp only [slice39Mod] at hc
  rw [sufChunks39, chunksFns_append, ← fns_eq40, ← hc]
  exact (drop_take_append_drop m6InlFns 303 8).symm
private theorem fns_eq38 : m6InlFns.drop 294 = chunksFns sufChunks38 := by
  have hc := cert38.fns_eq
  dsimp only [slice38Mod] at hc
  rw [sufChunks38, chunksFns_append, ← fns_eq39, ← hc]
  exact (drop_take_append_drop m6InlFns 294 9).symm
private theorem fns_eq37 : m6InlFns.drop 286 = chunksFns sufChunks37 := by
  have hc := cert37.fns_eq
  dsimp only [slice37Mod] at hc
  rw [sufChunks37, chunksFns_append, ← fns_eq38, ← hc]
  exact (drop_take_append_drop m6InlFns 286 8).symm
private theorem fns_eq36 : m6InlFns.drop 276 = chunksFns sufChunks36 := by
  have hc := cert36.fns_eq
  dsimp only [slice36Mod] at hc
  rw [sufChunks36, chunksFns_append, ← fns_eq37, ← hc]
  exact (drop_take_append_drop m6InlFns 276 10).symm
private theorem fns_eq35 : m6InlFns.drop 266 = chunksFns sufChunks35 := by
  have hc := cert35.fns_eq
  dsimp only [slice35Mod] at hc
  rw [sufChunks35, chunksFns_append, ← fns_eq36, ← hc]
  exact (drop_take_append_drop m6InlFns 266 10).symm
private theorem fns_eq34 : m6InlFns.drop 265 = chunksFns sufChunks34 := by
  have hc := cert34.fns_eq
  dsimp only [slice34Mod] at hc
  rw [sufChunks34, chunksFns_append, ← fns_eq35, ← hc]
  exact (drop_take_append_drop m6InlFns 265 1).symm
private theorem fns_eq33 : m6InlFns.drop 264 = chunksFns sufChunks33 := by
  have hc := cert33.fns_eq
  dsimp only [slice33Mod] at hc
  rw [sufChunks33, chunksFns_append, ← fns_eq34, ← hc]
  exact (drop_take_append_drop m6InlFns 264 1).symm
private theorem fns_eq32 : m6InlFns.drop 255 = chunksFns sufChunks32 := by
  have hc := cert32.fns_eq
  dsimp only [slice32Mod] at hc
  rw [sufChunks32, chunksFns_append, ← fns_eq33, ← hc]
  exact (drop_take_append_drop m6InlFns 255 9).symm
private theorem fns_eq31 : m6InlFns.drop 254 = chunksFns sufChunks31 := by
  have hc := cert31.fns_eq
  dsimp only [slice31Mod] at hc
  rw [sufChunks31, chunksFns_append, ← fns_eq32, ← hc]
  exact (drop_take_append_drop m6InlFns 254 1).symm
private theorem fns_eq30 : m6InlFns.drop 252 = chunksFns sufChunks30 := by
  have hc := cert30.fns_eq
  dsimp only [slice30Mod] at hc
  rw [sufChunks30, chunksFns_append, ← fns_eq31, ← hc]
  exact (drop_take_append_drop m6InlFns 252 2).symm
private theorem fns_eq29 : m6InlFns.drop 251 = chunksFns sufChunks29 := by
  have hc := cert29.fns_eq
  dsimp only [slice29Mod] at hc
  rw [sufChunks29, chunksFns_append, ← fns_eq30, ← hc]
  exact (drop_take_append_drop m6InlFns 251 1).symm
private theorem fns_eq28 : m6InlFns.drop 242 = chunksFns sufChunks28 := by
  have hc := cert28.fns_eq
  dsimp only [slice28Mod] at hc
  rw [sufChunks28, chunksFns_append, ← fns_eq29, ← hc]
  exact (drop_take_append_drop m6InlFns 242 9).symm
private theorem fns_eq27 : m6InlFns.drop 230 = chunksFns sufChunks27 := by
  have hc := cert27.fns_eq
  dsimp only [slice27Mod] at hc
  rw [sufChunks27, chunksFns_append, ← fns_eq28, ← hc]
  exact (drop_take_append_drop m6InlFns 230 12).symm
private theorem fns_eq26 : m6InlFns.drop 222 = chunksFns sufChunks26 := by
  have hc := cert26.fns_eq
  dsimp only [slice26Mod] at hc
  rw [sufChunks26, chunksFns_append, ← fns_eq27, ← hc]
  exact (drop_take_append_drop m6InlFns 222 8).symm
private theorem fns_eq25 : m6InlFns.drop 214 = chunksFns sufChunks25 := by
  have hc := cert25.fns_eq
  dsimp only [slice25Mod] at hc
  rw [sufChunks25, chunksFns_append, ← fns_eq26, ← hc]
  exact (drop_take_append_drop m6InlFns 214 8).symm
private theorem fns_eq24 : m6InlFns.drop 202 = chunksFns sufChunks24 := by
  have hc := cert24.fns_eq
  dsimp only [slice24Mod] at hc
  rw [sufChunks24, chunksFns_append, ← fns_eq25, ← hc]
  exact (drop_take_append_drop m6InlFns 202 12).symm
private theorem fns_eq23 : m6InlFns.drop 192 = chunksFns sufChunks23 := by
  have hc := cert23.fns_eq
  dsimp only [slice23Mod] at hc
  rw [sufChunks23, chunksFns_append, ← fns_eq24, ← hc]
  exact (drop_take_append_drop m6InlFns 192 10).symm
private theorem fns_eq22 : m6InlFns.drop 187 = chunksFns sufChunks22 := by
  have hc := cert22.fns_eq
  dsimp only [slice22Mod] at hc
  rw [sufChunks22, chunksFns_append, ← fns_eq23, ← hc]
  exact (drop_take_append_drop m6InlFns 187 5).symm
private theorem fns_eq21 : m6InlFns.drop 180 = chunksFns sufChunks21 := by
  have hc := cert21.fns_eq
  dsimp only [slice21Mod] at hc
  rw [sufChunks21, chunksFns_append, ← fns_eq22, ← hc]
  exact (drop_take_append_drop m6InlFns 180 7).symm
private theorem fns_eq20 : m6InlFns.drop 168 = chunksFns sufChunks20 := by
  have hc := cert20.fns_eq
  dsimp only [slice20Mod] at hc
  rw [sufChunks20, chunksFns_append, ← fns_eq21, ← hc]
  exact (drop_take_append_drop m6InlFns 168 12).symm
private theorem fns_eq19 : m6InlFns.drop 156 = chunksFns sufChunks19 := by
  have hc := cert19.fns_eq
  dsimp only [slice19Mod] at hc
  rw [sufChunks19, chunksFns_append, ← fns_eq20, ← hc]
  exact (drop_take_append_drop m6InlFns 156 12).symm
private theorem fns_eq18 : m6InlFns.drop 144 = chunksFns sufChunks18 := by
  have hc := cert18.fns_eq
  dsimp only [slice18Mod] at hc
  rw [sufChunks18, chunksFns_append, ← fns_eq19, ← hc]
  exact (drop_take_append_drop m6InlFns 144 12).symm
private theorem fns_eq17 : m6InlFns.drop 133 = chunksFns sufChunks17 := by
  have hc := cert17.fns_eq
  dsimp only [slice17Mod] at hc
  rw [sufChunks17, chunksFns_append, ← fns_eq18, ← hc]
  exact (drop_take_append_drop m6InlFns 133 11).symm
private theorem fns_eq16 : m6InlFns.drop 121 = chunksFns sufChunks16 := by
  have hc := cert16.fns_eq
  dsimp only [slice16Mod] at hc
  rw [sufChunks16, chunksFns_append, ← fns_eq17, ← hc]
  exact (drop_take_append_drop m6InlFns 121 12).symm
private theorem fns_eq15 : m6InlFns.drop 120 = chunksFns sufChunks15 := by
  have hc := cert15.fns_eq
  dsimp only [slice15Mod] at hc
  rw [sufChunks15, chunksFns_append, ← fns_eq16, ← hc]
  exact (drop_take_append_drop m6InlFns 120 1).symm
private theorem fns_eq14 : m6InlFns.drop 114 = chunksFns sufChunks14 := by
  have hc := cert14.fns_eq
  dsimp only [slice14Mod] at hc
  rw [sufChunks14, chunksFns_append, ← fns_eq15, ← hc]
  exact (drop_take_append_drop m6InlFns 114 6).symm
private theorem fns_eq13 : m6InlFns.drop 103 = chunksFns sufChunks13 := by
  have hc := cert13.fns_eq
  dsimp only [slice13Mod] at hc
  rw [sufChunks13, chunksFns_append, ← fns_eq14, ← hc]
  exact (drop_take_append_drop m6InlFns 103 11).symm
private theorem fns_eq12 : m6InlFns.drop 102 = chunksFns sufChunks12 := by
  have hc := cert12.fns_eq
  dsimp only [slice12Mod] at hc
  rw [sufChunks12, chunksFns_append, ← fns_eq13, ← hc]
  exact (drop_take_append_drop m6InlFns 102 1).symm
private theorem fns_eq11 : m6InlFns.drop 93 = chunksFns sufChunks11 := by
  have hc := cert11.fns_eq
  dsimp only [slice11Mod] at hc
  rw [sufChunks11, chunksFns_append, ← fns_eq12, ← hc]
  exact (drop_take_append_drop m6InlFns 93 9).symm
private theorem fns_eq10 : m6InlFns.drop 82 = chunksFns sufChunks10 := by
  have hc := cert10.fns_eq
  dsimp only [slice10Mod] at hc
  rw [sufChunks10, chunksFns_append, ← fns_eq11, ← hc]
  exact (drop_take_append_drop m6InlFns 82 11).symm
private theorem fns_eq9 : m6InlFns.drop 81 = chunksFns sufChunks9 := by
  have hc := cert9.fns_eq
  dsimp only [slice9Mod] at hc
  rw [sufChunks9, chunksFns_append, ← fns_eq10, ← hc]
  exact (drop_take_append_drop m6InlFns 81 1).symm
private theorem fns_eq8 : m6InlFns.drop 80 = chunksFns sufChunks8 := by
  have hc := cert8.fns_eq
  dsimp only [slice8Mod] at hc
  rw [sufChunks8, chunksFns_append, ← fns_eq9, ← hc]
  exact (drop_take_append_drop m6InlFns 80 1).symm
private theorem fns_eq7 : m6InlFns.drop 68 = chunksFns sufChunks7 := by
  have hc := cert7.fns_eq
  dsimp only [slice7Mod] at hc
  rw [sufChunks7, chunksFns_append, ← fns_eq8, ← hc]
  exact (drop_take_append_drop m6InlFns 68 12).symm
private theorem fns_eq6 : m6InlFns.drop 56 = chunksFns sufChunks6 := by
  have hc := cert6.fns_eq
  dsimp only [slice6Mod] at hc
  rw [sufChunks6, chunksFns_append, ← fns_eq7, ← hc]
  exact (drop_take_append_drop m6InlFns 56 12).symm
private theorem fns_eq5 : m6InlFns.drop 44 = chunksFns sufChunks5 := by
  have hc := cert5.fns_eq
  dsimp only [slice5Mod] at hc
  rw [sufChunks5, chunksFns_append, ← fns_eq6, ← hc]
  exact (drop_take_append_drop m6InlFns 44 12).symm
private theorem fns_eq4 : m6InlFns.drop 35 = chunksFns sufChunks4 := by
  have hc := cert4.fns_eq
  dsimp only [slice4Mod] at hc
  rw [sufChunks4, chunksFns_append, ← fns_eq5, ← hc]
  exact (drop_take_append_drop m6InlFns 35 9).symm
private theorem fns_eq3 : m6InlFns.drop 23 = chunksFns sufChunks3 := by
  have hc := cert3.fns_eq
  dsimp only [slice3Mod] at hc
  rw [sufChunks3, chunksFns_append, ← fns_eq4, ← hc]
  exact (drop_take_append_drop m6InlFns 23 12).symm
private theorem fns_eq2 : m6InlFns.drop 12 = chunksFns sufChunks2 := by
  have hc := cert2.fns_eq
  dsimp only [slice2Mod] at hc
  rw [sufChunks2, chunksFns_append, ← fns_eq3, ← hc]
  exact (drop_take_append_drop m6InlFns 12 11).symm
private theorem allChunks_fns_eq :
    m6InlMod.fns = chunksFns allChunks := by
  have hc := cert1.fns_eq
  dsimp only [slice1Mod] at hc
  have h1 : m6InlFns = chunksFns allChunks := by
    dsimp only [allChunks]
    rw [chunksFns_append, ← fns_eq2, ← hc]
    exact (List.take_append_drop 12 m6InlFns).symm
  exact h1

private theorem maxB51 :
    chunksMaxBound sufChunks51 ≤ 2048 :=
  cert51.maxBound_le
private theorem maxB50 : chunksMaxBound sufChunks50 ≤ 2048 := by
  rw [sufChunks50]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert50.maxBound_le maxB51
private theorem maxB49 : chunksMaxBound sufChunks49 ≤ 2048 := by
  rw [sufChunks49]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert49.maxBound_le maxB50
private theorem maxB48 : chunksMaxBound sufChunks48 ≤ 2048 := by
  rw [sufChunks48]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert48.maxBound_le maxB49
private theorem maxB47 : chunksMaxBound sufChunks47 ≤ 2048 := by
  rw [sufChunks47]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert47.maxBound_le maxB48
private theorem maxB46 : chunksMaxBound sufChunks46 ≤ 2048 := by
  rw [sufChunks46]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert46.maxBound_le maxB47
private theorem maxB45 : chunksMaxBound sufChunks45 ≤ 2048 := by
  rw [sufChunks45]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert45.maxBound_le maxB46
private theorem maxB44 : chunksMaxBound sufChunks44 ≤ 2048 := by
  rw [sufChunks44]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert44.maxBound_le maxB45
private theorem maxB43 : chunksMaxBound sufChunks43 ≤ 2048 := by
  rw [sufChunks43]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert43.maxBound_le maxB44
private theorem maxB42 : chunksMaxBound sufChunks42 ≤ 2048 := by
  rw [sufChunks42]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert42.maxBound_le maxB43
private theorem maxB41 : chunksMaxBound sufChunks41 ≤ 2048 := by
  rw [sufChunks41]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert41.maxBound_le maxB42
private theorem maxB40 : chunksMaxBound sufChunks40 ≤ 2048 := by
  rw [sufChunks40]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert40.maxBound_le maxB41
private theorem maxB39 : chunksMaxBound sufChunks39 ≤ 2048 := by
  rw [sufChunks39]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert39.maxBound_le maxB40
private theorem maxB38 : chunksMaxBound sufChunks38 ≤ 2048 := by
  rw [sufChunks38]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert38.maxBound_le maxB39
private theorem maxB37 : chunksMaxBound sufChunks37 ≤ 2048 := by
  rw [sufChunks37]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert37.maxBound_le maxB38
private theorem maxB36 : chunksMaxBound sufChunks36 ≤ 2048 := by
  rw [sufChunks36]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert36.maxBound_le maxB37
private theorem maxB35 : chunksMaxBound sufChunks35 ≤ 2048 := by
  rw [sufChunks35]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert35.maxBound_le maxB36
private theorem maxB34 : chunksMaxBound sufChunks34 ≤ 2048 := by
  rw [sufChunks34]
  simpa only [Nat.max_self] using
    chunksMaxBound_append_le cert34.maxBound_le maxB35
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

/-- Full kernel-checked cert covering all `382` functions in `m6InlMod` on AAPCS64 Arm64. -/
private noncomputable def m6InlCert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean m6InlMod [] [] 0 2048 :=
  { chunks := allChunks
    linkCheck := allChunks_link
    fns_eq := allChunks_fns_eq
    supportsAll := supportsAll_of_eq allChunks_fns_eq (supportsAll_of_chunks allChunks)
    maxBound_le := allChunks_maxBound }

/-- Full kernel-checked inlined cert over `m6Module.optInlinePolicy m6InlPolicy` on AAPCS64 Arm64,
transported in O(1) via `LinkedCert.castModule m6InlMod.eq`. -/
noncomputable def m6Cert :
    LinkedCert armTarget armLayout armLegalTarget armLabelClean
      (m6Module.optInlinePolicy m6InlPolicy) [] [] 0 2048 :=
  m6InlCert.castModule m6InlMod.eq

#print axioms m6Cert

end LeanQbe.T.Arm64.KissatM6Cert
