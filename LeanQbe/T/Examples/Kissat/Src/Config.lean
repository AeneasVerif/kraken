/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Module
public import LeanQbe.T.Examples.Kissat.Src.Header
meta import LeanQbe.T.Examples.Kissat.Src.Header

/-!
# Kissat C0 Solver Configuration Presets (`Src/Config.lean`)

Mirrors upstream `kissat/src/config.c` (`basic`, `default`, `plain`, `sat`, `unsat`) and
`kissat/src/options.h` (`TARGET_*`, `STABLE_*`, `RESTARTINT_*`), unifying runtime presets
between `Plain` and `Full` without duplicating CDCL code (`Stage R2b` / `R5`):
- Exact 13-option `set_plain_options` bitmask (`bumpreasons`, `chrono`, `compact`,
  `eagersubsume`, `jumpreasons`, `otfs`, `preprocess`, `reorder`, `rephase`,
  `restartreusetrail`, `simplify`, `tumble` disabled; `stable = 2` stable-only).
- Exact `--basic` delta (`+ restart=0, reduce=0, minimize=0`), `--sat` delta
  (`target=2, restartint=50`), and `--unsat` delta (`stable=0`).
- Stored in reserved `M6HdrExt.watermarks[7]` (`M6_WM_CFG = 7ULL`, word `31`, byte `+248`),
  untouched by all `40` `Src/` solver files, with `CFG_INIT_BIT` (`1ULL << 63`) fallback so
  zero-initialized `M6HdrExt` defaults cleanly to `CFG_DEFAULT`.
- Strictly data-pure (`0` `*Proof*`/`*Spec*`/`*Lemmas*`/`*Audit*`/`Amd64`/`Arm64`/`Kraken`
  imports).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Src.Config

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Src

@[expose] public section

/-! ## 1. `M6HdrExt` Config Storage Slot & Option-Bit Constants -/

/-- Reserved `M6HdrExt.watermarks` index (`7`, word `31`, byte offset `+248`). -/
def m6WmCfg : Nat := 7

/-- Byte offset of the configuration word inside `M6HdrExt` (`248`). -/
def m6HdrOffCfg : Nat := 8 * (m6WWmBase + m6WmCfg)

/-- Upstream `config.c` preset identifiers (`0..4`). -/
def cfgIdDefault : BitVec 64 := 0#64
def cfgIdPlain : BitVec 64 := 1#64
def cfgIdBasic : BitVec 64 := 2#64
def cfgIdSat : BitVec 64 := 3#64
def cfgIdUnsat : BitVec 64 := 4#64

/-- Bit positions in the `u64` configuration flag word (`0..18`, plus init bit `63`). -/
def cfgBitBumpReasons : Nat := 0
def cfgBitChrono : Nat := 1
def cfgBitCompact : Nat := 2
def cfgBitEagerSubsume : Nat := 3
def cfgBitJumpReasons : Nat := 4
def cfgBitOtfs : Nat := 5
def cfgBitPreprocess : Nat := 6
def cfgBitReorder : Nat := 7
def cfgBitRephase : Nat := 8
def cfgBitRestartReuseTrail : Nat := 9
def cfgBitSimplify : Nat := 10
def cfgBitTumble : Nat := 11
def cfgBitStableOnly : Nat := 12
def cfgBitRestart : Nat := 13
def cfgBitReduce : Nat := 14
def cfgBitMinimize : Nat := 15
def cfgBitFocusedOnly : Nat := 16
def cfgBitTargetSat : Nat := 17
def cfgBitRestartintSat : Nat := 18
def cfgBitInit : Nat := 63

/-- Single-bit masks for the `13` `--plain` options, `3` `--basic` disables, and `--sat`/`--unsat`.
-/
def cfgFlagBumpReasons : BitVec 64 := 1#64 <<< cfgBitBumpReasons
def cfgFlagChrono : BitVec 64 := 1#64 <<< cfgBitChrono
def cfgFlagCompact : BitVec 64 := 1#64 <<< cfgBitCompact
def cfgFlagEagerSubsume : BitVec 64 := 1#64 <<< cfgBitEagerSubsume
def cfgFlagJumpReasons : BitVec 64 := 1#64 <<< cfgBitJumpReasons
def cfgFlagOtfs : BitVec 64 := 1#64 <<< cfgBitOtfs
def cfgFlagPreprocess : BitVec 64 := 1#64 <<< cfgBitPreprocess
def cfgFlagReorder : BitVec 64 := 1#64 <<< cfgBitReorder
def cfgFlagRephase : BitVec 64 := 1#64 <<< cfgBitRephase
def cfgFlagRestartReuseTrail : BitVec 64 := 1#64 <<< cfgBitRestartReuseTrail
def cfgFlagSimplify : BitVec 64 := 1#64 <<< cfgBitSimplify
def cfgFlagTumble : BitVec 64 := 1#64 <<< cfgBitTumble
def cfgFlagStableOnly : BitVec 64 := 1#64 <<< cfgBitStableOnly
def cfgFlagRestart : BitVec 64 := 1#64 <<< cfgBitRestart
def cfgFlagReduce : BitVec 64 := 1#64 <<< cfgBitReduce
def cfgFlagMinimize : BitVec 64 := 1#64 <<< cfgBitMinimize
def cfgFlagFocusedOnly : BitVec 64 := 1#64 <<< cfgBitFocusedOnly
def cfgFlagTargetSat : BitVec 64 := 1#64 <<< cfgBitTargetSat
def cfgFlagRestartintSat : BitVec 64 := 1#64 <<< cfgBitRestartintSat
def cfgFlagInit : BitVec 64 := 1#64 <<< cfgBitInit

/-- Upstream `options.h` target/stable/restartint preset values. -/
def cfgTargetDefault : BitVec 64 := 1#64
def cfgTargetSatVal : BitVec 64 := 2#64
def cfgStableUnsatVal : BitVec 64 := 0#64
def cfgStableDefaultVal : BitVec 64 := 1#64
def cfgStablePlainVal : BitVec 64 := 2#64
def cfgRestartintDefault : BitVec 64 := 1#64
def cfgRestartintSatVal : BitVec 64 := 50#64

/-- Bitmask of the `12` options disabled by `set_plain_options` (bits `0..11`). -/
def cfgPlainDisableMask : BitVec 64 := 0x0000000000000FFF#64

/-- Bitmask of all `13` options modified by `set_plain_options` (bits `0..12`). -/
def cfgPlain13Mask : BitVec 64 := 0x0000000000001FFF#64

/-- Bitmask of the `3` additional core CDCL options disabled by `--basic` (bits `13..15`). -/
def cfgBasicExtraMask : BitVec 64 := 0x000000000000E000#64

/-- Exact `config.c` `"default"` preset flags. -/
def cfgDefault : BitVec 64 := cfgFlagInit ||| cfgPlainDisableMask ||| cfgBasicExtraMask

/-- Exact `config.c` `"plain"` preset flags (`set_plain_options`: 12 off + `stable=2`). -/
def cfgPlain : BitVec 64 := cfgFlagInit ||| cfgFlagStableOnly ||| cfgBasicExtraMask

/-- Exact `config.c` `"basic"` preset flags (`plain` + `restart=0`, `reduce=0`, `minimize=0`). -/
def cfgBasic : BitVec 64 := cfgFlagInit ||| cfgFlagStableOnly

/-- Exact `config.c` `"sat"` preset flags (`default` + `target=2`, `restartint=50`). -/
def cfgSat : BitVec 64 := cfgDefault ||| cfgFlagTargetSat ||| cfgFlagRestartintSat

/-- Exact `config.c` `"unsat"` preset flags (`default` + `stable=0`). -/
def cfgUnsat : BitVec 64 := cfgDefault ||| cfgFlagFocusedOnly

/-- Test whether `flag` bit is set in a configuration word (treating uninitialized as default). -/
def cfgHasFlag (w flag : BitVec 64) : Bool :=
  let eff := if (w &&& cfgFlagInit) == 0#64 then cfgDefault else w
  (eff &&& flag) != 0#64

/-- Upstream `options.stable` (`0`, `1`, `2`) decoded from a configuration word. -/
def cfgStableVal (w : BitVec 64) : BitVec 64 :=
  if cfgHasFlag w cfgFlagStableOnly then cfgStablePlainVal
  else if cfgHasFlag w cfgFlagFocusedOnly then cfgStableUnsatVal
  else cfgStableDefaultVal

/-- Upstream `options.target` (`1`, `2`) decoded from a configuration word. -/
def cfgTargetVal (w : BitVec 64) : BitVec 64 :=
  if cfgHasFlag w cfgFlagTargetSat then cfgTargetSatVal else cfgTargetDefault

/-- Upstream `options.restartint` (`1`, `50`) decoded from a configuration word. -/
def cfgRestartintVal (w : BitVec 64) : BitVec 64 :=
  if cfgHasFlag w cfgFlagRestartintSat then cfgRestartintSatVal else cfgRestartintDefault

/-- Map a preset identifier (`0..4`) to its exact preset bitmask. -/
def cfgOfId? (id : BitVec 64) : Option (BitVec 64) :=
  if id == cfgIdDefault then some cfgDefault
  else if id == cfgIdPlain then some cfgPlain
  else if id == cfgIdBasic then some cfgBasic
  else if id == cfgIdSat then some cfgSat
  else if id == cfgIdUnsat then some cfgUnsat
  else none

/-! ## 2. C0 Configuration Preset Functions (`kissat_c0! config`) -/

kissat_c0! config "
#include \"kissat_internal.h\"

#define M6_WM_CFG               7ULL

#define CFG_BUMPREASONS         (1ULL << 0)
#define CFG_CHRONO              (1ULL << 1)
#define CFG_COMPACT             (1ULL << 2)
#define CFG_EAGERSUBSUME        (1ULL << 3)
#define CFG_JUMPREASONS         (1ULL << 4)
#define CFG_OTFS                (1ULL << 5)
#define CFG_PREPROCESS          (1ULL << 6)
#define CFG_REORDER             (1ULL << 7)
#define CFG_REPHASE             (1ULL << 8)
#define CFG_RESTARTREUSETRAIL   (1ULL << 9)
#define CFG_SIMPLIFY            (1ULL << 10)
#define CFG_TUMBLE              (1ULL << 11)
#define CFG_STABLE_ONLY         (1ULL << 12)
#define CFG_RESTART             (1ULL << 13)
#define CFG_REDUCE              (1ULL << 14)
#define CFG_MINIMIZE            (1ULL << 15)
#define CFG_FOCUSED_ONLY        (1ULL << 16)
#define CFG_TARGET_SAT          (1ULL << 17)
#define CFG_RESTARTINT_SAT      (1ULL << 18)
#define CFG_INIT_BIT            (1ULL << 63)

#define CFG_TARGET_DEFAULT      1ULL
#define CFG_TARGET_SAT_VAL      2ULL
#define CFG_STABLE_UNSAT_VAL    0ULL
#define CFG_STABLE_DEFAULT_VAL  1ULL
#define CFG_STABLE_PLAIN_VAL    2ULL
#define CFG_RESTARTINT_DEFAULT  1ULL
#define CFG_RESTARTINT_SAT_VAL  50ULL

#define CFG_PLAIN_DISABLE_MASK  0x0000000000000FFFULL
#define CFG_PLAIN_MASK          0x0000000000001FFFULL
#define CFG_BASIC_EXTRA_MASK    0x000000000000E000ULL

#define CFG_DEFAULT             (CFG_INIT_BIT | CFG_PLAIN_DISABLE_MASK | CFG_BASIC_EXTRA_MASK)
#define CFG_PLAIN               (CFG_INIT_BIT | CFG_STABLE_ONLY | CFG_BASIC_EXTRA_MASK)
#define CFG_BASIC               (CFG_INIT_BIT | CFG_STABLE_ONLY)
#define CFG_SAT                 (CFG_DEFAULT | CFG_TARGET_SAT | CFG_RESTARTINT_SAT)
#define CFG_UNSAT               (CFG_DEFAULT | CFG_FOCUSED_ONLY)

#define CFG_ID_DEFAULT          0ULL
#define CFG_ID_PLAIN            1ULL
#define CFG_ID_BASIC            2ULL
#define CFG_ID_SAT              3ULL
#define CFG_ID_UNSAT            4ULL

extern u64 m6_hdr_get_watermark(FullHdr *h, u64 kind);
extern void m6_hdr_set_watermark(FullHdr *h, u64 kind, u64 val);

u64 kissat_config_mask_default(void) {
  return CFG_DEFAULT;
}

u64 kissat_config_mask_plain(void) {
  return CFG_PLAIN;
}

u64 kissat_config_mask_basic(void) {
  return CFG_BASIC;
}

u64 kissat_config_mask_sat(void) {
  return CFG_SAT;
}

u64 kissat_config_mask_unsat(void) {
  return CFG_UNSAT;
}

u64 kissat_config_get(FullHdr *h) {
  u64 w = m6_hdr_get_watermark(h, M6_WM_CFG);
  if ((w & CFG_INIT_BIT) == 0ULL) {
    return CFG_DEFAULT;
  }
  return w;
}

bool kissat_config_flag(FullHdr *h, u64 mask) {
  u64 w = kissat_config_get(h);
  return (w & mask) != 0ULL;
}

u64 kissat_config_stable(FullHdr *h) {
  u64 w = kissat_config_get(h);
  if ((w & CFG_STABLE_ONLY) != 0ULL) {
    return CFG_STABLE_PLAIN_VAL;
  }
  if ((w & CFG_FOCUSED_ONLY) != 0ULL) {
    return CFG_STABLE_UNSAT_VAL;
  }
  return CFG_STABLE_DEFAULT_VAL;
}

u64 kissat_config_target(FullHdr *h) {
  u64 w = kissat_config_get(h);
  return ((w & CFG_TARGET_SAT) != 0ULL) ? CFG_TARGET_SAT_VAL : CFG_TARGET_DEFAULT;
}

u64 kissat_config_restartint(FullHdr *h) {
  u64 w = kissat_config_get(h);
  return ((w & CFG_RESTARTINT_SAT) != 0ULL) ? CFG_RESTARTINT_SAT_VAL : CFG_RESTARTINT_DEFAULT;
}

void kissat_config_default(FullHdr *h) {
  m6_hdr_set_watermark(h, M6_WM_CFG, CFG_DEFAULT);
}

void kissat_config_plain(FullHdr *h) {
  m6_hdr_set_watermark(h, M6_WM_CFG, CFG_PLAIN);
}

void kissat_config_basic(FullHdr *h) {
  m6_hdr_set_watermark(h, M6_WM_CFG, CFG_BASIC);
}

void kissat_config_sat(FullHdr *h) {
  m6_hdr_set_watermark(h, M6_WM_CFG, CFG_SAT);
}

void kissat_config_unsat(FullHdr *h) {
  m6_hdr_set_watermark(h, M6_WM_CFG, CFG_UNSAT);
}

bool kissat_config_has_id(u64 cfg_id) {
  return cfg_id <= CFG_ID_UNSAT;
}

bool kissat_set_configuration(FullHdr *h, u64 cfg_id) {
  if (cfg_id == CFG_ID_DEFAULT) { kissat_config_default(h); return true; }
  if (cfg_id == CFG_ID_PLAIN) { kissat_config_plain(h); return true; }
  if (cfg_id == CFG_ID_BASIC) { kissat_config_basic(h); return true; }
  if (cfg_id == CFG_ID_SAT) { kissat_config_sat(h); return true; }
  if (cfg_id == CFG_ID_UNSAT) { kissat_config_unsat(h); return true; }
  return false;
}
"

/-- Ordered live functions of `Src/Config.lean` (`17` fns). -/
def fns : List Fn := config_fns

/-- External dependencies resolved by `Src/Tiers.lean`. -/
def externs : List Extern :=
  [ ⟨"m6_hdr_get_watermark", [i64, i64], [i64]⟩
  , ⟨"m6_hdr_set_watermark", [i64, i64, i64], []⟩
  ]

/-- Standalone acyclic module descriptor for `Src/Config.lean` (`0` exits). -/
def configModule : LeanQbe.T.Module :=
  { fns := fns, externs := externs, exits := [] }

end

/-! ## 3. Kernel-Checked `Func.Wf` & Module Shape Theorems (`0` `@[expose]`) -/

public section

theorem kissat_config_mask_default_wf : Func.Wf kissat_config_mask_default_body := by
  kissat_wf_reify
theorem kissat_config_mask_plain_wf : Func.Wf kissat_config_mask_plain_body := by
  kissat_wf_reify
theorem kissat_config_mask_basic_wf : Func.Wf kissat_config_mask_basic_body := by
  kissat_wf_reify
theorem kissat_config_mask_sat_wf : Func.Wf kissat_config_mask_sat_body := by
  kissat_wf_reify
theorem kissat_config_mask_unsat_wf : Func.Wf kissat_config_mask_unsat_body := by
  kissat_wf_reify
theorem kissat_config_get_wf : Func.Wf kissat_config_get_body := by kissat_wf_reify
theorem kissat_config_flag_wf : Func.Wf kissat_config_flag_body := by kissat_wf_reify
theorem kissat_config_stable_wf : Func.Wf kissat_config_stable_body := by kissat_wf_reify
theorem kissat_config_target_wf : Func.Wf kissat_config_target_body := by kissat_wf_reify
theorem kissat_config_restartint_wf : Func.Wf kissat_config_restartint_body := by
  kissat_wf_reify
theorem kissat_config_default_wf : Func.Wf kissat_config_default_body := by kissat_wf_reify
theorem kissat_config_plain_wf : Func.Wf kissat_config_plain_body := by kissat_wf_reify
theorem kissat_config_basic_wf : Func.Wf kissat_config_basic_body := by kissat_wf_reify
theorem kissat_config_sat_wf : Func.Wf kissat_config_sat_body := by kissat_wf_reify
theorem kissat_config_unsat_wf : Func.Wf kissat_config_unsat_body := by kissat_wf_reify
theorem kissat_config_has_id_wf : Func.Wf kissat_config_has_id_body := by kissat_wf_reify
theorem kissat_set_configuration_wf : Func.Wf kissat_set_configuration_body := by
  kissat_wf_reify

theorem fns_wf : ∀ f ∈ fns, f.Wf := by
  intro f hf
  simp only [fns, config_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact kissat_config_mask_default_wf
  · exact kissat_config_mask_plain_wf
  · exact kissat_config_mask_basic_wf
  · exact kissat_config_mask_sat_wf
  · exact kissat_config_mask_unsat_wf
  · exact kissat_config_get_wf
  · exact kissat_config_flag_wf
  · exact kissat_config_stable_wf
  · exact kissat_config_target_wf
  · exact kissat_config_restartint_wf
  · exact kissat_config_default_wf
  · exact kissat_config_plain_wf
  · exact kissat_config_basic_wf
  · exact kissat_config_sat_wf
  · exact kissat_config_unsat_wf
  · exact kissat_config_has_id_wf
  · exact kissat_set_configuration_wf

theorem configModule_fns : configModule.fns = fns := rfl

theorem configModule_noExit : configModule.exits = [] := rfl

theorem configModule_checkAcyclic : configModule.checkAcyclic = true := by rfl

end

end LeanQbe.T.Examples.Kissat.Src.Config
