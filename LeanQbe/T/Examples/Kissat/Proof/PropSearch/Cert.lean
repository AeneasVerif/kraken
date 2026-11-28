module

public import LeanQbe.T.Examples.Kissat.Src.PropSearch
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Backtrack.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Float64.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Tiers.Spec
public import LeanQbe.T.Logic.CanonicalEnv
import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpOvfFlush
import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpOvfTail
import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpProp

namespace LeanQbe.T.Examples.Kissat.Proof.PropSearch

open LeanQbe.T

public theorem cert :
    SegCert Spec.deps LeanQbe.T.Examples.Kissat.Src.PropSearch.fns Spec.specs := by
  intro Γ hdeps hrows
  have hWatchPush := Spec.deps_has_full_watch_push hdeps
  have hWm4 := Spec.deps_has_m6_wm4_get hdeps
  have hAddTicks := Spec.deps_has_m6_hdr_add_ticks hdeps
  have hBt := Spec.deps_has_full_backtrack hdeps
  have hOvf := Spec.has_full_prop_lit_ovf_hot hrows
  have hFlushSlow := Spec.has_full_prop_flush_slow_fid hrows
  have hFlushDel := Spec.has_full_prop_flush_del_fid hrows
  have hIgnHot := Spec.has_full_propagate_ignore_hot hrows
  have hProp := Spec.has_full_propagate hrows
  exact ⟨SpecEntry.Impl.of (full_prop_lit_ovf_hot_wp Γ hWatchPush),
    ⟨SpecEntry.Impl.of (full_prop_flush_slow_fid_wp Γ hWatchPush),
      ⟨SpecEntry.Impl.of (full_prop_flush_del_fid_wp Γ hFlushSlow),
        ⟨SpecEntry.Impl.of (full_propagate_ignore_hot_wp Γ hOvf hFlushDel hWm4 hAddTicks),
          ⟨SpecEntry.Impl.of (full_propagate_ignore_wp Γ hOvf hFlushDel hWm4 hAddTicks),
            ⟨SpecEntry.Impl.of (full_propagate_wp Γ hIgnHot),
              ⟨SpecEntry.Impl.of (full_flush_trail_wp Γ hBt hProp),
                ⟨SpecEntry.Impl.of
                    (full_propagate_beyond_m7_wp Γ hOvf hFlushDel hWm4 hAddTicks),
                  trivial⟩⟩⟩⟩⟩⟩⟩⟩

end LeanQbe.T.Examples.Kissat.Proof.PropSearch
