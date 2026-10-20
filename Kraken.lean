module

/-
Kraken - x86_64 Assembly Interpreter

Root module. The baseline instruction semantics is `Operation.interp` in
Kraken/X64/Semantics.lean, in continuation-passing style over `Effects`.
Kraken/X64/WP/Basic.lean is the run of a program fragment in the baseline's
burst. Kraken/X64/WP/Instance.lean interprets a program by its run at predicates over
machine states, and Kraken/X64/WP/Frame.lean at separation-logic assertions over the
memory, with the instruction specs of Kraken/SepSpecs.lean and the frame
inference of Kraken/SepFrameProc.lean. Kraken/StateCfg.lean links the runs of
basic blocks into the run of a program with jumps. Both wps are discharged by
the `Std.WP` `vcgen` pipeline.
-/

public import Kraken.X64.Semantics
public import Kraken.X64.Parser
public import Kraken.X64.OmniSemantics
public import Kraken.X64.Sep
public import Kraken.Specs
public import Kraken.Tactics
public import Kraken.X64.Registers
public import Kraken.X64.WP
public import Kraken.KVCGen
public import Kraken.X64.WP.Instance
public import Kraken.StateCfg
public import Kraken.MProp
public import Kraken.X64.WP.Frame
public import Kraken.SepCancel
public import Kraken.SepSpecs
public import Kraken.SepFrameProc
import Kraken.X64.Examples.Examples
import Kraken.X64.Examples.FrameWP.AluMem
import Kraken.X64.Examples.FrameWP.DynamicStack
import Kraken.X64.Examples.FrameWP.Move2RegsToHeap
import Kraken.X64.Examples.FrameWP.PushPop
import Kraken.X64.Examples.FrameWP.Sib
import Kraken.X64.Examples.FrameWP.Swap
import Kraken.X64.Examples.WP.AluMem
import Kraken.X64.Examples.WP.Basic
import Kraken.X64.Examples.WP.P3
import Kraken.X64.Examples.WP.CallSwap
import Kraken.X64.Examples.WP.Memmove
import Kraken.X64.Examples.WP.Jumps
import Kraken.X64.Examples.WP.Surprises
import Kraken.X64.Examples.WP.EventuallySurprises
import Kraken.X64.Examples.WP.PushPopLoop
