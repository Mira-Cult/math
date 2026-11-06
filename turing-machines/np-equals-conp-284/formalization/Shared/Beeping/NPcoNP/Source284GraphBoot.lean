import Shared.Beeping.NPcoNP.Parent290Coalesced

/-! The first two transitions of the checked 284 producer register graph.
This proves a graph-level startup fact only; no physical tape simulation is
assumed. The initial output is the source's explicit startup beep. -/

namespace Shared.Beeping.NPcoNP.Source284GraphBoot
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem startup_config : target.system.run 2 = ⟨2, fun _ => 0⟩ := by
  rfl

theorem startup_word : target.system.prefixWord 2 = [true] := by
  rfl

end Shared.Beeping.NPcoNP.Source284GraphBoot
