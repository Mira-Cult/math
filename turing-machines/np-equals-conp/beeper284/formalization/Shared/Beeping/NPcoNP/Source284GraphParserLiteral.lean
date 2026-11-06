import Shared.Beeping.NPcoNP.Source284GraphParserLoop
import Shared.Beeping.NPcoNP.Parent290Coalesced

/-! The marker/payload and clearing rows of the checked coalesced graph.
These local execution facts begin at supplied register configurations and do
not establish physical tape reachability or the complete parser loop. -/

namespace Shared.Beeping.NPcoNP.Source284GraphParserLiteral

open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Source284GraphParserLoop
open Shared.Beeping.NPcoNP.Parent290Coalesced

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem clear_row : ClearRow target := by rfl

theorem marker_rows : MarkerRows target := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem clear_segment (n : Nat) (b : Bank 12) (h : b 0 = n) :
    target.system.advance ⟨22,b⟩ (n+1) = ⟨23,write b 0 0⟩ ∧
      target.system.wordFrom ⟨22,b⟩ (n+1) = [] :=
  Source284GraphParserLoop.clear_segment target clear_row n b h

theorem marker_step (b : Bank 12) :
    target.system.step ⟨13,b⟩ =
      (⟨if b 0 % 2 = 0 then 22 else 14, write b 0 (b 0 / 2)⟩,[]) :=
  Source284GraphParserLoop.marker_step target marker_rows b

theorem payload_steps (b : Bank 12) :
    let bit := b 0 % 2
    let k := if bit = 0 then 2 else 3
    let result := write (write (write b 0 (b 0 / 2)) 6 (b 6 + bit)) 5 (b 5 + 1)
    target.system.advance ⟨19,b⟩ k = ⟨13,result⟩ ∧
      target.system.wordFrom ⟨19,b⟩ k = [] :=
  Source284GraphParserLoop.payload_steps target marker_rows b

end Shared.Beeping.NPcoNP.Source284GraphParserLiteral
