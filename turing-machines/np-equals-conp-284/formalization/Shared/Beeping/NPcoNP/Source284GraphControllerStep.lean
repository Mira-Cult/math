import Shared.Beeping.NPcoNP.Source284GraphComparison

/-! One event-preserving controller step in the concrete register graph. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284GraphControllerStep
open PASoundness PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.Parent290Coalesced
open Shared.Beeping.NPcoNP.Source284GraphApplyLoops (Seg)
open Shared.Beeping.NPcoNP.Source284GraphParserInit (clear_loop)
abbrev Bank := PASoundness.RegisterMachine.Bank 12

theorem row0 (b : Bank) : target.system.step ⟨0,b⟩ = (⟨1,b⟩,[true]) := by rfl

theorem row1 (b : Bank) : target.system.step ⟨1,b⟩ =
    if b 4 = 0 then (⟨2,b⟩,[]) else (⟨1,write b 4 (b 4-1)⟩,[]) := by
  cases h : b (4 : Fin 12) <;>
    simp [target,MaskInvariant.Program.system,MaskInvariant.Action.execute,execute,h,
      Parent290MaskData.program,CoalescingAlgebra.translateInstruction,
      CoalescingAlgebra.translate,Coalescing284Map.logicalToSuffix]

/-- Rejection emits exactly one beep and resets the input counter before the
next comparison. The reset takes a positive, finite number of graph steps. -/
theorem restart (b : Bank) :
    target.system.advance ⟨0,b⟩ (b 4+2) = ⟨2,write b 4 0⟩ ∧
    target.system.wordFrom ⟨0,b⟩ (b 4+2) = [true] := by
  have h := clear_loop target.system 1 2 4 row1 b
  have ht : b 4+2 = 1+(b 4+1) := by omega
  constructor
  · rw [ht,WordEventSystem.advance_add]
    simpa [WordEventSystem.advance,row0] using h.1
  · rw [ht,WordEventSystem.wordFrom_add]
    simpa [WordEventSystem.advance,WordEventSystem.wordFrom,row0,h.1] using h.2

/-- Every source comparison is simulated by a positive finite graph segment
from PC 2 to PC 2. Its word is empty on success and exactly one beep on
rejection, with candidate and input counters updated as the source prescribes. -/
theorem controller_step (b : Bank) (h9 : b 9=0) (h10 : b 10=0) (h11 : b 11=0) :
    ∃ (time : Nat) (out : Bank), 0 < time ∧
      target.system.advance ⟨2,b⟩ time = ⟨2,out⟩ ∧
      target.system.wordFrom ⟨2,b⟩ time =
        (if Source284Comparison.compare (b 3) (b 4) then [] else [true]) ∧
      out 3 = (if Source284Comparison.compare (b 3) (b 4) then b 3 else b 3+1) ∧
      out 4 = (if Source284Comparison.compare (b 3) (b 4) then b 4+1 else 0) ∧
      out 9=0 ∧ out 10=0 ∧ out 11=0 := by
  obtain ⟨k,r,hk,hseg,h3,h4,hs9,hs10,hs11⟩ :=
    Source284GraphComparison.comparison_from_pc2 b h9 h10 h11
  cases hc : Source284Comparison.compare (b 3) (b 4) with
  | true =>
    refine ⟨k,r,hk,?_,?_,?_,?_,hs9,hs10,hs11⟩
    · simpa [Seg,hc] using hseg.1
    · simpa [Seg,hc] using hseg.2
    · simpa [hc] using h3
    · simpa [hc] using h4
  | false =>
    have hr := restart r
    refine ⟨k+(r 4+2),write r 4 0,by omega,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [WordEventSystem.advance_add]
      have ha : target.system.advance ⟨2,b⟩ k = ⟨0,r⟩ := by simpa [Seg,hc] using hseg.1
      rw [ha,hr.1]
    · rw [WordEventSystem.wordFrom_add]
      have ha : target.system.advance ⟨2,b⟩ k = ⟨0,r⟩ := by simpa [Seg,hc] using hseg.1
      have hw : target.system.wordFrom ⟨2,b⟩ k = [] := hseg.2
      rw [ha,hw,hr.2]
      simp [hc]
    · simpa [write,hc] using h3
    · simp [write,hc]
    · simpa [write] using hs9
    · simpa [write] using hs10
    · simpa [write] using hs11

end Shared.Beeping.NPcoNP.Source284GraphControllerStep
