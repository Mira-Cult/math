import Shared.Beeping.NPcoNP.Source284SourceRelocation
import Shared.Beeping.NPcoNP.Source284ScratchSentinel

/-! Install a protected certificate sentinel immediately after parsing the
raw input and before any token blocks are built. This prevents an unmarked
zero gap from merging with leading zeros of an arbitrary certificate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284InitialCertificateSentinel

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

/-- The bare number at an unmarked boundary does not determine which zeros
belong to the gap. Even the two low tag zeros do not remove the ambiguity. -/
theorem no_unmarked_recovery :
    ¬ ∃ recover : Nat → Nat, ∀ gap frame : Nat, recover (2^gap*(4*frame)) = 4*frame := by
  rintro ⟨recover,h⟩
  have h1 := h 1 1
  have h2 := h 0 2
  norm_num at h1 h2
  omega

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284PayloadSentinelPipeline.description (14+states) (Source284ScratchSentinel.special continuation)

def totalCost (w : List Bool) : Nat :=
  Source284PayloadSentinelPipeline.totalCost w.length+(4*(w++[false]).length+7)

/-- The marker is physically written after parsing, and every subsequent
continuation step uses the shifted finite table. -/
theorem source_then (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate)
      (totalCost w+fuel) =
    toSource (shiftConfig 169 (run continuation
      ⟨2*certificate+1,2*flipped (w++[false]) ((((suffix/4)/4)/2)),some 0⟩ fuel)) := by
  have hc := Source284ScratchSentinel.closed states continuation hn hv
  let c : Config := ⟨certificate,2*flipped (w++[false]) ((suffix/4)/4),some 0⟩
  have hvalid : Valid (14+states) c := by
    intro q hq; simp [c] at hq; subst q; omega
  have hr := run_toSource (14+states) (Source284ScratchSentinel.special continuation) 1 c hc hvalid
    (4*(w++[false]).length+7+fuel)
  dsimp only [c] at hr
  have ht : 4*(w++[false]).length+7+fuel = (4*(w++[false]).length+7)+fuel := by omega
  rw [ht,Source284ScratchFlipReturn.run_add,Source284ScratchSentinel.special_frame] at hr
  change _ = toSource (run (Source284ScratchSentinel.special continuation)
    (shiftConfig 14 ⟨2*certificate+1,2*flipped (w++[false]) (((suffix/4)/4)/2),some 0⟩) fuel) at hr
  rw [Source284ScratchSentinel.continuation_run] at hr
  change Source284Relative.run (encode (14+states) (Source284ScratchSentinel.special continuation) 1)
    (Source284Relative.initial (2*flipped (w++[false]) ((suffix/4)/4)) certificate) _ = _ at hr
  have hp := Source284SourceRelocation.source_run_after_pipeline (14+states)
    (Source284ScratchSentinel.special continuation) w certificate suffix
    (4*(w++[false]).length+7+fuel) (by omega) hc
  have htime : totalCost w+fuel = Source284PayloadSentinelPipeline.totalCost w.length+
      (4*(w++[false]).length+7+fuel) := by simp [totalCost]; omega
  rw [htime]
  change Source284Relative.run (Source284PayloadSentinelPipeline.description (14+states)
    (Source284ScratchSentinel.special continuation)) _ _ = _
  rw [hp,hr,Source284SourceRelocation.lift_toSource,Source284SourceRelocation.shiftConfig_add]

noncomputable def costPolynomial : Polynomial Nat :=
  2*Polynomial.X^2+26*Polynomial.X+36+(4*(Polynomial.X+1)+7)

theorem totalCost_polynomial (w : List Bool) : totalCost w = costPolynomial.eval w.length := by
  rw [totalCost,Source284PayloadSentinelPipeline.totalCost_formula]
  simp [costPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow]
  ring

end Shared.Beeping.NPcoNP.Source284InitialCertificateSentinel
