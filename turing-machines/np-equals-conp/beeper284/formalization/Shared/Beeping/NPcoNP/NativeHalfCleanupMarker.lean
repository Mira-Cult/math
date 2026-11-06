import Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix

/-! The prepared exceptional HALF cleanup leaves a concrete one to the
right of its state-23 head. This is a tape-layout result, not a claim that
the literal blank-start run reaches the prepared boundary. -/

namespace Shared.Beeping.NPcoNP.NativeHalfCleanupMarker

open Shared.Beeping.NPcoNP.NativeHalfCleanupPrefix
open Shared.Beeping.NPcoNP.NativeHalfSweep

/-- The reserve bit written by the reverse cleanup is a one. -/
theorem postTape_marker (base : Int → Bool) (b : Int) (values : List Nat) :
    postTape base b values
      (b + 3 + ((false :: UnaryBank.encode values).length : Int)) = true := by
  exact spec_top _ _ _

/-- The marker is strictly to the right of the state-23 head, uniformly even
when the encoded bank is empty and the protected base tape is arbitrary. -/
theorem postTape_marker_right (base : Int → Bool) (b : Int) (values : List Nat) :
    ∃ p : Int, b < p ∧ postTape base b values p = true := by
  refine ⟨b + 3 + ((false :: UnaryBank.encode values).length : Int), ?_,
    postTape_marker base b values⟩
  have hn : (0 : Int) ≤ ((false :: UnaryBank.encode values).length : Int) := by omega
  omega

end Shared.Beeping.NPcoNP.NativeHalfCleanupMarker
