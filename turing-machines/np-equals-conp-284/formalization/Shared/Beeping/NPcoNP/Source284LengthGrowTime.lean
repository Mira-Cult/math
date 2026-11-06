import Shared.Beeping.NPcoNP.Source284LengthGrowLoop

/-! Explicit charged source-step bound for the autonomous producer. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
namespace Shared.Beeping.NPcoNP.Source284LengthGrowTime

open Shared.Beeping.NPcoNP.Source284LengthGrowRound
open Shared.Beeping.NPcoNP.Source284LengthGrowLoop

theorem grow_formula (xs rest : List Bool) (b : Bool) :
    growTime xs rest b = 4*xs.length*xs.length+24*xs.length+
      12*(xs.length+1+rest.length)+58 := by
  simp [growTime,compareTime,List.length_append]
  ring

theorem equal_formula (n : Nat) : equalTime n = 4*n*n+28*n+36 := by
  simp [equalTime,compareTime]
  ring

/-- The multiplication by three avoids truncated division in the exact
cubic formula. `k` is the number already produced and `n` the final size. -/
theorem total_formula (xs rest : List Bool) :
    let k := xs.length
    let n := xs.length+rest.length
    3*totalTime xs rest + (4*k*k*k+30*k*k+36*n*k+140*k) =
      4*n*n*n+78*n*n+224*n+108 := by
  induction rest generalizing xs with
  | nil =>
    simp [totalTime,equal_formula]
    ring
  | cons b rest ih =>
    have h := ih (xs++[b])
    simp only [List.length_append,List.length_singleton,List.length_nil,Nat.zero_add,
      List.length_cons] at h ⊢
    rw [totalTime,grow_formula]
    nlinarith

theorem zero_formula (w : List Bool) :
    3*totalTime [] w = 4*w.length*w.length*w.length+78*w.length*w.length+224*w.length+108 := by
  simpa using total_formula [] w

end Shared.Beeping.NPcoNP.Source284LengthGrowTime
