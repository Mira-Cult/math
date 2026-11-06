import Shared.Beeping.NPcoNP.Source284SquareRepeat

/-! Exact polynomial accounting for a fixed number of square-growth passes. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284SquareRepeatCost

open Shared.Beeping.NPcoNP.Source284SquareRepeat

theorem roundCost_formula (n current width : Nat) :
    roundCost n current width = n^4+2*n^3+2*n^2*current+4*n^2*width+35*n^2+44*n+26 := by
  have h := Shared.Beeping.NPcoNP.Source284SquareLoopTotal.loopCost_formula n n 0 current width
  simp only [roundCost] at *
  nlinarith

theorem repeatCost_formula (k n current width : Nat) :
    repeatCost k n current width+n^4*k =
      k*(n^4+2*n^3+2*n^2*current+4*n^2*width+35*n^2+44*n+26)+n^4*k*k := by
  induction k generalizing current with
  | zero => simp [repeatCost]
  | succ k ih =>
    simp only [repeatCost,roundCost_formula]
    have h := ih (current+n*n)
    nlinarith

/-- An explicit polynomial upper bound, with `k` fixed in the code. -/
theorem repeatCost_le (k n width : Nat) :
    repeatCost k n 0 width ≤
      k*(n^4+2*n^3+4*n^2*width+35*n^2+44*n+26)+n^4*k*k := by
  have h := repeatCost_formula k n 0 width
  simp only [mul_zero,add_zero] at h
  omega

end Shared.Beeping.NPcoNP.Source284SquareRepeatCost
