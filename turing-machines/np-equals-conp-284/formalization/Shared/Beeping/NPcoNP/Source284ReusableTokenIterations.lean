import Shared.Beeping.NPcoNP.Source284ReusableTokenLoop
import Shared.Beeping.NPcoNP.Source284WorkspaceSuffixCost

/-! The fixed token-transfer table can execute any finite number of rounds.
The repetition count is a mathematical observation index; it is not yet a
source program that chooses a stopping time. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 5000000
namespace Shared.Beeping.NPcoNP.Source284ReusableTokenIterations

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)
open Shared.Beeping.NPcoNP.Source284ReusableTokenRound (roundCost)
open Shared.Beeping.NPcoNP.Source284ReusableTokenLoop (table)

def repeatCost : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | r+1, m, n, width => roundCost m n width + repeatCost r m (n+m) width

theorem halves_add (a b value : Nat) : halves a (halves b value) = halves (a+b) value := by
  simp only [Source284WorkspaceSuffixCost.halves_eq,Nat.div_div_eq_div_mul,pow_add]
  congr 1
  ring

/-- Every finite prefix of the same fixed table restores the original token
block and extends the counter by `rounds * m`, including `m = 0`. -/
theorem iterations (rounds m n : Nat) (w : List Bool) (certificate higher : Nat) :
    run table ⟨pairTape (List.replicate m false) certificate,
      2*flipped w (counter n higher),some 0⟩ (repeatCost rounds m n w.length) =
    ⟨pairTape (List.replicate m false) certificate,
      2*flipped w (counter (n+rounds*m) (halves (rounds*m) higher)),some 0⟩ := by
  induction rounds generalizing n higher with
  | zero => simp [repeatCost,run,halves]
  | succ rounds ih =>
    simp only [repeatCost]
    rw [run_add,Source284ReusableTokenLoop.iteration,ih,halves_add]
    have ha : n+m+rounds*m = n+(rounds+1)*m := by ring
    have hb : rounds*m+m = (rounds+1)*m := by ring
    rw [ha,hb]

/-- Exact polynomial cost of all iterations, avoiding truncated subtraction. -/
theorem repeatCost_formula (rounds m n width : Nat) :
    repeatCost rounds m n width + m*m*rounds =
      rounds*(3*m*m+m*(2*n+4*width+29)+16)+m*m*rounds*rounds := by
  induction rounds generalizing n with
  | zero => simp [repeatCost]
  | succ rounds ih =>
    simp only [repeatCost,Source284ReusableTokenRound.roundCost_formula]
    have h := ih (n+m)
    nlinarith

/-- In particular, `m` rounds produce `m^2` additional counter marks. -/
theorem square_prefix (m n : Nat) (w : List Bool) (certificate higher : Nat) :
    run table ⟨pairTape (List.replicate m false) certificate,
      2*flipped w (counter n higher),some 0⟩ (repeatCost m m n w.length) =
    ⟨pairTape (List.replicate m false) certificate,
      2*flipped w (counter (n+m*m) (halves (m*m) higher)),some 0⟩ :=
  iterations m m n w certificate higher


/-- The redirected loop is a finite closed, non-accepting source table. -/
theorem finite_rows : ∀ q : Fin 42, ∀ b : Bool,
    (table q.val b).next.getD 42 < 42 := by decide +kernel

theorem closed : Closed 42 table := by
  intro q hq b q' hnext
  have h := finite_rows ⟨q,hq⟩ b
  simp [hnext] at h
  exact h

theorem source_iterations (rounds m n : Nat) (w : List Bool) (certificate higher : Nat) :
    Source284Relative.run (encode 42 table 1)
      (Source284Relative.initial (2*flipped w (counter n higher))
        (pairTape (List.replicate m false) certificate)) (repeatCost rounds m n w.length) =
    ⟨pairTape (List.replicate m false) certificate,
      2*flipped w (counter (n+rounds*m) (halves (rounds*m) higher)),active 0⟩ := by
  let start : Config := ⟨pairTape (List.replicate m false) certificate,
    2*flipped w (counter n higher),some 0⟩
  have hi : Valid 42 start := by intro q hq; simp [start] at hq; subst q; omega
  have hr := run_toSource 42 table 1 start closed hi (repeatCost rounds m n w.length)
  rw [iterations] at hr
  exact hr

namespace Fixtures
example : run table ⟨pairTape [] 7,2*flipped [] (counter 0 5),some 0⟩
    (repeatCost 2 0 0 0) = ⟨pairTape [] 7,2*flipped [] (counter 0 5),some 0⟩ := by decide +kernel
example : run table ⟨pairTape [false] 7,2*flipped [true] (counter 0 5),some 0⟩
    (repeatCost 1 1 0 1) = ⟨pairTape [false] 7,2*flipped [true] (counter 1 2),some 0⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284ReusableTokenIterations
