import Shared.Beeping.NPcoNP.NativeHalfState27Scan

/-! An adversarial prepared state-27 configuration. A tape that is zero
from the head indefinitely to the right makes the literal machine scan
silently forever. Such a tape can have finite nonblank support, but this
module does not assert that the blank-start machine reaches state 27 on it. -/

namespace Shared.Beeping.NPcoNP.NativeHalfState27Trap

open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfState27Scan

/-- A right-zero tail forces every finite prefix to remain in state 27,
move right once per transition, and leave the whole tape unchanged. -/
theorem run_zeroes (h : Int) (t : Int → Bool)
    (hz : ∀ i : Nat, t (h + (i : Int)) = false) (n : Nat) :
    machine.system.advance (cfg 27 h t) n = cfg 27 (h + n) t := by
  have hs := scan_zeroes h t n (fun i _ => hz i)
  simpa [silentSegment, W, ScalarWordRefinement.advance_ofBeep] using hs.1

/-- Every transition of the rightward scan is silent. -/
theorem run_zeroes_silent (h : Int) (t : Int → Bool)
    (hz : ∀ i : Nat, t (h + (i : Int)) = false) (n : Nat) :
    ¬ machine.system.BeepFrom (cfg 27 h t) n := by
  have hs := scan_zeroes h t (n+1) (fun i _ => hz i)
  exact silent_no_beep machine _ _ _ n hs (by omega)

/-- The all-zero tape has finite nonblank support and furnishes a concrete
silent configuration that never exits state 27. -/
theorem blank_tape_trap (h : Int) :
    let t : Int → Bool := fun _ => false
    (∃ touched : List Int, ∀ p, p ∉ touched → t p = false) ∧
      ∀ n, (machine.system.advance (cfg 27 h t) n).state = 27 ∧
        ¬ machine.system.BeepFrom (cfg 27 h t) n := by
  dsimp only
  refine ⟨⟨[], by simp⟩, ?_⟩
  intro n
  have hz : ∀ i : Nat, (fun _ : Int => false) (h + (i : Int)) = false := by simp
  constructor
  · rw [run_zeroes h _ hz n]
    rfl
  · exact run_zeroes_silent h _ hz n

end Shared.Beeping.NPcoNP.NativeHalfState27Trap
