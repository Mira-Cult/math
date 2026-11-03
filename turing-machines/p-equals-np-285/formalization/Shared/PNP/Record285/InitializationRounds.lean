import Shared.PNP.Record285.InitializationChecker
set_option maxRecDepth 16384
set_option maxHeartbeats 0
set_option exponentiation.threshold 8192
/-! A proposed repeated literal initialization cycle. A successful check is
turned into an exact silent physical segment. No universal check is assumed. -/
namespace Shared.PNP.Record285.InitializationRounds
open Shared.PNP.Record285.InitializationChecker Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep Shared.PNP.Record285.BootstrapRows

def cfg (n : Nat) : Config 285 := ⟨exit,-(2*((n:Int)+1)),rep4 (1910-n)+1,false,4^(n+2)*rep4 (n+2)⟩
def roundCommands (n : Nat) : List Command := [
.single,
.single,
.rightRun .fill10 (2*n+2),
.single,
.single,
.leftRun .scan110 (2*n+1),
.leftPair .scan110 1,
.leftRun .scan110 0,
.leftPair .scan110 (1907-1*n),
.single,
.single,
.single,
.single,
.single,
.rightRun .scan109 5,
.single,
.single,
.rightPair .boot6 (1906-1*n),
.single,
.single,
.single,
.single,
.single,
.rightRun .scan12 (2*n+3),
.single,
.rightRun .scan14 0,
.rightPair .shift14 (1*n-1),
.single,
.single,
.leftRun .scan51 0,
.leftPair .scan51 (1*n-1),
.leftRun .scan51 0,
.leftPair .scan51 0,
.leftRun .scan51 (2*n+2),
.single,
.single,
.single,
.rightRun .scan55 1,
.single,
.rightRun .erase56 (2*n+2),
.single,
.single,
.leftRun .scan119 (2*n+4),
.single,
.leftRun .scan110 1,
.leftPair .scan110 (1907-1*n),
.single,
.single,
.single,
.single,
.single,
.rightRun .scan109 5,
.single,
.single,
.rightPair .boot6 (1906-1*n),
.single,
.single,
.single,
.single,
.single,
.rightRun .fill10 (2*n+2),
.single,
.single,
.leftRun .scan110 (2*n+1),
.leftPair .scan110 0,
.leftRun .scan110 2,
.leftPair .scan110 (1907-1*n),
.single,
.single,
.single,
.single,
.single,
.rightRun .scan109 5,
.single,
.single,
.rightPair .boot6 (1906-1*n),
.single,
.single,
.single,
.single,
.single,
.rightRun .scan11 (2*n+3),
.single,
.single,
.single,
.rightPair .scan46 (1*n-1),
.single,
.single,
.leftPair .shift48 (1*n+0),
.single,
.single,
.leftRun .scan51 (2*n+3),
.single,
.single,
.leftRun .clear1 2,
.single,
.rightRun .scan55 4,
.single,
.rightRun .erase56 (2*n+2),
.single,
.single,
.leftRun .scan119 (2*n+7),
.single,
.leftRun .scan110 0,
.leftPair .scan110 (1906-1*n),
.single,
.single,
.single,
.single,
.single,
.rightRun .scan109 5,
.single,
.single,
.rightPair .boot6 (1905-1*n),
.single,
.single,
.single]
def duration (n : Nat) : Nat := 30690+16*n

/-- Check a candidate cycle using the proved physical command checker. -/
def checkRound (n : Nat) : Bool :=
  decide (verify (roundCommands n) (cfg n) = some (duration n,cfg (n+1)))

theorem checked_round (n : Nat) (h : checkRound n = true) :
    silent Record285.machine (duration n) (cfg n) = some (cfg (n+1)) := by
  exact verify_sound _ _ _ _ (of_decide_eq_true h)

/-- Sum exact physical durations without assuming any loop accelerates time. -/
def elapsed (start : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => duration start + elapsed (start+1) k

theorem checked_rounds (start count : Nat)
    (h : ∀ n, start ≤ n → n < start+count → checkRound n = true) :
    silent Record285.machine (elapsed start count) (cfg start) = some (cfg (start+count)) := by
  induction count generalizing start with
  | zero => simp [elapsed, silent]
  | succ k ih =>
    have hone := checked_round start (h start (by omega) (by omega))
    have hrest := ih (start+1) (by intro n hn hl; exact h n (by omega) (by omega))
    simp only [elapsed, silent_add, hone, Option.bind_some]
    have he : start+1+k = start+(k+1) := by omega
    simpa only [he] using hrest

theorem range_join (start a b : Nat)
    (ha : (List.range' start a).all checkRound = true)
    (hb : (List.range' (start+a) b).all checkRound = true) :
    (List.range' start (a+b)).all checkRound = true := by
  rw [← List.range'_append, List.all_append]
  simp only [Nat.one_mul, ha, hb, Bool.and_self]

end Shared.PNP.Record285.InitializationRounds
