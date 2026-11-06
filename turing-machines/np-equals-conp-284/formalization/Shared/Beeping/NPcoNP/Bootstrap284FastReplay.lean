import Shared.Beeping.NPcoNP.Bootstrap284FastEffects
import Shared.Beeping.NPcoNP.Bootstrap284Certificate

/-! A more compact executable tape-update implementation of the bootstrap
certificate checker, proved extensionally equal to the original checker. -/
namespace Shared.Beeping.NPcoNP.Bootstrap284FastReplay
open Shared.Beeping Shared.Beeping.Machines PASoundness
open Shared.Beeping.NPcoNP.Table284
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.Bootstrap284Scans
open Shared.Beeping.NPcoNP.Bootstrap284FastEffects
open Shared.Beeping.NPcoNP.Bootstrap284Certificate

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

def executeFast (op : Op) (c : Config 284) : Option (Config 284 × Nat) :=
  match op with
  | .single => if (machine.step c).2 then none else some ((machine.step c).1,1)
  | .right n => if 0<n ∧ c.state=4 ∧ rightOK n c.head c.tape then
      some (cfg 4 (c.head+2*(n : Int)) c.tape,2*n) else none
  | .left n => if 0<n ∧ c.state=2 ∧ leftOK n c.head c.tape then
      some (cfg 2 (c.head-2*(n : Int)) (fastLeft n c.tape c.head),2*n) else none
  | .fill n => if 0<n ∧ c.state=0 ∧ leftOK n c.head c.tape then
      some (cfg 0 (c.head-2*(n : Int)) (fastFill n c.tape c.head),2*n) else none

theorem executeFast_eq (op : Op) (c : Config 284) : executeFast op c=execute op c := by
  cases op with
  | single => rfl
  | right n => rfl
  | left n => simp only [executeFast,execute,← left_eq_fast]
  | fill n => simp only [executeFast,execute,← fill_eq_fast]

def replayFast : List Op → Config 284 → Option (Config 284 × Nat)
  | [],c => some (c,0)
  | op::ops,c => do
    let (d,n) ← executeFast op c
    let (e,m) ← replayFast ops d
    pure (e,n+m)

theorem replayFast_eq (ops : List Op) (c : Config 284) : replayFast ops c=replay ops c := by
  induction ops generalizing c with
  | nil => rfl
  | cons op ops ih => simp only [replayFast,replay,executeFast_eq,ih]

theorem replayFast_sound (ops : List Op) (c e : Config 284) (n : Nat)
    (he : replayFast ops c=some (e,n)) : silentSegment machine c e n := by
  rw [replayFast_eq] at he
  exact replay_sound ops c e n he

theorem replayFast_cost_ge_length (ops : List Op) (c e : Config 284) (n : Nat)
    (he : replayFast ops c=some (e,n)) : ops.length≤n := by
  rw [replayFast_eq] at he
  exact replay_cost_ge_length ops c e n he
end Shared.Beeping.NPcoNP.Bootstrap284FastReplay
