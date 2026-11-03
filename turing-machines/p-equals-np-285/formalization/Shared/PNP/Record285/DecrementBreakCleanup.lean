import Shared.PNP.Record285.DecrementZeroExactRun

/-! One-level break followed by exact event-free control and bank cleanup. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.DecrementBreakCleanup
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementShift (even_bit even_tail)
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.IncrementCleanup
open Shared.PNP.Record285.IncrementPreparation (dispatch0)

structure SkipRows (M : Machine 285) (skip : Fin 285) : Prop where
  one : M.table.row skip true = ⟨false,.left,skip,false⟩
  zero : M.table.row skip false = ⟨false,.left,lexical,false⟩

theorem literal_skip_rows : SkipRows Record285.machine DecrementZero.breakOne := by
  constructor <;> rw [ArtifactEndpoint.literal_rows] <;> decide

/-- Erase a trailing run of ones and pass the next zero without changing it. -/
theorem skip_one (M : Machine 285) (skip : Fin 285) (rows : SkipRows M skip)
    (n : Nat) (head : Int) (far right : Nat) :
    silent M (n+1) (atLeftWord skip (head-1) (runPattern true n false far) right) =
      some (atLeftWord lexical (head-n-2) far (2*pushBit n false right)) := by
  have hs := sweep_left M skip true false rows.one n false (head-1) far right
  have hlast : silent M 1 (atLeftWord skip (head-1-n) (2*far) (pushBit n false right)) =
      some (atLeftWord lexical (head-n-2) far (2*pushBit n false right)) := by
    simp only [atLeftWord,even_bit,even_tail,silent,PhysicalNumeric.step,rows.zero,
      Bool.false_eq_true,if_false,bitVal,Nat.add_zero]
    have hh : head-1-(n:Int)-1 = head-(n:Int)-2 := by omega
    rw [hh]
  rw [silent_add,hs]
  simp only [Option.bind_some,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
  exact hlast

theorem prepared_right (n1 n2 gap bank : Nat) :
    pushBit n2 false (2*pushBit n1 false (4*runPattern true (gap+1) false bank)) =
      runPattern false (n1+n2+3) true (runPattern true gap false bank) := by
  have hb : 4*runPattern true (gap+1) false bank =
      runPattern false 2 true (runPattern true gap false bank) := by
    simp only [runPattern,bitVal,if_true,Bool.false_eq_true,if_false,Nat.zero_add]
    omega
  rw [hb,pattern_zero_add]
  have hp : 2*runPattern false (n1+2) true (runPattern true gap false bank) =
      runPattern false ((n1+2)+1) true (runPattern true gap false bank) := by
    symm
    rw [runPattern]
    simp only [bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
  rw [hp,pattern_zero_add]
  congr 1
  omega

/-- Two successive control-zero boundaries are handled, then the bank and
dispatcher are restored. The complete tape and exact duration are explicit. -/
theorem skip_and_cleanup (n1 n2 gap : Nat) (head : Int) (far bank : Nat) :
    silent Record285.machine (3*(n1+n2)+2*gap+12)
      (atLeftWord DecrementZero.breakOne (head-1)
        (runPattern true n1 false (runPattern true n2 false far))
        (4*runPattern true (gap+1) false bank)) =
      some (atLeftWord dispatch0 (head-n1-n2-3) far
        (1+2*runPattern false (n1+n2+gap+3) true (2*bank))) := by
  let z := n1+n2+3
  have hs := skip_one Record285.machine DecrementZero.breakOne literal_skip_rows n1 head
    (runPattern true n2 false far) (4*runPattern true (gap+1) false bank)
  have hm := mark_control Record285.machine literal_rows n2 (head-n1-1) far
    (2*pushBit n1 false (4*runPattern true (gap+1) false bank))
  have hh : (head-(n1:Int)-1)-1 = head-(n1:Int)-2 := by omega
  rw [hh,prepared_right] at hm
  have hc := clear_prepared Record285.machine literal_rows z gap (head-n1-1-n2) far bank
  have hr := return_dispatch Record285.machine literal_rows (z+gap) (head+gap+1) far bank
  have hmid : head-(n1:Int)-1-(n2:Int)+(z:Int)+(gap:Int)-1 = head+(gap:Int)+1 := by
    dsimp [z]; omega
  have hend : head+(gap:Int)+1-(((z+gap:Nat):Int)+1) = head-(n1:Int)-(n2:Int)-3 := by
    dsimp [z]; omega
  rw [hend] at hr
  have htime : 3*(n1+n2)+2*gap+12 = (n1+1)+((n2+1)+((z+gap+3)+(z+gap+1))) := by
    dsimp [z]; omega
  have hz : z+gap = n1+n2+gap+3 := by dsimp [z]; omega
  rw [hz] at hr
  rw [htime,silent_add,hs]
  simp only [Option.bind_some]
  rw [silent_add,hm]
  simp only [Option.bind_some]
  rw [silent_add,hc]
  simp only [Option.bind_some,hmid]
  simpa only [hz] using hr

theorem skip_and_cleanup_physical (n1 n2 gap : Nat) (head : Int) (far bank : Nat)
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (atLeftWord DecrementZero.breakOne (head-1)
      (runPattern true n1 false (runPattern true n2 false far))
      (4*runPattern true (gap+1) false bank)) physical) :
    let steps := 3*(n1+n2)+2*gap+12
    Rel (atLeftWord dispatch0 (head-n1-n2-3) far
      (1+2*runPattern false (n1+n2+gap+3) true (2*bank)))
      ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
    (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
    0 < steps := by
  have hp := silent_physical Record285.machine _ physical hrel _ _
    (skip_and_cleanup n1 n2 gap head far bank)
  exact ⟨hp.1,hp.2,by omega⟩

end Shared.PNP.Record285.DecrementBreakCleanup
