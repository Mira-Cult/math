import Shared.PNP.Record285.ControlContinueCore
import Shared.PNP.Record285.DecrementControl

/-! Literal break cleanup for an unprepared gap and full arbitrary bank. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ControlBreak
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.IncrementCleanup
open Shared.PNP.Record285.IncrementPreparation (dispatch0)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar

/-- A control break begins with an unprepared run of zeros. It clears the
control suffix, restores the anchor, and enters the detector. -/
theorem cleanup_unprepared (M : Machine 285) (rows : IncrementCleanup.Rows M)
    (n gap : Nat) (head : Int) (far bank : Nat) :
    silent M (3*n+2*gap+5)
      (atLeftWord lexical (head-1) (runPattern true n false far)
        (runPattern false gap true (2*bank))) =
      some (atLeftWord dispatch0 (head-n-2) far
        (1+2*runPattern false (n+gap) true (2*bank))) := by
  let z := n+gap
  have hm := mark_control M rows n head far (runPattern false gap true (2*bank))
  rw [pattern_zero_add] at hm
  have hc := clear_prepared M rows z 0 (head-n) far bank
  have hzero : runPattern true 0 false bank = 2*bank := by simp [runPattern,bitVal]
  simp only [hzero,Nat.add_zero,Int.natCast_zero,Int.add_zero] at hc
  have hr := return_dispatch M rows z (head+gap-1) far bank
  have hmid : head-(n:Int)+(z:Int)-1 = head+(gap:Int)-1 := by dsimp [z]; omega
  have hend : head+(gap:Int)-1-((z:Int)+1) = head-(n:Int)-2 := by dsimp [z]; omega
  rw [hend] at hr
  have htime : 3*n+2*gap+5 = (n+1)+((z+0+3)+(z+1)) := by dsimp [z]; omega
  rw [htime,silent_add,hm]
  simp only [Option.bind_some]
  rw [silent_add,hc]
  simp only [Option.bind_some,hmid]
  exact hr

/-- A level-zero break returns to the root under explicit, finite anchor and
control-prefix conditions. The bank and arbitrary far tail remain exact. -/
theorem break_zero_return (pre : List Bool) (hzero : false ∈ pre.reverse)
    (hsafe : detectorRun 0 (scanWord pre) = some 0) (gap : Nat) (head : Int)
    (leftTail bank : Nat) :
    let p := peel pre.reverse
    let precode := p.2.reverse
    let rightTail := runPattern false (p.1+gap) true (2*bank)
    let steps := (3*p.1+2*(gap+1)+5)+(precode.length+17)
    silent Record285.machine steps
      (atLeftWord lexical head (bits (pre.reverse++rootLeft) leftTail)
        (2*runPattern false gap true (2*bank))) =
      some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1) leftTail rightTail) := by
  dsimp only
  let p := peel pre.reverse
  let precode := p.2.reverse
  let rightTail := runPattern false (p.1+gap) true (2*bank)
  have hzero' : false ∈ pre.reverse++rootLeft := by simp [hzero]
  have hp := peel_append pre.reverse rootLeft hzero
  have hw := peel_bits (pre.reverse++rootLeft) hzero' leftTail
  rw [hp] at hw
  dsimp only at hw
  have hc := cleanup_unprepared Record285.machine literal_rows p.1 (gap+1) (head+1)
    (bits (p.2++rootLeft) leftTail) bank
  have hgap : runPattern false (gap+1) true (2*bank) =
      2*runPattern false gap true (2*bank) := by
    simp only [runPattern,bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
  rw [hgap] at hc
  have hpos : head+1-1 = head := by omega
  rw [hpos,← hw] at hc
  have hsafe' := peel_prefix_safe pre hsafe hzero
  have hr := literal_return_root precode hsafe' (head-p.1) leftTail rightTail
  have hpre : pathLeft precode = p.2++rootLeft := by
    simp [precode,pathLeft,rootLeft,List.append_assoc]
  have hright : 1+2*runPattern false (p.1+(gap+1)) true (2*bank) = 1+4*rightTail := by
    dsimp only [rightTail]
    rw [show p.1+(gap+1) = (p.1+gap)+1 by omega,runPattern]
    simp only [bitVal,Bool.false_eq_true,if_false,Nat.zero_add]
    omega
  have hhead : head+1-(p.1:Int)-2 = (head-p.1)-1 := by omega
  rw [hhead] at hc
  rw [hpre,← hright] at hr
  rw [silent_add,hc]
  simp only [Option.bind_some]
  exact hr

end Shared.PNP.Record285.ControlBreak
