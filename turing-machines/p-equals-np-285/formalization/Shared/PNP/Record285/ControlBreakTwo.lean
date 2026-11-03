import Shared.PNP.Record285.ControlBreakOne
import Shared.PNP.Record285.ControlBreakRank

/-! Complete literal two-level break from the grammar root. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ControlBreak
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.IncrementCleanup
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.ControlInvariant
open Shared.PNP.Record285.ControlContinue (literal_control_leaf_any)

def skipTwoState : Fin 285 := ⟨118,by decide⟩

theorem skip_two_zero : Record285.machine.table.row skipTwoState false = ⟨false,.left,skipState,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]; decide

theorem skip_two_one : Record285.machine.table.row skipTwoState true = ⟨false,.left,skipTwoState,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]; decide

def returnAfterTwoSkip : List Bool → Option (List Bool)
  | [] => none
  | false::rest => returnAfterOneSkip rest
  | true::rest => returnAfterTwoSkip rest

def returnPathSkipTwo (code : List Bool) : Option (List Bool) := returnAfterTwoSkip code.reverse

theorem peel_count (xs : List Bool) (hz : false ∈ xs) :
    (peel xs).2.count false+1 = xs.count false := by
  have hd := peel_decomposition xs hz
  have hc := congrArg (fun ys : List Bool => ys.count false) hd
  have hz' : (List.replicate (peel xs).1 true).count false = 0 := by simp [List.count_replicate]
  simp only [List.count_append,hz',Nat.zero_add,List.count_cons_self] at hc
  omega

theorem count_has_zero (xs : List Bool) (h : 0 < xs.count false) : false ∈ xs := by
  by_cases hz : false ∈ xs
  · exact hz
  · have hc : xs.count false = 0 := List.count_eq_zero.mpr hz
    omega

theorem three_peels (xs : List Bool) (h : 3 ≤ xs.count false) :
    false ∈ xs ∧ false ∈ (peel xs).2 ∧ false ∈ (peel (peel xs).2).2 := by
  have h1 := count_has_zero xs (by omega)
  have hc1 := peel_count xs h1
  have h2 := count_has_zero (peel xs).2 (by omega)
  have hc2 := peel_count (peel xs).2 h2
  have h3 := count_has_zero (peel (peel xs).2).2 (by omega)
  exact ⟨h1,h2,h3⟩

theorem return_after_two_skip (xs : List Bool) (hfirst : false ∈ xs)
    (hsecond : false ∈ (peel xs).2) (hthird : false ∈ (peel (peel xs).2).2) :
    returnAfterTwoSkip xs = some ((peel (peel (peel xs).2).2).2.reverse++[true]) := by
  induction xs with
  | nil => simp at hfirst
  | cons b bs ih =>
    cases b with
    | false =>
      simpa only [returnAfterTwoSkip,peel] using return_after_one_skip bs hsecond hthird
    | true =>
      have hb : false ∈ bs := by simpa using hfirst
      simpa only [returnAfterTwoSkip,peel] using ih hb hsecond hthird

theorem break_two_return (pre : List Bool) (hfirst : false ∈ pre.reverse)
    (hsecond : false ∈ (peel pre.reverse).2) (hthird : false ∈ (peel (peel pre.reverse).2).2)
    (hsafe : detectorRun 0 (scanWord pre) = some 0) (gap : Nat) (head : Int)
    (leftTail bank : Nat) :
    let p := peel pre.reverse
    let q := peel p.2
    let r := peel q.2
    let precode := r.2.reverse
    let inner := (q.1+1)+(3*r.1+2*(q.1+(p.1+gap+1)+2)+5)+(precode.length+17)
    let steps := (p.1+1)+inner
    silent Record285.machine steps
      (atLeftWord skipTwoState head (bits (pre.reverse++rootLeft) leftTail)
        (2*runPattern false gap true (2*bank))) =
      some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-1-q.1-1-r.1) leftTail
        (runPattern false (r.1+(q.1+(p.1+gap+1)+1)) true (2*bank))) := by
  dsimp only
  let p := peel pre.reverse
  have hz : false ∈ pre.reverse++rootLeft := by simp [hfirst]
  have hp := peel_append pre.reverse rootLeft hfirst
  have hw := peel_bits (pre.reverse++rootLeft) hz leftTail
  rw [hp] at hw
  dsimp only at hw
  have hs := skip_control Record285.machine skipTwoState skipState skip_two_zero skip_two_one p.1 gap head
    (bits (p.2++rootLeft) leftTail) bank
  have hsafe' := peel_prefix_safe pre hsafe hfirst
  have hr := break_one_return p.2.reverse (by simpa using hsecond) (by simpa using hthird) hsafe'
    (p.1+gap+1) (head-p.1-1) leftTail bank
  simp only [List.reverse_reverse] at hr
  rw [hw,silent_add,hs]
  simp only [Option.bind_some]
  exact hr

/-- The literal `break.2` has the required three zero boundaries by a
checked invariant, and returns to root preserving the entire bank. -/
theorem root_break_two (code : List Bool) (hwalk : walk 162 code = some (.brk 2))
    (marker : Bool) (gap : Nat) (head : Int) (leftTail rightTail bank : Nat)
    (hanchor : bitVal marker+2*rightTail = runPattern false gap true (2*bank)) :
    ∃ pre, code = pre++[true] ∧
      let p := peel pre.reverse
      let q := peel p.2
      let r := peel q.2
      let precode := r.2.reverse
      let inner := (q.1+1)+(3*r.1+2*(q.1+(p.1+gap+1)+2)+5)+(precode.length+17)
      let steps := code.length+(p.1+1)+inner
      returnPathSkipTwo code = some (precode++[true]) ∧
      silent Record285.machine steps
        (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft []) head leftTail rightTail) =
        some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
          (head-2-p.1-1-q.1-1-r.1) leftTail
          (runPattern false (r.1+(q.1+(p.1+gap+1)+1)) true (2*bank))) ∧ 0 < steps := by
  obtain ⟨pre,hcode,hcount,hsafe⟩ := ControlBreakRank.break_prefix_zeros code 2 hwalk
  have hcount' : 3 ≤ pre.reverse.count false := by simpa only [List.count_reverse] using hcount
  have hprior := three_peels pre.reverse hcount'
  have hf := literal_control_leaf_any code pre (.brk 2) skipTwoState
    (by simpa only [rootIndex] using hwalk) hcode (by decide) (by decide) marker head leftTail rightTail
  rw [hanchor] at hf
  have hr := break_two_return pre hprior.1 hprior.2.1 hprior.2.2 hsafe gap (head-2) leftTail bank
  have hp := return_after_two_skip pre.reverse hprior.1 hprior.2.1 hprior.2.2
  refine ⟨pre,hcode,?_,?_,by omega⟩
  · simpa [returnPathSkipTwo,returnAfterTwoSkip,hcode,List.reverse_append] using hp
  · rw [show code.length+((peel pre.reverse).1+1)+
        (((peel (peel pre.reverse).2).1+1)+
          (3*(peel (peel (peel pre.reverse).2).2).1+
            2*((peel (peel pre.reverse).2).1+((peel pre.reverse).1+gap+1)+2)+5)+
          ((peel (peel (peel pre.reverse).2).2).2.reverse.length+17)) =
        code.length+(((peel pre.reverse).1+1)+
          (((peel (peel pre.reverse).2).1+1)+
            (3*(peel (peel (peel pre.reverse).2).2).1+
              2*((peel (peel pre.reverse).2).1+((peel pre.reverse).1+gap+1)+2)+5)+
            ((peel (peel (peel pre.reverse).2).2).2.reverse.length+17))) by omega,
      silent_add,hf]
    simp only [Option.bind_some]
    exact hr

theorem root_break_two_physical (code : List Bool) (hwalk : walk 162 code = some (.brk 2))
    (marker : Bool) (gap : Nat) (head : Int) (leftTail rightTail bank : Nat)
    (hanchor : bitVal marker+2*rightTail = runPattern false gap true (2*bank))
    (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft []) head leftTail rightTail)
      physical) :
    ∃ pre, code = pre++[true] ∧
      let p := peel pre.reverse
      let q := peel p.2
      let r := peel q.2
      let precode := r.2.reverse
      let inner := (q.1+1)+(3*r.1+2*(q.1+(p.1+gap+1)+2)+5)+(precode.length+17)
      let steps := code.length+(p.1+1)+inner
      returnPathSkipTwo code = some (precode++[true]) ∧
      Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-2-p.1-1-q.1-1-r.1) leftTail
        (runPattern false (r.1+(q.1+(p.1+gap+1)+1)) true (2*bank)))
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
      0 < steps := by
  obtain ⟨pre,hcode,hpath,hs,hpos⟩ := root_break_two code hwalk marker gap head leftTail rightTail bank hanchor
  have hp := silent_physical Record285.machine _ physical hrel _ _ hs
  exact ⟨pre,hcode,hpath,hp.1,hp.2,hpos⟩

end Shared.PNP.Record285.ControlBreak
