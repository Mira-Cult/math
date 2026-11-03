import Shared.PNP.Record285.ControlContinueOne

/-! Complete two-level grammar continuation from root to root. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ControlContinue
open Shared.Beeping.Machines
open Shared.PNP.Record285.PhysicalNumeric
open Shared.PNP.Record285.BootstrapSweep
open Shared.PNP.Record285.PhysicalSweeps
open Shared.PNP.Record285.RelativeTape (bitVal)
open Shared.PNP.Record285.IncrementSelector (odd_bit odd_tail)
open Shared.PNP.Record285.IncrementReturn (atLeftWord)
open Shared.PNP.Record285.IncrementCleanup
open Shared.PNP.Record285.IncrementPreparation (break0 dispatch0)
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar
open Shared.PNP.Record285.ControlInvariant

def skipState : Fin 285 := ⟨120,by decide⟩

theorem skip_zero : Record285.machine.table.row skipState false = ⟨false,.left,skipState,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]; decide

theorem skip_one : Record285.machine.table.row skipState true = ⟨false,.left,break0,false⟩ := by
  rw [ArtifactEndpoint.literal_rows]; decide

def continueAfterTwo : List Bool → Option (List Bool)
  | [] => none
  | true::rest => continueAfterOne rest
  | false::rest => continueAfterTwo rest

def continuePathTwo (code : List Bool) : Option (List Bool) :=
  continueAfterTwo code.reverse.tail

theorem continue_after_two (xs : List Bool) (h : true ∈ xs)
    (hnext : true ∈ (peelZeros xs).2) :
    continueAfterTwo xs = some ((peelZeros (peelZeros xs).2).2.reverse++[true]) := by
  induction xs with
  | nil => simp at h
  | cons b bs ih =>
    cases b with
    | true => simpa [continueAfterTwo,peelZeros] using continue_after_one bs hnext
    | false =>
      have hb : true ∈ bs := by simpa using h
      simpa only [continueAfterTwo,peelZeros] using ih hb hnext

theorem peel_zeros_preserves_second (xs : List Bool) (hcount : 2 ≤ xs.count true) :
    true ∈ (peelZeros xs).2 := by
  have ht : true ∈ xs := by
    by_cases hm : true ∈ xs
    · exact hm
    · have hz : xs.count true = 0 := List.count_eq_zero.mpr hm
      omega
  have hd := peel_zeros_decomposition xs ht
  have hc := congrArg (fun ys : List Bool => ys.count true) hd
  have hz : (List.replicate (peelZeros xs).1 false).count true = 0 := by simp [List.count_replicate]
  simp only [List.count_append,hz,Nat.zero_add,List.count_cons_self] at hc
  have hp : 0 < ((peelZeros xs).2).count true := by omega
  by_cases hm : true ∈ (peelZeros xs).2
  · exact hm
  · have hz' : ((peelZeros xs).2).count true = 0 := List.count_eq_zero.mpr hm
    omega

theorem continue_two_prior (pre : List Bool)
    (hwalk : walk 162 (pre++[true]) = some (.cont 2)) :
    true ∈ pre.reverse ∧ true ∈ (peelZeros pre.reverse).2 := by
  have hc : 2 ≤ pre.count true := by
    cases pre with
    | nil => simp [walk,root_true_edge] at hwalk
    | cons a as =>
      cases a with
      | false => cases as <;> simp [walk,root_false_edge] at hwalk
      | true =>
        cases as with
        | nil => simp [walk,root_true_edge,next_true_edge] at hwalk
        | cons b bs =>
          cases b with
          | true => simp [walk,root_true_edge,next_true_edge] at hwalk
          | false =>
            cases bs with
            | nil => simp [walk,root_true_edge,next_false_edge,beep_true_edge] at hwalk
            | cons c cs =>
              cases c with
              | false => cases cs <;> simp [walk,root_true_edge,next_false_edge,beep_false_edge] at hwalk
              | true => simp
  have hr : 2 ≤ pre.reverse.count true := by simpa using hc
  have hfirst : true ∈ pre.reverse := by
    by_cases hm : true ∈ pre.reverse
    · exact hm
    · have hz : pre.reverse.count true = 0 := List.count_eq_zero.mpr hm
      omega
  exact ⟨hfirst,peel_zeros_preserves_second pre.reverse hr⟩

theorem skip_scan (M : Machine 285) (qskip qnext : Fin 285)
    (h0 : M.table.row qskip false = ⟨false,.left,qskip,false⟩)
    (h1 : M.table.row qskip true = ⟨false,.left,qnext,false⟩)
    (n : Nat) (head : Int) (far right : Nat) :
    silent M (n+1) (atLeftWord qskip head (runPattern false n true far) (4*right)) =
      some (atLeftWord qnext (head-n-1) far (4*(2*pushBit n false right))) := by
  have hs := sweep_left M qskip false false h0 n true head far (4*right)
  have he : silent M 1
      (atLeftWord qskip (head-n) (1+2*far) (pushBit n false (4*right))) =
      some (atLeftWord qnext (head-n-1) far (4*(2*pushBit n false right))) := by
    simp only [atLeftWord,odd_bit,odd_tail,silent,PhysicalNumeric.step,h1,
      Bool.false_eq_true,if_false,bitVal,Nat.add_zero,push_zeros_four]
    have hr : 2*(4*pushBit n false right) = 4*(2*pushBit n false right) := by omega
    simp only [hr]
  rw [silent_add,hs]
  simp only [Option.bind_some,bitVal,if_true]
  exact he

theorem continue_two_return (pre : List Bool) (hfirst : true ∈ pre.reverse)
    (hsecond : true ∈ (peelZeros pre.reverse).2)
    (hsafe : detectorRun 0 (scanWord pre) = some 0) (head : Int) (leftTail rightTail : Nat) :
    let p := peelZeros pre.reverse
    let q := peelZeros p.2
    let precode := q.2.reverse
    let mid := 2*pushBit p.1 false rightTail
    let right := 2*pushBit q.1 false mid
    let steps := (p.1+1)+(q.1+1+(precode.length+17))
    silent Record285.machine steps
      (atLeftWord skipState head (bits (pre.reverse++rootLeft) leftTail) (4*rightTail)) =
      some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-1-q.1) leftTail right) := by
  dsimp only
  let p := peelZeros pre.reverse
  let mid := 2*pushBit p.1 false rightTail
  have hd := peel_zeros_decomposition pre.reverse hfirst
  have hw : bits (pre.reverse++rootLeft) leftTail =
      runPattern false p.1 true (bits (p.2++rootLeft) leftTail) := by
    rw [hd]
    simp only [List.cons_append,List.append_assoc]
    exact bits_zeros p.1 (p.2++rootLeft) leftTail
  have hs := skip_scan Record285.machine skipState break0 skip_zero skip_one p.1 head
    (bits (p.2++rootLeft) leftTail) rightTail
  have hp := peeled_prefix_safe pre hfirst hsafe
  have hr := continue_one_return p.2.reverse (by simpa using hsecond) hp (head-p.1-1) leftTail mid
  simp only [List.reverse_reverse] at hr
  rw [hw,silent_add,hs]
  simp only [Option.bind_some]
  exact hr

theorem continue_path_two (pre : List Bool) (hfirst : true ∈ pre.reverse)
    (hsecond : true ∈ (peelZeros pre.reverse).2) :
    continuePathTwo (pre++[true]) =
      some ((peelZeros (peelZeros pre.reverse).2).2.reverse++[true]) := by
  simpa [continuePathTwo,List.reverse_append] using continue_after_two pre.reverse hfirst hsecond

/-- The `continue.2` leaf returns to the literal root after skipping the
first earlier one, preserving the complete physical tape. -/
theorem root_continue_two (code : List Bool) (hwalk : walk 162 code = some (.cont 2))
    (head : Int) (leftTail rightTail : Nat) :
    ∃ pre, code = pre++[true] ∧
      let p := peelZeros pre.reverse
      let q := peelZeros p.2
      let precode := q.2.reverse
      let mid := 2*pushBit p.1 false rightTail
      let right := 2*pushBit q.1 false mid
      let steps := code.length+(p.1+1)+(q.1+1+(precode.length+17))
      continuePathTwo code = some (precode++[true]) ∧
      silent Record285.machine steps (rootEntry code head leftTail rightTail) =
        some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
          (head-2-p.1-1-q.1) leftTail right) ∧ 0 < steps := by
  obtain ⟨pre,parent,row,hcode,_,_,_,_,hsafe⟩ := continue_prefix_safe code 2 hwalk
  have hprior := continue_two_prior pre (by simpa [hcode] using hwalk)
  have hf := literal_control_leaf code pre (.cont 2) skipState
    (by simpa only [rootIndex] using hwalk) hcode (by decide) (by decide) head leftTail rightTail
  have hr := continue_two_return pre hprior.1 hprior.2 hsafe (head-2) leftTail rightTail
  refine ⟨pre,hcode,?_,?_,by omega⟩
  · rw [hcode]
    exact continue_path_two pre hprior.1 hprior.2
  · rw [show code.length+((peelZeros pre.reverse).1+1)+
        ((peelZeros (peelZeros pre.reverse).2).1+1+
          ((peelZeros (peelZeros pre.reverse).2).2.reverse.length+17)) =
        code.length+(((peelZeros pre.reverse).1+1)+
          ((peelZeros (peelZeros pre.reverse).2).1+1+
            ((peelZeros (peelZeros pre.reverse).2).2.reverse.length+17))) by omega,
      silent_add,hf]
    simp only [Option.bind_some]
    exact hr

theorem root_continue_two_physical (code : List Bool) (hwalk : walk 162 code = some (.cont 2))
    (head : Int) (leftTail rightTail : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (rootEntry code head leftTail rightTail) physical) :
    ∃ pre, code = pre++[true] ∧
      let p := peelZeros pre.reverse
      let q := peelZeros p.2
      let precode := q.2.reverse
      let mid := 2*pushBit p.1 false rightTail
      let right := 2*pushBit q.1 false mid
      let steps := code.length+(p.1+1)+(q.1+1+(precode.length+17))
      continuePathTwo code = some (precode++[true]) ∧
      Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-2-p.1-1-q.1) leftTail right)
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
      0 < steps := by
  obtain ⟨pre,hcode,hpath,hs,hpos⟩ := root_continue_two code hwalk head leftTail rightTail
  have hp := silent_physical Record285.machine _ physical hrel _ _ hs
  exact ⟨pre,hcode,hpath,hp.1,hp.2,hpos⟩

theorem skip_scan_any (M : Machine 285) (qskip qnext : Fin 285)
    (h0 : M.table.row qskip false = ⟨false,.left,qskip,false⟩)
    (h1 : M.table.row qskip true = ⟨false,.left,qnext,false⟩)
    (n : Nat) (head : Int) (far right : Nat) :
    silent M (n+1) (atLeftWord qskip head (runPattern false n true far) (2*right)) =
      some (atLeftWord qnext (head-n-1) far (2*(2*pushBit n false right))) := by
  have hs := sweep_left M qskip false false h0 n true head far (2*right)
  have hp : pushBit n false (2*right) = 2*pushBit n false right := by
    simpa only [bitVal,Bool.false_eq_true,if_false,Nat.add_zero] using pushBit_affine n false right
  have he : silent M 1
      (atLeftWord qskip (head-n) (1+2*far) (pushBit n false (2*right))) =
      some (atLeftWord qnext (head-n-1) far (2*(2*pushBit n false right))) := by
    simp only [atLeftWord,odd_bit,odd_tail,silent,PhysicalNumeric.step,h1,
      Bool.false_eq_true,if_false,bitVal,Nat.add_zero,hp]
  rw [silent_add,hs]
  simp only [Option.bind_some,bitVal,if_true]
  exact he

theorem continue_two_return_any (pre : List Bool) (hfirst : true ∈ pre.reverse)
    (hsecond : true ∈ (peelZeros pre.reverse).2)
    (hsafe : detectorRun 0 (scanWord pre) = some 0) (head : Int) (leftTail right : Nat) :
    let p := peelZeros pre.reverse
    let q := peelZeros p.2
    let precode := q.2.reverse
    let mid := 2*pushBit p.1 false right
    let steps := (p.1+1)+(q.1+1+(precode.length+17))
    silent Record285.machine steps
      (atLeftWord skipState head (bits (pre.reverse++rootLeft) leftTail) (2*right)) =
      some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1-1-q.1) leftTail (pushBit q.1 false mid)) := by
  dsimp only
  let p := peelZeros pre.reverse
  let mid := 2*pushBit p.1 false right
  have hd := peel_zeros_decomposition pre.reverse hfirst
  have hw : bits (pre.reverse++rootLeft) leftTail =
      runPattern false p.1 true (bits (p.2++rootLeft) leftTail) := by
    rw [hd]
    simp only [List.cons_append,List.append_assoc]
    exact bits_zeros p.1 (p.2++rootLeft) leftTail
  have hs := skip_scan_any Record285.machine skipState break0 skip_zero skip_one p.1 head
    (bits (p.2++rootLeft) leftTail) right
  have hp := peeled_prefix_safe pre hfirst hsafe
  have hr := continue_one_return_any p.2.reverse (by simpa using hsecond) hp (head-p.1-1) leftTail mid
  simp only [List.reverse_reverse] at hr
  rw [hw,silent_add,hs]
  simp only [Option.bind_some]
  exact hr

theorem root_continue_two_any (code : List Bool) (hwalk : walk 162 code = some (.cont 2))
    (marker : Bool) (head : Int) (leftTail rightTail : Nat) :
    ∃ pre, code = pre++[true] ∧
      let p := peelZeros pre.reverse
      let q := peelZeros p.2
      let precode := q.2.reverse
      let mid := 2*pushBit p.1 false (bitVal marker+2*rightTail)
      let steps := code.length+(p.1+1)+(q.1+1+(precode.length+17))
      continuePathTwo code = some (precode++[true]) ∧
      silent Record285.machine steps
        (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft []) head leftTail rightTail) =
        some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
          (head-2-p.1-1-q.1) leftTail (pushBit q.1 false mid)) ∧ 0 < steps := by
  obtain ⟨pre,parent,row,hcode,_,_,_,_,hsafe⟩ := continue_prefix_safe code 2 hwalk
  have hprior := continue_two_prior pre (by simpa [hcode] using hwalk)
  have hf := literal_control_leaf_any code pre (.cont 2) skipState
    (by simpa only [rootIndex] using hwalk) hcode (by decide) (by decide) marker head leftTail rightTail
  have hr := continue_two_return_any pre hprior.1 hprior.2 hsafe (head-2) leftTail (bitVal marker+2*rightTail)
  refine ⟨pre,hcode,?_,?_,by omega⟩
  · rw [hcode]
    exact continue_path_two pre hprior.1 hprior.2
  · rw [show code.length+((peelZeros pre.reverse).1+1)+
        ((peelZeros (peelZeros pre.reverse).2).1+1+
          ((peelZeros (peelZeros pre.reverse).2).2.reverse.length+17)) =
        code.length+(((peelZeros pre.reverse).1+1)+
          ((peelZeros (peelZeros pre.reverse).2).1+1+
            ((peelZeros (peelZeros pre.reverse).2).2.reverse.length+17))) by omega,
      silent_add,hf]
    simp only [Option.bind_some]
    exact hr

theorem root_continue_two_any_physical (code : List Bool) (hwalk : walk 162 code = some (.cont 2))
    (marker : Bool) (head : Int) (leftTail rightTail : Nat) (physical : Shared.Beeping.Machines.Config 285)
    (hrel : Rel (denote (rightWord treeRoot (-(code.length:Int)) code marker rootLeft []) head leftTail rightTail)
      physical) :
    ∃ pre, code = pre++[true] ∧
      let p := peelZeros pre.reverse
      let q := peelZeros p.2
      let precode := q.2.reverse
      let mid := 2*pushBit p.1 false (bitVal marker+2*rightTail)
      let steps := code.length+(p.1+1)+(q.1+1+(precode.length+17))
      continuePathTwo code = some (precode++[true]) ∧
      Rel (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-2-p.1-1-q.1) leftTail (pushBit q.1 false mid))
        ((Shared.Beeping.EventSystem.mk physical Record285.machine.step).run steps) ∧
      (∀ t, t < steps → ¬ (Shared.Beeping.EventSystem.mk physical Record285.machine.step).BeepAt t) ∧
      0 < steps := by
  obtain ⟨pre,hcode,hpath,hs,hpos⟩ := root_continue_two_any code hwalk marker head leftTail rightTail
  have hp := silent_physical Record285.machine _ physical hrel _ _ hs
  exact ⟨pre,hcode,hpath,hp.1,hp.2,hpos⟩

end Shared.PNP.Record285.ControlContinue
