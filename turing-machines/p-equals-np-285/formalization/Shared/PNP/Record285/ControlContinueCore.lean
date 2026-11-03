import Shared.PNP.Record285.GrammarAutoDispatch
import Shared.PNP.Record285.GrammarReturnRoot

/-! Full-tape continuation return after the literal control leaf. -/
set_option maxRecDepth 8192
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
open Shared.PNP.Record285.GenericDispatch
open Shared.PNP.Record285.DispatcherInvariant (detector_append)
open Shared.PNP.Record285.SymbolicDispatch
open Shared.PNP.Record285.Grammar

/-- Read a word from right to left up to its first one. -/
def peelZeros : List Bool → Nat × List Bool
  | [] => (0,[])
  | true::xs => (0,xs)
  | false::xs => let p := peelZeros xs; (p.1+1,p.2)

theorem peel_zeros_decomposition (xs : List Bool) (h : true ∈ xs) :
    xs = List.replicate (peelZeros xs).1 false ++ true::(peelZeros xs).2 := by
  induction xs with
  | nil => simp at h
  | cons b bs ih =>
    cases b with
    | true => simp [peelZeros]
    | false =>
      have hb : true ∈ bs := by simpa using h
      have hh := ih hb
      cases hp : peelZeros bs with
      | mk n rest =>
        simp only [hp] at hh
        simp only [peelZeros,hp,List.replicate_succ,List.cons_append]
        exact congrArg (List.cons false) hh

theorem bits_zeros (n : Nat) (rest : List Bool) (tail : Nat) :
    bits (List.replicate n false ++ true::rest) tail =
      runPattern false n true (bits rest tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,List.cons_append,bits,runPattern,bitVal,
      Bool.false_eq_true,if_false,Nat.zero_add,ih]

theorem peeled_prefix_safe (pre : List Bool) (htrue : true ∈ pre.reverse)
    (hsafe : detectorRun 0 (scanWord pre) = some 0) :
    detectorRun 0 (scanWord (peelZeros pre.reverse).2.reverse) = some 0 := by
  have hd := peel_zeros_decomposition pre.reverse htrue
  have hs := hsafe
  simp only [scanWord] at hs ⊢
  rw [hd,List.append_assoc,detector_append] at hs
  cases hm : detectorRun 0 (List.replicate (peelZeros pre.reverse).1 false) with
  | none => simp [hm] at hs
  | some d =>
    simp only [hm,Option.bind_some] at hs
    change detectorRun d (true :: ((peelZeros pre.reverse).2 ++ [false,true,true])) = some 0 at hs
    simp only [detectorRun,detectorNext,if_true,Option.bind_some] at hs
    simpa only [List.reverse_reverse] using hs

theorem push_zeros_four (n tail : Nat) : pushBit n false (4*tail) = 4*pushBit n false tail := by
  induction n generalizing tail with
  | zero => rfl
  | succ n ih =>
    simp only [pushBit,bitVal,Bool.false_eq_true,if_false,Nat.add_zero]
    have h := ih (2*tail)
    have he : 2*(4*tail) = 4*(2*tail) := by omega
    simpa only [he] using h

/-- A finite zero scan retains the first one and enters the dispatcher. -/
theorem continue_scan (M : Machine 285) (rows : IncrementCleanup.Rows M)
    (n : Nat) (head : Int) (far right : Nat) :
    silent M (n+1) (atLeftWord IncrementPreparation.break0 head
      (runPattern false n true far) (4*right)) =
      some (atLeftWord IncrementPreparation.dispatch0 (head-n-1) far
        (1+4*(2*pushBit n false right))) := by
  have hs := sweep_left M IncrementPreparation.break0 false false rows.returnZero n true head far (4*right)
  have hlast : silent M 1
      (atLeftWord IncrementPreparation.break0 (head-n) (1+2*far) (pushBit n false (4*right))) =
      some (atLeftWord IncrementPreparation.dispatch0 (head-n-1) far
        (1+4*(2*pushBit n false right))) := by
    simp only [atLeftWord,odd_bit,odd_tail,silent,PhysicalNumeric.step,rows.returnOne,
      Bool.false_eq_true,if_false,bitVal,if_true,push_zeros_four]
    have hr : 2*(4*pushBit n false right)+1 = 1+4*(2*pushBit n false right) := by omega
    simp only [hr]
  rw [silent_add,hs]
  simp only [Option.bind_some,bitVal,if_true]
  exact hlast

/-- Under the explicit earlier-one and detector-safe conditions, continuation
reaches the next root with arbitrary tails and exact silent duration. -/
theorem continue_one_return (pre : List Bool) (htrue : true ∈ pre.reverse)
    (hsafe : detectorRun 0 (scanWord pre) = some 0) (head : Int) (leftTail rightTail : Nat) :
    let p := peelZeros pre.reverse
    let precode := p.2.reverse
    let right := 2*pushBit p.1 false rightTail
    let steps := p.1+1+(precode.length+17)
    silent Record285.machine steps
      (atLeftWord IncrementPreparation.break0 head (bits (pre.reverse++rootLeft) leftTail) (4*rightTail)) =
      some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1) leftTail right) := by
  dsimp only
  let p := peelZeros pre.reverse
  let precode := p.2.reverse
  let right := 2*pushBit p.1 false rightTail
  have hd := peel_zeros_decomposition pre.reverse htrue
  have hw : bits (pre.reverse++rootLeft) leftTail =
      runPattern false p.1 true (bits (p.2++rootLeft) leftTail) := by
    rw [hd]
    simp only [List.cons_append,List.append_assoc]
    exact bits_zeros p.1 (p.2++rootLeft) leftTail
  have hs := continue_scan Record285.machine IncrementCleanup.literal_rows p.1 head
    (bits (p.2++rootLeft) leftTail) rightTail
  have hp := peeled_prefix_safe pre htrue hsafe
  have hr := literal_return_root precode hp (head-p.1) leftTail right
  have hprefix : pathLeft precode = p.2++rootLeft := by
    simp [precode,pathLeft,rootLeft,List.append_assoc]
  have hpos : (head-p.1)-1 = head-p.1-1 := by omega
  rw [hprefix,hpos] at hr
  rw [hw,silent_add,hs]
  simp only [Option.bind_some]
  exact hr

theorem continue_scan_any (M : Machine 285) (rows : IncrementCleanup.Rows M)
    (n : Nat) (head : Int) (far right : Nat) :
    silent M (n+1) (atLeftWord IncrementPreparation.break0 head
      (runPattern false n true far) (2*right)) =
      some (atLeftWord IncrementPreparation.dispatch0 (head-n-1) far
        (1+4*pushBit n false right)) := by
  have hs := sweep_left M IncrementPreparation.break0 false false rows.returnZero n true head far (2*right)
  have hp : pushBit n false (2*right) = 2*pushBit n false right := by
    simpa only [bitVal,Bool.false_eq_true,if_false,Nat.add_zero] using pushBit_affine n false right
  have hlast : silent M 1
      (atLeftWord IncrementPreparation.break0 (head-n) (1+2*far) (pushBit n false (2*right))) =
      some (atLeftWord IncrementPreparation.dispatch0 (head-n-1) far
        (1+4*pushBit n false right)) := by
    simp only [atLeftWord,odd_bit,odd_tail,silent,PhysicalNumeric.step,rows.returnOne,
      Bool.false_eq_true,if_false,bitVal,if_true,hp]
    have hr : 2*(2*pushBit n false right)+1 = 1+4*pushBit n false right := by omega
    simp only [hr]
  rw [silent_add,hs]
  simp only [Option.bind_some,bitVal,if_true]
  exact hlast

/-- No assumption on the bit immediately after the control instruction:
it is included in `right` and retained exactly. -/
theorem continue_one_return_any (pre : List Bool) (htrue : true ∈ pre.reverse)
    (hsafe : detectorRun 0 (scanWord pre) = some 0) (head : Int) (leftTail right : Nat) :
    let p := peelZeros pre.reverse
    let precode := p.2.reverse
    let steps := p.1+1+(precode.length+17)
    silent Record285.machine steps
      (atLeftWord IncrementPreparation.break0 head (bits (pre.reverse++rootLeft) leftTail) (2*right)) =
      some (denote (rightWord treeRoot (-(precode.length:Int)) precode true rootLeft [false])
        (head-p.1) leftTail (pushBit p.1 false right)) := by
  dsimp only
  let p := peelZeros pre.reverse
  let precode := p.2.reverse
  have hd := peel_zeros_decomposition pre.reverse htrue
  have hw : bits (pre.reverse++rootLeft) leftTail =
      runPattern false p.1 true (bits (p.2++rootLeft) leftTail) := by
    rw [hd]
    simp only [List.cons_append,List.append_assoc]
    exact bits_zeros p.1 (p.2++rootLeft) leftTail
  have hs := continue_scan_any Record285.machine IncrementCleanup.literal_rows p.1 head
    (bits (p.2++rootLeft) leftTail) right
  have hp := peeled_prefix_safe pre htrue hsafe
  have hr := literal_return_root precode hp (head-p.1) leftTail (pushBit p.1 false right)
  have hprefix : pathLeft precode = p.2++rootLeft := by
    simp [precode,pathLeft,rootLeft,List.append_assoc]
  have hpos : (head-p.1)-1 = head-p.1-1 := by omega
  rw [hprefix,hpos] at hr
  rw [hw,silent_add,hs]
  simp only [Option.bind_some]
  exact hr

end Shared.PNP.Record285.ControlContinue
