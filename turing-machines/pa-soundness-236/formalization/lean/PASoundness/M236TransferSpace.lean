import PASoundness.M236GapInvariant
import PASoundness.M236EmitSuccessor
/-! Reflected zero-space preservation for literal transfer and output leaves. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def fitsTransferSpace (word residual : List Bool) : Bool :=
  match resolveZeros Grammar.nodes 158 157 residual with
  | none => false
  | some next => decide (residual.length = word.length ∧
      residual ++ List.replicate 2 false = next ++
        List.replicate ((residual.length + 2) - next.length) false)

/-- Extract only the returned control word; coverage of named leaves is
proved separately by the continue, break, and output candidate theorems. -/
def transferResidual (word : List Bool) : Option (List Bool) :=
  let pre := word.dropLast
  match Continue.pathName 157 word with
  | some "_continue.1" => (Continue.candidate1 pre).map (fun (_, _, _, residual) => residual)
  | some "_continue.2" => (Continue.candidate2 pre).map (fun (_, _, _, _, residual) => residual)
  | some "_continue.3" => (Continue.candidate3 pre).map (fun (_, _, _, _, _, residual) => residual)
  | some "_break.1" => (Break.candidate1 pre).map (fun (_, _, _, _, residual) => residual)
  | some "_break.3" => (Break.candidate3 pre).map (fun (_, _, _, _, _, _, residual) => residual)
  | some "emit.0" | some "emit.1" =>
    match word.reverse with
    | false :: _ => (Emit.continueCandidate pre).map (fun (_, _, _, residual) => residual)
    | true :: _ => (Emit.cleanupCandidate pre).map (fun (_, _, _, residual) => residual)
    | _ => none
  | _ => none

def transferSpaceOK (word : List Bool) : Bool :=
  match transferResidual word with
  | some residual => fitsTransferSpace word residual
  | none => true

/-- Every returned literal transfer/output candidate retains the same
control-space length and has a zero-only suffix after its next leaf. -/
theorem transfer_space_checked : Grammar.completePaths.all transferSpaceOK = true := by decide

theorem transfer_space_extracted (word residual next : List Bool)
    (hpath : Grammar.LeafPath Grammar.nodes 157 word)
    (hres : transferResidual word = some residual)
    (hnext : resolveZeros Grammar.nodes 158 157 residual = some next) :
    residual.length = word.length ∧ residual ++ List.replicate 2 false = next ++
      List.replicate ((residual.length + 2) - next.length) false := by
  have hm := Grammar.every_leaf_path word hpath
  have hc := (List.all_eq_true.mp transfer_space_checked) word hm
  unfold transferSpaceOK at hc
  rw [hres] at hc
  simp only at hc
  unfold fitsTransferSpace at hc
  rw [hnext] at hc
  exact of_decide_eq_true hc

/-- A checked transfer suffix and a sufficient total budget yield the next
literal path, two separator zeros, and the same path-length-plus-gap budget. -/
theorem transfer_gap_factor (word residual next : List Bool) (gap : Nat)
    (hlen : residual.length = word.length)
    (hfit : residual ++ List.replicate 2 false = next ++
      List.replicate ((residual.length + 2) - next.length) false)
    (hmargin : next.length ≤ gap + word.length) (suffix : List Bool) :
    ∃ gap', residual ++ (List.replicate (2 + gap) false ++ suffix) =
        next ++ false :: false :: (List.replicate gap' false ++ suffix) ∧
      next.length + gap' = word.length + gap := by
  have hnext : next.length ≤ residual.length + 2 := by
    have h := congrArg List.length hfit
    simp only [List.length_append, List.length_replicate] at h
    omega
  let gap' := residual.length + gap - next.length
  have hz : (residual.length + 2 - next.length) + gap = 2 + gap' := by dsimp [gap']; omega
  refine ⟨gap', ?_, ?_⟩
  · calc
      _ = (residual ++ List.replicate 2 false) ++ (List.replicate gap false ++ suffix) := by
        rw [← List.replicate_append_replicate]
        simp [List.append_assoc]
      _ = (next ++ List.replicate (residual.length + 2 - next.length) false) ++
          (List.replicate gap false ++ suffix) := congrArg
            (fun xs : List Bool => xs ++ (List.replicate gap false ++ suffix)) hfit
      _ = next ++ (List.replicate ((residual.length + 2 - next.length) + gap) false ++ suffix) := by
        have heq : List.replicate (residual.length + 2 - next.length) false ++
            (List.replicate gap false ++ suffix) =
            List.replicate ((residual.length + 2 - next.length) + gap) false ++ suffix := by
          rw [← List.append_assoc, List.replicate_append_replicate]
        simpa only [List.append_assoc] using congrArg (fun xs : List Bool => next ++ xs) heq
      _ = next ++ (List.replicate (2 + gap') false ++ suffix) := by rw [hz]
      _ = _ := by
        have hz' : List.replicate (2 + gap') false = [false, false] ++ List.replicate gap' false := by
          simpa using (List.replicate_append_replicate (n := 2) (m := gap') (a := false)).symm
        rw [hz']
        rfl
  · dsimp [gap']; omega
end PASoundness.M236.Control
