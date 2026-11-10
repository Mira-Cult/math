import PASoundness.M236EmitCoverage
/-! Checked next-leaf destinations for both fused-output row forms. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Emit
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def successorOK (word : List Bool) : Bool :=
  let pre := word.dropLast
  match Continue.pathName 157 word with
  | some "emit.0" | some "emit.1" =>
    match word.reverse, Break.successorPrefix 0 word with
    | false :: _, some source =>
      match continueCandidate pre with
      | some (_, _, _, residual) => Continue.sameResolved source residual && Continue.fitsPadding residual
      | none => false
    | true :: _, some source =>
      match cleanupCandidate pre with
      | some (_, _, _, residual) => Continue.sameResolved source residual && Continue.fitsPadding residual
      | none => false
    | _, _ => false
  | _ => true

/-- Every literal output occurrence has its formal successor destination and
the next leaf fits within the returned path plus two zero cells. -/
theorem successor_checked : Grammar.completePaths.all successorOK = true := by decide

theorem continue_destination (b : Bool) (pre : List Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [false])
      (.leaf (emitName b) 72 true .left (some b)))
    (first : Nat) (runs : List (Fin 6)) (bit : Bool) (residual : List Bool)
    (hcan : continueCandidate pre = some (first, runs, bit, residual)) :
    ∃ source next, Break.successorPrefix 0 (pre ++ [false]) = some source ∧
      Control.resolveZeros Grammar.nodes 158 157 source = some next ∧
      Control.resolveZeros Grammar.nodes 158 157 residual = some next ∧
      next <+: residual ++ List.replicate 2 false := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp successor_checked) (pre ++ [false]) hm
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  have hc' : (match Break.successorPrefix 0 (pre ++ [false]) with
      | some source => Continue.sameResolved source residual && Continue.fitsPadding residual
      | none => false) = true := by
    cases hx : Break.successorPrefix 0 (pre ++ [false]) <;> cases b <;>
      simpa [successorOK, emitName, hn, List.reverse_append, hcan, hx] using hc
  cases hs : Break.successorPrefix 0 (pre ++ [false]) with
  | none => simp [hs] at hc'
  | some source =>
    have hh : Continue.sameResolved source residual = true ∧ Continue.fitsPadding residual = true := by
      simpa [hs] using hc'
    obtain ⟨next, h1, h2⟩ := Continue.sameResolved_sound source residual hh.1
    have hp : next <+: residual ++ List.replicate 2 false := by
      unfold Continue.fitsPadding at hh
      rw [h2] at hh
      exact of_decide_eq_true hh.2
    exact ⟨source, next, rfl, h1, h2, hp⟩

theorem cleanup_destination (b : Bool) (pre : List Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [true])
      (.leaf (emitName b) 68 false .left (some b)))
    (scratch : Nat) (runs : List (Fin 6)) (bit : Bool) (residual : List Bool)
    (hcan : cleanupCandidate pre = some (scratch, runs, bit, residual)) :
    ∃ source next, Break.successorPrefix 0 (pre ++ [true]) = some source ∧
      Control.resolveZeros Grammar.nodes 158 157 source = some next ∧
      Control.resolveZeros Grammar.nodes 158 157 residual = some next ∧
      next <+: residual ++ List.replicate 2 false := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp successor_checked) (pre ++ [true]) hm
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  have hc' : (match Break.successorPrefix 0 (pre ++ [true]) with
      | some source => Continue.sameResolved source residual && Continue.fitsPadding residual
      | none => false) = true := by
    cases hx : Break.successorPrefix 0 (pre ++ [true]) <;> cases b <;>
      simpa [successorOK, emitName, hn, List.reverse_append, hcan, hx] using hc
  cases hs : Break.successorPrefix 0 (pre ++ [true]) with
  | none => simp [hs] at hc'
  | some source =>
    have hh : Continue.sameResolved source residual = true ∧ Continue.fitsPadding residual = true := by
      simpa [hs] using hc'
    obtain ⟨next, h1, h2⟩ := Continue.sameResolved_sound source residual hh.1
    have hp : next <+: residual ++ List.replicate 2 false := by
      unfold Continue.fitsPadding at hh
      rw [h2] at hh
      exact of_decide_eq_true hh.2
    exact ⟨source, next, rfl, h1, h2, hp⟩
end PASoundness.M236.Emit
