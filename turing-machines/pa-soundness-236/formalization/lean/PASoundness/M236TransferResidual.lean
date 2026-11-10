import PASoundness.M236TransferSpace
/-! Named literal leaves select the corresponding checked return candidate. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Control
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

theorem residual_continue1 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.1" 72 false .left none))
    (first : Nat) (runs : List (Fin 6)) (bit : Bool) (residual : List Bool)
    (hcan : Continue.candidate1 pre = some (first, runs, bit, residual)) :
    transferResidual (pre ++ [last]) = some residual := by
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  simp [transferResidual, hn, hcan]

theorem residual_continue2 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.2" 73 false .left none))
    (first second : Nat) (runs : List (Fin 6)) (bit : Bool) (residual : List Bool)
    (hcan : Continue.candidate2 pre = some (first, second, runs, bit, residual)) :
    transferResidual (pre ++ [last]) = some residual := by
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  simp [transferResidual, hn, hcan]

theorem residual_continue3 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.3" 74 false .left none))
    (first second third : Nat) (runs : List (Fin 6)) (bit : Bool) (residual : List Bool)
    (hcan : Continue.candidate3 pre = some (first, second, third, runs, bit, residual)) :
    transferResidual (pre ++ [last]) = some residual := by
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  simp [transferResidual, hn, hcan]

theorem residual_break1 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.1" 69 false .left none))
    (first scratch : Nat) (runs : List (Fin 6)) (bit : Bool) (residual : List Bool)
    (hcan : Break.candidate1 pre = some (first, scratch, runs, bit, residual)) :
    transferResidual (pre ++ [last]) = some residual := by
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  simp [transferResidual, hn, hcan]

theorem residual_break3 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.3" 71 false .left none))
    (first second third scratch : Nat) (runs : List (Fin 6)) (bit : Bool) (residual : List Bool)
    (hcan : Break.candidate3 pre = some (first, second, third, scratch, runs, bit, residual)) :
    transferResidual (pre ++ [last]) = some residual := by
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  simp [transferResidual, hn, hcan]

theorem residual_emit_continue (b : Bool) (pre : List Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [false])
      (.leaf (Emit.emitName b) 72 true .left (some b)))
    (first : Nat) (runs : List (Fin 6)) (bit : Bool) (residual : List Bool)
    (hcan : Emit.continueCandidate pre = some (first, runs, bit, residual)) :
    transferResidual (pre ++ [false]) = some residual := by
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  cases b <;> simp [transferResidual, Emit.emitName, hn, hcan, List.reverse_append]

theorem residual_emit_cleanup (b : Bool) (pre : List Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [true])
      (.leaf (Emit.emitName b) 68 false .left (some b)))
    (scratch : Nat) (runs : List (Fin 6)) (bit : Bool) (residual : List Bool)
    (hcan : Emit.cleanupCandidate pre = some (scratch, runs, bit, residual)) :
    transferResidual (pre ++ [true]) = some residual := by
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  cases b <;> simp [transferResidual, Emit.emitName, hn, hcan, List.reverse_append]

/-- A checked literal transfer candidate preserves a sufficient gap budget
and exposes the resolved next path with both zero separators. -/
theorem normalize_transfer_budget (word residual next : List Bool) (gap : Nat)
    (hpath : Grammar.LeafPath Grammar.nodes 157 word)
    (hres : transferResidual word = some residual)
    (hnext : resolveZeros Grammar.nodes 158 157 residual = some next)
    (hbudget : 25 ≤ gap + word.length) (suffix : List Bool) :
    ∃ gap', residual ++ (List.replicate (2 + gap) false ++ suffix) =
        next ++ false :: false :: (List.replicate gap' false ++ suffix) ∧
      next.length + gap' = word.length + gap ∧ 25 ≤ next.length + gap' := by
  obtain ⟨hlen, hfit⟩ := transfer_space_extracted word residual next hpath hres hnext
  have hleaf := resolveZeros_sound Grammar.nodes 158 157 residual next hnext
  have hlenNext := leaf_length_le next hleaf
  have hmargin : next.length ≤ gap + word.length := by omega
  obtain ⟨gap', hf, hc⟩ := transfer_gap_factor word residual next gap hlen hfit hmargin suffix
  exact ⟨gap', hf, hc, by omega⟩

theorem two_zeros (gap : Nat) (suffix : List Bool) :
    List.replicate (2 + gap) false ++ suffix = false :: false :: (List.replicate gap false ++ suffix) := by
  rw [← List.replicate_append_replicate]
  rfl
end PASoundness.M236.Control
