import PASoundness.PeanoBetaCRTResidueSelect

/-! Standard-model meaning of the bounded target-relation totality premise and
selected residue. These semantic facts are separate from the PA derivations. -/
namespace PASoundness.PeanoBetaCRTTotalityMeaning
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoBetaCRTResidueSelect

theorem totality_realize (φ : Peano.Formula) (ρ : Nat → Nat) :
    (totality φ).Realize ρ ↔
      ∀ j : Nat, j < ρ 8 → ∃ r : Nat,
        φ.Realize (Function.update (Function.update ρ 2 j) 3 r) ∧
          r < ((j + 1) * ρ 1 + 1) := by
  classical
  simp [totality, FOL.existsAt, FOL.realize_allAt, Classical.not_forall,
    CompactArithmetic.realize_less, CompactArithmetic.modulus,
    Peano.realize_succ, Peano.realize_mul, Function.update]

/-- The simultaneous selected instance updates the relation's index/value
names without changing any other assignment. -/
theorem selected_realize (φ : Peano.Formula) (ρ : Nat → Nat) :
    (PeanoBetaCRTSelect.selected φ).Realize ρ ↔
      φ.Realize (Function.update (Function.update ρ 2 (ρ 7)) 3 (ρ 13)) := by
  rw [PeanoBetaCRTSelect.selected, FOL.realize_subst]
  have h : (fun x : Nat => ((if x = 2 then (.var 7 : Peano.Term) else
      if x = 3 then .var 13 else .var x)).realize ρ) =
      Function.update (Function.update ρ 2 (ρ 7)) 3 (ρ 13) := by
    funext x
    by_cases hx2 : x = 2
    · subst x; simp [Function.update]
    · by_cases hx3 : x = 3
      · subst x; simp [Function.update]
      · simp [hx2,hx3,Function.update]
  rw [h]

/-- Exact standard meaning of the selected-residue existential. The update at
name 13 remains visible when φ is not assumed fresh there. -/
theorem residue_realize_exact (φ : Peano.Formula) (ρ : Nat → Nat) :
    (PeanoBetaCRTSelect.residueExists φ).Realize ρ ↔
      ∃ r : Nat, φ.Realize (Function.update (Function.update (Function.update ρ 13 r)
        2 (ρ 7)) 3 r) ∧ r < ((ρ 7 + 1) * ρ 1 + 1) := by
  classical
  simp [PeanoBetaCRTSelect.residueExists, PeanoBetaCRTSelect.bound,
    FOL.existsAt, FOL.realize_allAt, Classical.not_forall, selected_realize,
    CompactArithmetic.realize_less, CompactArithmetic.modulus,
    Peano.realize_succ, Peano.realize_mul, Function.update]

/-- If the residue-witness name is fresh in φ, its external assignment is
unaffected; the intended bound-variable meaning follows. -/
theorem residue_realize (φ : Peano.Formula) (ρ : Nat → Nat)
    (hφ13 : 13 ∉ φ.freeVarFinset) :
    (PeanoBetaCRTSelect.residueExists φ).Realize ρ ↔
      ∃ r : Nat, φ.Realize (Function.update (Function.update ρ 2 (ρ 7)) 3 r) ∧
        r < ((ρ 7 + 1) * ρ 1 + 1) := by
  rw [residue_realize_exact]
  apply exists_congr
  intro r
  have h := FOL.realize_agree φ
    (Function.update (Function.update (Function.update ρ 13 r) 2 (ρ 7)) 3 r)
    (Function.update (Function.update ρ 2 (ρ 7)) 3 r) (by
      intro x hx
      have hx13 : x ≠ 13 := by intro he; subst x; exact hφ13 hx
      simp [Function.update, hx13])
  exact and_congr_left (fun _ => h)

end PASoundness.PeanoBetaCRTTotalityMeaning
