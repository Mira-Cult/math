import PASoundness.PeanoBetaCRTAlignment
import PASoundness.PeanoBetaCRTInvariant

/-! Standard meaning of the beta CRT invariant at the bounded endpoint.
This semantic characterization is separate from all PA proof constructions. -/
namespace PASoundness.PeanoBetaCRTEndpointMeaning
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic PeanoDivisibility
open PeanoBetaCRTInvariant

theorem endpoint_realize_exact (φ : Peano.Formula) (ρ : Nat → Nat) :
    (invariantAt φ (.var 8)).Realize ρ ↔
      ∃ p b : Nat,
        (∀ j : Nat, j < ρ 8 → ∃ r : Nat,
          φ.Realize (Function.update (Function.update
            (Function.update (Function.update ρ 10 p) 9 b) 2 j) 3 r) ∧
            Beta b (ρ 1) j r) ∧
        (∀ j : Nat, j < ρ 8 → ∃ q : Nat, p = q * ((j + 1) * ρ 1 + 1)) := by
  classical
  simp [invariantAt, invariantWith, matrixAt, rowsAt, factorsAt, futureAt,
    FOL.existsAt, FOL.realize_allAt, Classical.not_forall, CompactArithmetic.realize_less,
    PeanoDivisibility.divides_realize, CompactArithmetic.modulus,
    Peano.realize_succ, Peano.realize_mul, Function.update]

/-- At k=N the future-index guard is vacuous. If code/product witness names
are fresh in φ, the same row value is visible in φ and beta without capturing
external relation parameters. This is standard semantics, not a PA derivation. -/
theorem endpoint_realize (φ : Peano.Formula) (ρ : Nat → Nat)
    (hφ9 : 9 ∉ φ.freeVarFinset) (hφ10 : 10 ∉ φ.freeVarFinset) :
    (invariantAt φ (.var 8)).Realize ρ ↔
      ∃ p b : Nat,
        (∀ j : Nat, j < ρ 8 → ∃ r : Nat,
          φ.Realize (Function.update (Function.update ρ 2 j) 3 r) ∧
            Beta b (ρ 1) j r) ∧
        (∀ j : Nat, j < ρ 8 → ∃ q : Nat, p = q * ((j + 1) * ρ 1 + 1)) := by
  rw [endpoint_realize_exact]
  apply exists_congr
  intro p
  apply exists_congr
  intro b
  have hrows : (∀ j : Nat, j < ρ 8 → ∃ r : Nat,
      φ.Realize (Function.update (Function.update
        (Function.update (Function.update ρ 10 p) 9 b) 2 j) 3 r) ∧
        Beta b (ρ 1) j r) ↔
      (∀ j : Nat, j < ρ 8 → ∃ r : Nat,
        φ.Realize (Function.update (Function.update ρ 2 j) 3 r) ∧
          Beta b (ρ 1) j r) := by
    apply forall_congr'
    intro j
    apply imp_congr_right
    intro _
    apply exists_congr
    intro r
    have h := FOL.realize_agree φ
      (Function.update (Function.update (Function.update (Function.update ρ 10 p) 9 b) 2 j) 3 r)
      (Function.update (Function.update ρ 2 j) 3 r) (by
        intro x hx
        have hx9 : x ≠ 9 := by intro he; subst x; exact hφ9 hx
        have hx10 : x ≠ 10 := by intro he; subst x; exact hφ10 hx
        simp [Function.update, hx9, hx10])
    exact and_congr h Iff.rfl
  exact and_congr hrows Iff.rfl

/-- The alignment convention supplies the two freshness conditions needed for
the clean endpoint meaning. -/
theorem endpoint_realize_namesSafe (φ : Peano.Formula) (ρ : Nat → Nat)
    (hφ : PeanoBetaCRTAlignment.NamesSafe φ) :
    (invariantAt φ (.var 8)).Realize ρ ↔
      ∃ p b : Nat,
        (∀ j : Nat, j < ρ 8 → ∃ r : Nat,
          φ.Realize (Function.update (Function.update ρ 2 j) 3 r) ∧
            Beta b (ρ 1) j r) ∧
        (∀ j : Nat, j < ρ 8 → ∃ q : Nat, p = q * ((j + 1) * ρ 1 + 1)) := by
  have h9 : 9 ∉ φ.freeVarFinset := by
    intro h; have hx := hφ 9 h; simp [PeanoBetaCRTAlignment.reservedNames] at hx
  have h10 : 10 ∉ φ.freeVarFinset := by
    intro h; have hx := hφ 10 h; simp [PeanoBetaCRTAlignment.reservedNames] at hx
  exact endpoint_realize φ ρ h9 h10

end PASoundness.PeanoBetaCRTEndpointMeaning
