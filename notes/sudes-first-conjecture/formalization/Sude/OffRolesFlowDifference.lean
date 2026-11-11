import Sude.Statement
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Transport line differences under a cell permutation which fixes the
active roles. The two supplied squares must agree off those roles. This does
not construct the permutation or squares, bound absolute line sums, or prove
any prime target or completion. -/

namespace Sude
noncomputable section

/-- A permutation fixing the roles cannot move an off-role point into them. -/
theorem off_roles_perm_outside {α : Type*} (roles : Set α)
    (σ : Equiv.Perm α) (hfix : ∀ x ∈ roles, σ x = x)
    {x : α} (hx : x ∉ roles) : σ x ∉ roles := by
  intro hσx
  have heq : σ x = x := σ.injective (hfix (σ x) hσx)
  exact hx (heq ▸ hσx)

/-- Precomposing two functions by a permutation that fixes the roles leaves
their pointwise difference unchanged, when they agree off the roles. -/
theorem off_roles_perm_difference {α : Type*} (roles : Set α)
    (σ : Equiv.Perm α) (out base : α → ℤ)
    (hfix : ∀ x ∈ roles, σ x = x)
    (hoff : ∀ x ∉ roles, out x = base x) (x : α) :
    out (σ x) - base (σ x) = out x - base x := by
  by_cases hx : x ∈ roles
  · rw [hfix x hx]
  · have hσx := off_roles_perm_outside roles σ hfix hx
    rw [hoff (σ x) hσx, hoff x hx]
    simp

/-- Pointwise agreement on any supplied set is retained even if the
permutation does not preserve that set. -/
theorem off_roles_perm_agreement {α β : Type*} (roles : Set α)
    (σ : Equiv.Perm α) (out base : α → β)
    (hfix : ∀ x ∈ roles, σ x = x)
    (hoff : ∀ x ∉ roles, out x = base x)
    {x : α} (hx : out x = base x) : out (σ x) = base (σ x) := by
  by_cases hrole : x ∈ roles
  · simpa only [hfix x hrole] using hx
  · exact hoff (σ x) (off_roles_perm_outside roles σ hfix hrole)

/-- Any indexed line has the same output-minus-base sum after the shared
permutation. The indexing may repeat points. -/
theorem off_roles_perm_line_difference {α ι : Type*} [Fintype ι]
    (roles : Set α) (σ : Equiv.Perm α) (out base : α → ℤ)
    (hfix : ∀ x ∈ roles, σ x = x)
    (hoff : ∀ x ∉ roles, out x = base x) (line : ι → α) :
    (∑ i, out (σ (line i))) - (∑ i, base (σ (line i))) =
      (∑ i, out (line i)) - (∑ i, base (line i)) := by
  classical
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => off_roles_perm_difference roles σ out base hfix hoff (line i))

/-- The four physical line differences are preserved simultaneously.  For a
given flow output, this can be used with its exact off-roles agreement. -/
theorem off_roles_perm_physical_differences {n : ℕ}
    (roles : Finset (Cell n)) (σ : Equiv.Perm (Cell n))
    (out base : Cell n ≃ Fin (n*n))
    (hfix : ∀ z ∈ roles, σ z = z)
    (hoff : ∀ z ∉ roles, entry out z = entry base z) :
    (∀ r, (rowSum (σ.trans out) r : ℤ) - (rowSum (σ.trans base) r : ℤ) =
      (rowSum out r : ℤ) - (rowSum base r : ℤ)) ∧
    (∀ c, (columnSum (σ.trans out) c : ℤ) - (columnSum (σ.trans base) c : ℤ) =
      (columnSum out c : ℤ) - (columnSum base c : ℤ)) ∧
    ((mainSum (σ.trans out) : ℤ) - (mainSum (σ.trans base) : ℤ) =
      (mainSum out : ℤ) - (mainSum base : ℤ)) ∧
    ((antiSum (σ.trans out) : ℤ) - (antiSum (σ.trans base) : ℤ) =
      (antiSum out : ℤ) - (antiSum base : ℤ)) := by
  classical
  let valsOut : Cell n → ℤ := fun z => (entry out z : ℤ)
  let valsBase : Cell n → ℤ := fun z => (entry base z : ℤ)
  have hfix' : ∀ z ∈ (roles : Set (Cell n)), σ z = z := hfix
  have hoff' : ∀ z ∉ (roles : Set (Cell n)), valsOut z = valsBase z := by
    intro z hz
    change (entry out z : ℤ) = (entry base z : ℤ)
    exact_mod_cast hoff z hz
  constructor
  · intro r
    simpa only [rowSum, entry, Equiv.trans_apply, Nat.cast_sum, valsOut, valsBase] using
      off_roles_perm_line_difference (roles : Set (Cell n)) σ valsOut valsBase hfix' hoff'
        (fun c : Fin n => (r,c))
  constructor
  · intro c
    simpa only [columnSum, entry, Equiv.trans_apply, Nat.cast_sum, valsOut, valsBase] using
      off_roles_perm_line_difference (roles : Set (Cell n)) σ valsOut valsBase hfix' hoff'
        (fun r : Fin n => (r,c))
  constructor
  · simpa only [mainSum, entry, Equiv.trans_apply, Nat.cast_sum, valsOut, valsBase] using
      off_roles_perm_line_difference (roles : Set (Cell n)) σ valsOut valsBase hfix' hoff'
        (fun i : Fin n => (i,i))
  · simpa only [antiSum, entry, Equiv.trans_apply, Nat.cast_sum, valsOut, valsBase] using
      off_roles_perm_line_difference (roles : Set (Cell n)) σ valsOut valsBase hfix' hoff'
        (fun i : Fin n => (i,i.rev))

end
end Sude
