import PASoundness.PeanoBetaCRTAlpha

/-! Syntactic normalization of an outer parameter to the canonical bound
index used by the finite-selector construction. -/
namespace PASoundness.PeanoAX8PredicateNormalize
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic

/-- Rename the free outer parameter 5 to the canonical index 1. -/
def normalized (ρ : Peano.Formula) : Peano.Formula :=
  FOL.substAt ρ 5 (.var 1)

/-- If index 1 was fresh in the original predicate, restoring the outer
parameter recovers its exact syntax, including all other parameters. -/
theorem normalized_roundtrip (ρ : Peano.Formula) (h1 : 1 ∉ ρ.freeVarFinset) :
    FOL.substAt (normalized ρ) 1 (.var 5) = ρ :=
  PeanoBetaCRTAlpha.subst_roundtrip ρ 5 1 (by decide) h1

/-- The outer name is absent after normalization, irrespective of its
occurrences in the original predicate. -/
theorem normalized_outer_fresh (ρ : Peano.Formula) :
    5 ∉ (normalized ρ).freeVarFinset :=
  PeanoBetaCRTAlpha.subst_rename_fresh ρ 5 1 (by decide)

/-- A name different from the new index remains absent if it was absent
before normalization. -/
theorem normalized_preserves_fresh (ρ : Peano.Formula) (k : Nat)
    (hk1 : k ≠ 1) (hk : k ∉ ρ.freeVarFinset) :
    k ∉ (normalized ρ).freeVarFinset := by
  unfold normalized FOL.substAt
  rw [SyntaxTransport.formula_subst_freeVars]
  rintro ⟨x,hx,h⟩
  by_cases hx5 : x = 5
  · subst x
    simp [FirstOrder.Language.Term.varFinset, hk1] at h
  · have he : k = x := by simpa [hx5, FirstOrder.Language.Term.varFinset] using h
    subst x
    exact hk hx

/-- In particular, the invariant's bound, power and code names remain
fresh for the normalized predicate under the displayed explicit conditions. -/
theorem normalized_invariant_fresh (ρ : Peano.Formula)
    (h0 : 0 ∉ ρ.freeVarFinset) (h2 : 2 ∉ ρ.freeVarFinset)
    (h3 : 3 ∉ ρ.freeVarFinset) :
    0 ∉ (normalized ρ).freeVarFinset ∧
      2 ∉ (normalized ρ).freeVarFinset ∧
      3 ∉ (normalized ρ).freeVarFinset :=
  ⟨normalized_preserves_fresh ρ 0 (by decide) h0,
    normalized_preserves_fresh ρ 2 (by decide) h2,
    normalized_preserves_fresh ρ 3 (by decide) h3⟩

end PASoundness.PeanoAX8PredicateNormalize

#print axioms PASoundness.PeanoAX8PredicateNormalize.normalized_roundtrip
#print axioms PASoundness.PeanoAX8PredicateNormalize.normalized_invariant_fresh
