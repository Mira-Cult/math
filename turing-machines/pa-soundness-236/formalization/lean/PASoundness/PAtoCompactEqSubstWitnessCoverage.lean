import PASoundness.PAtoCompactEqSubstScopedReduction
import PASoundness.PAtoCompactAllTermsTotalityClosed
import PASoundness.PAtoCompactVacuousEqualityAlignment
import PASoundness.PAtoCompactGuardedEqualityReflexivity

/-! Guard coverage and graph existence for the two replacement terms in a
PA equality-substitution axiom. Unlike the universal-elimination case, the
equality antecedent itself mentions both terms even when the substituted
variable is absent from the source formula. Equality-node alignment and
graph functionality are not established here. -/
namespace PASoundness.PAtoCompactEqSubstWitnessCoverage

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedEqualityReflexivity
open PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactEqSubstScopedReduction

/-- Both terms occur in the equality antecedent, independently of whether
the source formula contains the substituted variable. -/
theorem left_coverage (φ : Peano.Formula) (x : Nat) (t u : Peano.Term) :
    ∀ a ∈ t.varFinset, (id : Nat → Nat) a ∈ (axiomFormula φ x t u).freeVarFinset := by
  intro a ha
  simp only [id_eq, axiomFormula, BoundedFormula.freeVarFinset, eq_free, Finset.mem_union]
  exact Or.inl (Or.inl ha)

theorem right_coverage (φ : Peano.Formula) (x : Nat) (t u : Peano.Term) :
    ∀ a ∈ u.varFinset, (id : Nat → Nat) a ∈ (axiomFormula φ x t u).freeVarFinset := by
  intro a ha
  simp only [id_eq, axiomFormula, BoundedFormula.freeVarFinset, eq_free, Finset.mem_union]
  exact Or.inl (Or.inr ha)

/-- The actual sorted axiom guard supplies each variable's candidate
condition, without an occurrence hypothesis on `x`. -/
def left_guard (φ : Peano.Formula) (x : Nat) (t u : Peano.Term) (a : Nat)
    (ha : a ∈ t.varFinset) :
    KDerivation (imp (guardFormula (axiomFormula φ x t u)).encode
      (domainAt (guardBase (axiomFormula φ x t u)) a).encode) :=
  guardFormula_projection (axiomFormula φ x t u) a (left_coverage φ x t u a ha)

def right_guard (φ : Peano.Formula) (x : Nat) (t u : Peano.Term) (a : Nat)
    (ha : a ∈ u.varFinset) :
    KDerivation (imp (guardFormula (axiomFormula φ x t u)).encode
      (domainAt (guardBase (axiomFormula φ x t u)) a).encode) :=
  guardFormula_projection (axiomFormula φ x t u) a (right_coverage φ x t u a ha)

/-- Canonical graph existence for the left replacement term, under the
equality-substitution axiom's actual guard. The imported all-term totality
construction supplies the finite K proof; no model-soundness argument is used. -/
noncomputable def left_total (φ : Peano.Formula) (x : Nat) (t u : Peano.Term) :
    KDerivation (imp (guardFormula (axiomFormula φ x t u)).encode
      (existsCode (outputName (axiomFormula φ x t u))
        (termGraph id t (outputName (axiomFormula φ x t u))
          (allocatorBase (axiomFormula φ x t u))).encode)) :=
  PAtoCompactAllTermsTotalityClosed.canonical_total id (axiomFormula φ x t u) t
    (left_coverage φ x t u)

/-- The same guard supplies graph existence for the right replacement term. -/
noncomputable def right_total (φ : Peano.Formula) (x : Nat) (t u : Peano.Term) :
    KDerivation (imp (guardFormula (axiomFormula φ x t u)).encode
      (existsCode (outputName (axiomFormula φ x t u))
        (termGraph id u (outputName (axiomFormula φ x t u))
          (allocatorBase (axiomFormula φ x t u))).encode)) :=
  PAtoCompactAllTermsTotalityClosed.canonical_total id (axiomFormula φ x t u) u
    (right_coverage φ x t u)

end PASoundness.PAtoCompactEqSubstWitnessCoverage

#print axioms PASoundness.PAtoCompactEqSubstWitnessCoverage.left_coverage
#print axioms PASoundness.PAtoCompactEqSubstWitnessCoverage.right_coverage
#print axioms PASoundness.PAtoCompactEqSubstWitnessCoverage.left_guard
#print axioms PASoundness.PAtoCompactEqSubstWitnessCoverage.right_guard
#print axioms PASoundness.PAtoCompactEqSubstWitnessCoverage.left_total
#print axioms PASoundness.PAtoCompactEqSubstWitnessCoverage.right_total
