import PASoundness.PAtoCompactUnaryGraphFunctionalityFull
import PASoundness.PAtoCompactGuardedEqualityReflexivity
import PASoundness.PAtoCompactGuardedVacuity

/-! Supply the canonical PA free-variable guard to the unary graph
functionality proof, with source-variable coverage explicit. -/
namespace PASoundness.PAtoCompactUnaryGraphFunctionalityGuarded

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactGuardedEqualityReflexivity PASoundness.PAtoCompactGuardedVacuity
open PASoundness.PAtoCompactUnaryGraphFunctionalityFull

/-- If the PA formula's guard covers a unary term's variables, its guarded
candidate assumptions make any two graph outputs quotient-equivalent. -/
noncomputable def unary_functional {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) {t : Peano.language.Term α} (ht : UnaryTerm t)
    (b p q : Nat) (hb : guardBase φ ≤ b) (hp : p < b) (hq : q < b)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    KDerivation (imp (guardFormula φ).encode (imp (termGraph v t p b).encode
      (imp (termGraph v t q b).encode (equivAt b p q).encode))) := by
  have hbound : ∀ x ∈ φ.freeVarFinset, x < guardBase φ := by
    intro x hx
    have hh : x ≤ φ.freeVarFinset.sup id := Finset.le_sup (f := id) hx
    unfold guardBase
    omega
  apply PAtoCompactUnaryGraphFunctionalityFull.unary_functional v (guardFormula φ) ht b p q
  · intro a ha
    have hh := hbound (v a) (hcover a ha)
    omega
  · intro x hx
    have hh := hbound x (guardFormula_free_subset φ hx)
    omega
  · intro a ha
    have hh := hbound (v a) (hcover a ha)
    exact compose (guardFormula_projection φ (v a) (hcover a ha))
      (domainAt_transport (guardBase φ) b (v a) (by omega) (by omega))
  · exact hp
  · exact hq

end PASoundness.PAtoCompactUnaryGraphFunctionalityGuarded

#print axioms PASoundness.PAtoCompactUnaryGraphFunctionalityGuarded.unary_functional
