import PASoundness.PAtoCompactUnaryGuardedTotality

/-! A concrete fresh output and allocation base for guarded unary-term
existence. This proves no functionality or binary arithmetic totality. -/
namespace PASoundness.PAtoCompactUnaryGuardedCanonical

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactUnaryTermTransport

/-- Choose the first name above the source formula's free-variable labels. -/
def outputName (φ : Peano.Formula) : Nat := guardBase φ

/-- Reserve one further name for the unary recursion's temporary witness. -/
def allocatorBase (φ : Peano.Formula) : Nat := outputName φ + 2

/-- Under the formula's guard, a unary-fragment term has a graph value at
concretely chosen fresh names whenever the guard covers its source variables. -/
noncomputable def unary_total {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) {t : Peano.language.Term α} (h : UnaryTerm t)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    KDerivation (imp (guardFormula φ).encode
      (existsCode (outputName φ) (termGraph v t (outputName φ) (allocatorBase φ)).encode)) := by
  apply PAtoCompactUnaryGuardedTotality.unary_total v φ h (allocatorBase φ) (outputName φ)
    (by simp [allocatorBase]) _ hcover
  intro z hz
  have hle : z ≤ φ.freeVarFinset.sup id := Finset.le_sup (f := id) hz
  unfold outputName guardBase
  omega

theorem unary_total_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) {t : Peano.language.Term α} (h : UnaryTerm t)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    theoremCode (certificate (unary_total v φ h hcover)) =
      imp (guardFormula φ).encode
        (existsCode (outputName φ) (termGraph v t (outputName φ) (allocatorBase φ)).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactUnaryGuardedCanonical

#print axioms PASoundness.PAtoCompactUnaryGuardedCanonical.unary_total
#print axioms PASoundness.PAtoCompactUnaryGuardedCanonical.unary_total_certificate
