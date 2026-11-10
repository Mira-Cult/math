import PASoundness.PAtoCompactAddUnaryGuardedTotality
import PASoundness.PAtoCompactAdditionArbitraryTotality

/-! Unconditional finite K graph existence for PA terms built from variables,
zero, successor and addition under a source guard covering their variables.
This does not establish multiplication, graph functionality or the PA bridge. -/
namespace PASoundness.PAtoCompactAddUnaryTotalityClosed
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactAdditionGraphFromChildren
open PASoundness.PAtoCompactAddUnaryTotalityInduction

/-- The proved arbitrary-label candidate addition family discharges the
operation proof input for the generated graph induction. -/
noncomputable def additionExistence : AdditionExistence where
  next := PAtoCompactAdditionArbitraryTotality.addition_total

/-- The canonical generated graph has an output, assuming the source guard
covers the term variables. This works for arbitrary nesting of addition and
successor, including aliased source-variable names. -/
noncomputable def canonical_total {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) {t : Peano.language.Term α} (h : AddUnaryTerm t)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    KDerivation (imp (guardFormula φ).encode
      (existsCode (outputName φ) (termGraph v t (outputName φ) (allocatorBase φ)).encode)) :=
  PAtoCompactAddUnaryGuardedTotality.canonical_total v φ h additionExistence hcover

theorem canonical_total_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) {t : Peano.language.Term α} (h : AddUnaryTerm t)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    theoremCode (certificate (canonical_total v φ h hcover)) =
      imp (guardFormula φ).encode
        (existsCode (outputName φ) (termGraph v t (outputName φ) (allocatorBase φ)).encode) :=
  certificate_correct _
end PASoundness.PAtoCompactAddUnaryTotalityClosed
#print axioms PASoundness.PAtoCompactAddUnaryTotalityClosed.additionExistence
#print axioms PASoundness.PAtoCompactAddUnaryTotalityClosed.canonical_total
#print axioms PASoundness.PAtoCompactAddUnaryTotalityClosed.canonical_total_certificate
