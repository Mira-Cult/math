import PASoundness.PAtoCompactAllTermsGuardedTotality
import PASoundness.PAtoCompactMultiplicationArbitraryFromFixed

/-! Conditional finite K generated-graph existence for all PA terms. A fixed
candidate-multiplication output proof is an explicit input; it is reallocated
and relabeled to supply the recursive graph construction. This module does not
prove that input, graph functionality, substitution, or the PA bridge. -/
namespace PASoundness.PAtoCompactAllTermsTotalityFromFixedMultiplication

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactMultiplicationGraphFromChildren

/-- The fixed-name candidate multiplication-existence statement. -/
def fixedMultiplication : Nat :=
  imp (domainAt 300 200).encode (imp (domainAt 300 30).encode
    (existsCode 32 (andF (domainAt 300 32) (mulAt 300 200 30 32)).encode))

/-- A finite K proof of fixed-name multiplication existence yields the family
at all permitted allocator names, including aliased input labels. -/
noncomputable def multiplicationExistence (fixed : KDerivation fixedMultiplication) :
    MultiplicationExistence where
  next := PASoundness.PAtoCompactMultiplicationArbitraryFromFixed.arbitrary_from_fixed fixed

/-- Under an explicit fixed-name multiplication-existence K proof and source
guard covering the mapped variables, every PA term has a canonical generated
graph output. There is no restriction on term constructors. -/
noncomputable def canonical_total {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) (t : Peano.language.Term α)
    (fixed : KDerivation fixedMultiplication)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    KDerivation (imp (guardFormula φ).encode
      (existsCode (outputName φ) (termGraph v t (outputName φ) (allocatorBase φ)).encode)) :=
  PAtoCompactAllTermsGuardedTotality.canonical_total v φ t (multiplicationExistence fixed) hcover

theorem canonical_total_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) (t : Peano.language.Term α)
    (fixed : KDerivation fixedMultiplication)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    theoremCode (certificate (canonical_total v φ t fixed hcover)) =
      imp (guardFormula φ).encode
        (existsCode (outputName φ) (termGraph v t (outputName φ) (allocatorBase φ)).encode) :=
  certificate_correct _
end PASoundness.PAtoCompactAllTermsTotalityFromFixedMultiplication
#print axioms PASoundness.PAtoCompactAllTermsTotalityFromFixedMultiplication.multiplicationExistence
#print axioms PASoundness.PAtoCompactAllTermsTotalityFromFixedMultiplication.canonical_total
#print axioms PASoundness.PAtoCompactAllTermsTotalityFromFixedMultiplication.canonical_total_certificate
