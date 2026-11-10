import PASoundness.PAtoCompactAllTermsTotalityFromFixedMultiplication
import PASoundness.PAtoCompactMultiplicationCandidateTotalityClosed

/-! Finite K generated-graph existence for every PA term, under a source
guard covering the mapped term variables. The multiplication-existence
family is supplied from the fixed candidate-multiplication theorem. This does
not establish graph functionality, formula substitution, PA proof transport,
or the PA soundness equivalence. -/
namespace PASoundness.PAtoCompactAllTermsTotalityClosed

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactMultiplicationGraphFromChildren

/-- Candidate multiplication output existence at the precise interface used
by the generated-graph induction; syntactic input labels may coincide. -/
noncomputable def multiplicationExistence : MultiplicationExistence :=
  PAtoCompactAllTermsTotalityFromFixedMultiplication.multiplicationExistence
    PAtoCompactMultiplicationCandidateTotalityClosed.candidate_total

/-- A source guard covering the mapped term variables supplies a generated
term-graph output at any explicitly fresh output and allocator names. -/
noncomputable def guarded_total {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) (t : Peano.language.Term α) (b out : Nat)
    (hb : out + 1 < b) (hnames : ∀ z ∈ φ.freeVarFinset, z < out)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    KDerivation (imp (guardFormula φ).encode
      (existsCode out (termGraph v t out b).encode)) :=
  PAtoCompactAllTermsGuardedTotality.guarded_total v φ t multiplicationExistence
    b out hb hnames hcover

/-- Every PA term has a canonical generated-graph output under a source
guard covering its mapped variables. Arbitrary nesting of all four arithmetic
operations is supported; there is no multiplication-existence proof input. -/
noncomputable def canonical_total {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) (t : Peano.language.Term α)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    KDerivation (imp (guardFormula φ).encode
      (existsCode (outputName φ) (termGraph v t (outputName φ) (allocatorBase φ)).encode)) :=
  PAtoCompactAllTermsGuardedTotality.canonical_total v φ t multiplicationExistence hcover

theorem guarded_total_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) (t : Peano.language.Term α) (b out : Nat)
    (hb : out + 1 < b) (hnames : ∀ z ∈ φ.freeVarFinset, z < out)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    theoremCode (certificate (guarded_total v φ t b out hb hnames hcover)) =
      imp (guardFormula φ).encode (existsCode out (termGraph v t out b).encode) :=
  certificate_correct _

theorem canonical_total_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) (t : Peano.language.Term α)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    theoremCode (certificate (canonical_total v φ t hcover)) =
      imp (guardFormula φ).encode
        (existsCode (outputName φ) (termGraph v t (outputName φ) (allocatorBase φ)).encode) :=
  certificate_correct _
end PASoundness.PAtoCompactAllTermsTotalityClosed
#print axioms PASoundness.PAtoCompactAllTermsTotalityClosed.multiplicationExistence
#print axioms PASoundness.PAtoCompactAllTermsTotalityClosed.guarded_total
#print axioms PASoundness.PAtoCompactAllTermsTotalityClosed.canonical_total
#print axioms PASoundness.PAtoCompactAllTermsTotalityClosed.guarded_total_certificate
#print axioms PASoundness.PAtoCompactAllTermsTotalityClosed.canonical_total_certificate
