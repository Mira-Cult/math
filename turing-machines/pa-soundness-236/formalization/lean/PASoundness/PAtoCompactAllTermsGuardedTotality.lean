import PASoundness.PAtoCompactFullTermTotalityInduction
import PASoundness.PAtoCompactAddUnaryTotalityClosed
import PASoundness.PAtoCompactUnaryGuardedTotality
import PASoundness.PAtoCompactUnaryGuardedCanonical

/-! Source-guarded graph existence for all PA terms, conditional on an explicit
finite K multiplication existence family. This does not establish that family,
graph functionality, or PA soundness. -/
namespace PASoundness.PAtoCompactAllTermsGuardedTotality
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactMultiplicationGraphFromChildren
open PASoundness.PAtoCompactFullTermTotalityInduction
open PASoundness.PAtoCompactUnaryGuardedCanonical

/-- The source guard provides each variable candidate. The supplied multiplication family and proved addition and successor
families build all remaining graph witnesses. -/
noncomputable def guarded_total {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) (t : Peano.language.Term α)
    (times : MultiplicationExistence) (b out : Nat) (hb : out+1 < b)
    (hnames : ∀ z ∈ φ.freeVarFinset, z < out)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    KDerivation (imp (guardFormula φ).encode (existsCode out (termGraph v t out b).encode)) := by
  apply PAtoCompactFullTermTotalityInduction.total v
    PAtoCompactUnaryGuardedTotality.successorExistence
    PAtoCompactAddUnaryTotalityClosed.additionExistence times (guardFormula φ) (allTerms t) b out hb
  · intro z hz
    exact hnames z (PAtoCompactGuardedVacuity.guardFormula_free_subset φ hz)
  · intro a ha
    exact hnames (v a) (hcover a ha)
  · intro a ha
    have hm := hcover a ha
    have hle : v a ≤ φ.freeVarFinset.sup id := Finset.le_sup (f := id) hm
    have hguard : v a < guardBase φ := by unfold guardBase; omega
    exact compose
      (PAtoCompactGuardedEqualityReflexivity.guardFormula_projection φ (v a) hm)
      (PAtoCompactGuardBaseTransport.domainAt_transport (guardBase φ) b (v a)
        (by omega) (by have := hnames (v a) hm; omega))

/-- A canonical output and allocator bound above all free variables. -/
noncomputable def canonical_total {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) (t : Peano.language.Term α)
    (times : MultiplicationExistence)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    KDerivation (imp (guardFormula φ).encode
      (existsCode (outputName φ) (termGraph v t (outputName φ) (allocatorBase φ)).encode)) := by
  apply guarded_total v φ t times (allocatorBase φ) (outputName φ)
    (by simp [allocatorBase]) _ hcover
  intro z hz
  have hle : z ≤ φ.freeVarFinset.sup id := Finset.le_sup (f := id) hz
  unfold outputName guardBase
  omega

theorem guarded_total_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) (t : Peano.language.Term α)
    (times : MultiplicationExistence) (b out : Nat) (hb : out+1 < b)
    (hnames : ∀ z ∈ φ.freeVarFinset, z < out)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    theoremCode (certificate (guarded_total v φ t times b out hb hnames hcover)) =
      imp (guardFormula φ).encode (existsCode out (termGraph v t out b).encode) := certificate_correct _

theorem canonical_total_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) (t : Peano.language.Term α)
    (times : MultiplicationExistence)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    theoremCode (certificate (canonical_total v φ t times hcover)) =
      imp (guardFormula φ).encode
        (existsCode (outputName φ) (termGraph v t (outputName φ) (allocatorBase φ)).encode) :=
  certificate_correct _
end PASoundness.PAtoCompactAllTermsGuardedTotality
#print axioms PASoundness.PAtoCompactAllTermsGuardedTotality.guarded_total
#print axioms PASoundness.PAtoCompactAllTermsGuardedTotality.canonical_total
#print axioms PASoundness.PAtoCompactAllTermsGuardedTotality.guarded_total_certificate
#print axioms PASoundness.PAtoCompactAllTermsGuardedTotality.canonical_total_certificate
