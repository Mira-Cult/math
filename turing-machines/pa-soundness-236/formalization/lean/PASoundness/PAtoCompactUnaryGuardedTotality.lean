import PASoundness.PAtoCompactUnaryTotalityInduction
import PASoundness.PAtoCompactSuccessorQuotientExistence
import PASoundness.PAtoCompactGuardedVacuity
import PASoundness.PAtoCompactGuardedEqualityReflexivity

/-! Guarded existence for the unary PA term fragment. The source guard must
cover the term variables. This does not address addition or multiplication,
term-graph functionality, or the full PA interpretation. -/
namespace PASoundness.PAtoCompactUnaryGuardedTotality

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactUnaryTotalityInduction

/-- The previously constructed quotient-successor proof supplies the full
finite K proof family required by the unary totality induction. -/
def successorExistence : SuccessorExistence where
  next := by
    intro b x out hx ho hxo
    exact PAtoCompactSuccessorQuotientExistence.quotient_successor_exists b x out (by omega) ho hxo

/-- Any unary-fragment term has a value under the guard of a source formula
whose free-variable names cover the term. The output label must be fresh for
that guard, with room for a temporary witness below the allocator. -/
noncomputable def unary_total {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) {t : Peano.language.Term α} (h : UnaryTerm t)
    (b out : Nat) (hb : out + 1 < b)
    (hnames : ∀ z ∈ φ.freeVarFinset, z < out)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    KDerivation (imp (guardFormula φ).encode (existsCode out (termGraph v t out b).encode)) := by
  apply PAtoCompactUnaryTotalityInduction.unary_total v successorExistence (guardFormula φ) h b out hb
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

theorem unary_total_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (φ : Peano.Formula) {t : Peano.language.Term α} (h : UnaryTerm t)
    (b out : Nat) (hb : out + 1 < b)
    (hnames : ∀ z ∈ φ.freeVarFinset, z < out)
    (hcover : ∀ a ∈ t.varFinset, v a ∈ φ.freeVarFinset) :
    theoremCode (certificate (unary_total v φ h b out hb hnames hcover)) =
      imp (guardFormula φ).encode (existsCode out (termGraph v t out b).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactUnaryGuardedTotality

#print axioms PASoundness.PAtoCompactUnaryGuardedTotality.successorExistence
#print axioms PASoundness.PAtoCompactUnaryGuardedTotality.unary_total
#print axioms PASoundness.PAtoCompactUnaryGuardedTotality.unary_total_certificate
