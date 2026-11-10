import PASoundness.PAtoCompactReverseUnaryAtom
import PASoundness.PAtoCompactUnaryGraphFunctionalityGuarded

/-! Canonical PA-guard specialization of reverse unary atomic substitution.
The guard must cover each free variable of the substituted term. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactReverseUnaryAtomGuarded
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedEqualityReflexivity PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactReverseUnaryAtom

/-- Under a PA free-variable guard covering t, the finite K proof of reverse
atomic substitution requires no additional proof-data inputs. The unchanged
right term s may be arbitrary, provided x does not occur in it. -/
noncomputable def reverse_atomic_guarded (φ : Peano.Formula) (x : Nat) (t s : Peano.Term)
    (ht : UnaryTerm t) (q d : Nat) (hx : x ∉ s.varFinset)
    (hb : guardBase φ ≤ d) (hq : q < d)
    (hcover : ∀ a ∈ t.varFinset, a ∈ φ.freeVarFinset) :
    KDerivation (imp (guardFormula φ).encode (imp (termGraph id t q d).encode
      (imp (code (FOL.substAt ((.var x : Peano.Term).equal s) x t))
        (code (FOL.substAt ((.var x : Peano.Term).equal s) x (.var q)))))) := by
  have hbound : ∀ a ∈ t.varFinset, a < guardBase φ := by
    intro a ha
    have hh : a ≤ φ.freeVarFinset.sup id := Finset.le_sup (f := id) (hcover a ha)
    unfold guardBase
    omega
  have htd : ∀ a ∈ t.varFinset, a < d := by
    intro a ha
    have hh := hbound a ha
    omega
  apply reverse_atomic_substitution x t s ht (guardFormula φ) q d hx hq htd
  intro a ha
  exact compose (guardFormula_projection φ a (hcover a ha))
    (domainAt_transport (guardBase φ) d a (by have := hbound a ha; omega) (by have := htd a ha; omega))

theorem reverse_atomic_guarded_certificate (φ : Peano.Formula) (x : Nat) (t s : Peano.Term)
    (ht : UnaryTerm t) (q d : Nat) (hx : x ∉ s.varFinset)
    (hb : guardBase φ ≤ d) (hq : q < d)
    (hcover : ∀ a ∈ t.varFinset, a ∈ φ.freeVarFinset) :
    theoremCode (certificate (reverse_atomic_guarded φ x t s ht q d hx hb hq hcover)) =
      imp (guardFormula φ).encode (imp (termGraph id t q d).encode
        (imp (code (FOL.substAt ((.var x : Peano.Term).equal s) x t))
          (code (FOL.substAt ((.var x : Peano.Term).equal s) x (.var q))))) := certificate_correct _
end PASoundness.PAtoCompactReverseUnaryAtomGuarded

#print axioms PASoundness.PAtoCompactReverseUnaryAtomGuarded.reverse_atomic_guarded
#print axioms PASoundness.PAtoCompactReverseUnaryAtomGuarded.reverse_atomic_guarded_certificate
