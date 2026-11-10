import PASoundness.CompactDerivations
import PASoundness.CompactNamed

/-! Compositional implication alignment while retaining a fixed guard.
The guard can contain the term-graph witness needed by a substitution proof.
All inputs and outputs are finite K derivations. -/
namespace PASoundness.PAtoCompactGuardedLogicalCongruence

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations

/-- Both directions of an alignment under one unchanged hypothesis. -/
abbrev GuardedBoth (h a b : Formula) :=
  KDerivation (imp h.encode (imp a.encode b.encode)) ×
    KDerivation (imp h.encode (imp b.encode a.encode))

/-- Implication is contravariant in its antecedent and covariant in its
consequent, while the same guard remains available to both subderivations. -/
def guarded_implication_forward (h a a' b b' : Formula)
    (ha : KDerivation (imp h.encode (imp a'.encode a.encode)))
    (hb : KDerivation (imp h.encode (imp b.encode b'.encode))) :
    KDerivation (imp h.encode (imp (Formula.imp a b).encode (Formula.imp a' b').encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [a'.encode, (Formula.imp a b).encode, h.encode]
  have hA' : Context Γ a'.encode := Context.head _ _
  have hAB : Context Γ (Formula.imp a b).encode := .hypothesis (by simp [Γ])
  have hH : Context Γ h.encode := .hypothesis (by simp [Γ])
  have hA : Context Γ a.encode := .mp hA' (.mp hH (.closed ha))
  have hB : Context Γ b.encode := .mp hA hAB
  exact .mp hB (.mp hH (.closed hb))

def guarded_implication (h a a' b b' : Formula)
    (ha : GuardedBoth h a a') (hb : GuardedBoth h b b') :
    GuardedBoth h (Formula.imp a b) (Formula.imp a' b') :=
  ⟨guarded_implication_forward h a a' b b' ha.2 hb.1,
    guarded_implication_forward h a' a b' b ha.1 hb.2⟩

theorem guarded_implication_forward_certificate (h a a' b b' : Formula)
    (ha : KDerivation (imp h.encode (imp a'.encode a.encode)))
    (hb : KDerivation (imp h.encode (imp b.encode b'.encode))) :
    theoremCode (certificate (guarded_implication_forward h a a' b b' ha hb)) =
      imp h.encode (imp (Formula.imp a b).encode (Formula.imp a' b').encode) := certificate_correct _

end PASoundness.PAtoCompactGuardedLogicalCongruence

#print axioms PASoundness.PAtoCompactGuardedLogicalCongruence.guarded_implication_forward
#print axioms PASoundness.PAtoCompactGuardedLogicalCongruence.guarded_implication
#print axioms PASoundness.PAtoCompactGuardedLogicalCongruence.guarded_implication_forward_certificate
