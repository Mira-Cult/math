import PASoundness.PAtoCompactEquivalentAliasInstantiation

/-! Lift the proved alias equivalence through the two explicit endpoint
equality guards. This is a finite K proof transformation. It does not assert
that free endpoint substitution is capture-safe in the original formula. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactEquivalentAliasGuardLift
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactEquivalentAliasInstantiation
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

/-- Alias names 40 and 41 are bound, with their values tied to endpoints 2 and 5. -/
def guarded (f : Formula) : Formula :=
  .ex 40 (conj (.equal 40 2) (.ex 41 (conj (.equal 41 5) f)))

private def conj_congr (a : Formula) {b c : Formula}
    (h : KDerivation (imp b.encode c.encode)) :
    KDerivation (imp (conj a b).encode (conj a c).encode) := by
  change KDerivation (imp (neg (imp a.encode (neg b.encode)))
    (neg (imp a.encode (neg c.encode))))
  exact contrapose (implicationCongr (CompactHilbertBasis.identity a.encode) (contrapose h))

private def lift {a b : Formula} (h : KDerivation (imp a.encode b.encode)) :
    KDerivation (imp (guarded a).encode (guarded b).encode) :=
  existsCongr 40 (conj_congr (.equal 40 2)
    (existsCongr 41 (conj_congr (.equal 41 5) h)))

def forward : KDerivation (imp (guarded originalAliases).encode
    (guarded preparedAliases).encode) := lift PAtoCompactEquivalentAliasInstantiation.forward

def backward : KDerivation (imp (guarded preparedAliases).encode
    (guarded originalAliases).encode) := lift PAtoCompactEquivalentAliasInstantiation.backward

theorem forward_certificate : theoremCode (certificate forward) =
    imp (guarded originalAliases).encode (guarded preparedAliases).encode := certificate_correct forward

theorem backward_certificate : theoremCode (certificate backward) =
    imp (guarded preparedAliases).encode (guarded originalAliases).encode := certificate_correct backward

end PASoundness.PAtoCompactEquivalentAliasGuardLift

#print axioms PASoundness.PAtoCompactEquivalentAliasGuardLift.forward
#print axioms PASoundness.PAtoCompactEquivalentAliasGuardLift.backward
#print axioms PASoundness.PAtoCompactEquivalentAliasGuardLift.forward_certificate
#print axioms PASoundness.PAtoCompactEquivalentAliasGuardLift.backward_certificate
