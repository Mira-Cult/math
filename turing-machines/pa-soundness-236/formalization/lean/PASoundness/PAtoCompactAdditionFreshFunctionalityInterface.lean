import PASoundness.PAtoCompactGuardFunctionalityCrossBase

/-! An explicit finite-K proof-data interface for a fresh-base addition graph
step. This interface is not inhabited by this module. -/
namespace PASoundness.PAtoCompactAdditionFreshFunctionalityInterface

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstBinaryStep

/-- The fresh-base addition case at identity variable mapping. Both child
proofs, the original guard, and allocator inequalities remain explicit. -/
abbrev FreshAddition : Type :=
  ∀ (t u : Peano.Term) (b c p q e f : Nat) (g : Formula),
    b + 1 < c → p < b → q < b →
    (∀ a ∈ t.varFinset, a < b) → (∀ a ∈ u.varFinset, a < b) →
    (∀ a ∈ g.free, a < b) →
    b + 1 < e + 2 → c + 1 < e + 2 → p < f + 2 → q < f + 2 →
    KDerivation (imp g.encode (imp (termGraph id t b (b+64)).encode
      (imp (termGraph id t c (c+64)).encode (equivAt e b c).encode))) →
    KDerivation (imp g.encode (imp (termGraph id u (b+1) (b+64+termCost t)).encode
      (imp (termGraph id u (c+1) (c+64+termCost t)).encode
        (equivAt e (b+1) (c+1)).encode))) →
    KDerivation (imp g.encode (imp (termGraph id (binaryTerm true t u) p b).encode
      (imp (termGraph id (binaryTerm true t u) q c).encode (equivAt f p q).encode)))

end PASoundness.PAtoCompactAdditionFreshFunctionalityInterface

#print axioms PASoundness.PAtoCompactAdditionFreshFunctionalityInterface.FreshAddition
