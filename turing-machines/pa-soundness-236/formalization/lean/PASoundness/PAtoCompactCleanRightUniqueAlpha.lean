import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactZeroSuccessor

/-! Capture-safe alpha conversion and vacuity for the supplied old right
bijection witness body. These are finite K proof-data helpers; no matrix,
filter, graph existence, or quotient result is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCleanRightUniqueAlpha
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def uniqueBody (u : Nat) : Formula :=
  .imp (namedBoth (.member 0 u) (graphFormula 10 u 3)) (.equal u 2)

def oldUnique : Formula := .all 4 (uniqueBody 4)
def freshUnique : Formula := .all 30 (uniqueBody 30)

def oldBody : Nat := both (member 0 2) (both (graphFormula 10 2 3).encode oldUnique.encode)

/-- Rename the old uniqueness binder 4 to 30; 30 avoids all internal
pair/graph binders and all free names. -/
def old_unique_alpha : KDerivation (imp oldUnique.encode freshUnique.encode) := by
  have h := (universalAlpha 4 30 (uniqueBody 4) (by decide) (by decide) (by decide)).1
  have hs : replace 4 30 (uniqueBody 4) = uniqueBody 30 := by decide
  rw [hs] at h
  exact h

/-- The reverse conversion restores the original exact uniqueness formula. -/
def old_unique_unalpha : KDerivation (imp freshUnique.encode oldUnique.encode) := by
  have h := (universalAlpha 4 30 (uniqueBody 4) (by decide) (by decide) (by decide)).2
  have hs : replace 4 30 (uniqueBody 4) = uniqueBody 30 := by decide
  rw [hs] at h
  exact h

/-- Although the old uniqueness formula binds name 4, it is vacuous at 4
in K: alpha-rename the inner binder, generalize, then restore it. -/
def old_unique_vacuity_4 : KDerivation (imp oldUnique.encode (allCode 4 oldUnique.encode)) := by
  have hv : KDerivation (imp freshUnique.encode (allCode 4 freshUnique.encode)) :=
    freshUnique.vacuity 4 (by decide)
  exact compose old_unique_alpha (compose hv (allCongr 4 old_unique_unalpha))

/-- Conjunction preserves supplied vacuity proofs in the literal compact
encoding, whose negation is relative to code 1. -/
def conjunction_vacuity (q a b : Nat)
    (ha : KDerivation (imp a (allCode q a)))
    (hb : KDerivation (imp b (allCode q b))) :
    KDerivation (imp (both a b) (allCode q (both a b))) :=
  negationVacuity q (implicationVacuity q ha (negationVacuity q hb))

/-- Full old witness body is K-vacuous at name 4, including the internally
bound uniqueness clause. -/
def old_body_vacuity_4 : KDerivation (imp oldBody (allCode 4 oldBody)) := by
  have hm := membershipVacuity 0 2 4 (by decide) (by decide)
  have hg := (graphFormula 10 2 3).vacuity 4 (by decide)
  exact conjunction_vacuity 4 (member 0 2) (both (graphFormula 10 2 3).encode oldUnique.encode)
    hm (conjunction_vacuity 4 (graphFormula 10 2 3).encode oldUnique.encode hg old_unique_vacuity_4)

theorem alpha_vacuity_certificates :
    theoremCode (certificate old_unique_alpha) = imp oldUnique.encode freshUnique.encode ∧
    theoremCode (certificate old_unique_unalpha) = imp freshUnique.encode oldUnique.encode ∧
    theoremCode (certificate old_unique_vacuity_4) = imp oldUnique.encode (allCode 4 oldUnique.encode) ∧
    theoremCode (certificate old_body_vacuity_4) = imp oldBody (allCode 4 oldBody) :=
  ⟨certificate_correct old_unique_alpha, certificate_correct old_unique_unalpha,
    certificate_correct old_unique_vacuity_4, certificate_correct old_body_vacuity_4⟩

end PASoundness.PAtoCompactCleanRightUniqueAlpha

#print axioms PASoundness.PAtoCompactCleanRightUniqueAlpha.old_unique_alpha
#print axioms PASoundness.PAtoCompactCleanRightUniqueAlpha.old_body_vacuity_4
#print axioms PASoundness.PAtoCompactCleanRightUniqueAlpha.alpha_vacuity_certificates
