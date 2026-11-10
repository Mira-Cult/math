import PASoundness.PAtoCompactRestrictedEquivalentTarget

/-! Literal K instantiation of the proved original/prepared equivalence at
fresh endpoint aliases 40 and 41. These aliases avoid the original E's bound
coordinate labels 2 and 5, and also the prepared matrix's 30 and 31. This is
not yet a substitution of the actual endpoint names 2 and 5 into original E. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactEquivalentAliasInstantiation
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactRestrictedEquivalentTarget
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Canonical quotient formula at two non-capturing endpoint aliases. -/
def originalAliases : Formula := replace 1 41 (replace 0 40 equivalentFormula)
/-- Prepared quotient formula at the same endpoint aliases. -/
def preparedAliases : Formula := replace 1 41 (replace 0 40 preparedEquivalent)

/-- Generalize a concrete K proof, then instantiate it twice. The binder
freshness checks are specific to these displayed formulas. -/
def forward : KDerivation (imp originalAliases.encode preparedAliases.encode) := by
  let f : Formula := .imp equivalentFormula preparedEquivalent
  have d : KDerivation f.encode := prepare_equivalent.forward
  have i0 := universalInstance 0 40 f (by decide) (by decide) (by decide)
  have d0 : KDerivation (replace 0 40 f).encode := .mp (.generalize 0 d) i0
  have i1 := universalInstance 1 41 (replace 0 40 f) (by decide) (by decide) (by decide)
  have d1 : KDerivation (replace 1 41 (replace 0 40 f)).encode := .mp (.generalize 1 d0) i1
  exact d1

def backward : KDerivation (imp preparedAliases.encode originalAliases.encode) := by
  let f : Formula := .imp preparedEquivalent equivalentFormula
  have d : KDerivation f.encode := prepare_equivalent.backward
  have i0 := universalInstance 0 40 f (by decide) (by decide) (by decide)
  have d0 : KDerivation (replace 0 40 f).encode := .mp (.generalize 0 d) i0
  have i1 := universalInstance 1 41 (replace 0 40 f) (by decide) (by decide) (by decide)
  have d1 : KDerivation (replace 1 41 (replace 0 40 f)).encode := .mp (.generalize 1 d0) i1
  exact d1

theorem forward_certificate : theoremCode (certificate forward) =
    imp originalAliases.encode preparedAliases.encode := certificate_correct forward

theorem backward_certificate : theoremCode (certificate backward) =
    imp preparedAliases.encode originalAliases.encode := certificate_correct backward

end PASoundness.PAtoCompactEquivalentAliasInstantiation

#print axioms PASoundness.PAtoCompactEquivalentAliasInstantiation.forward
#print axioms PASoundness.PAtoCompactEquivalentAliasInstantiation.backward
#print axioms PASoundness.PAtoCompactEquivalentAliasInstantiation.forward_certificate
#print axioms PASoundness.PAtoCompactEquivalentAliasInstantiation.backward_certificate
