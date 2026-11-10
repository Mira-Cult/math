import PASoundness.PAtoCompactAdditionOldTargetFromBijection
import PASoundness.PAtoCompactAdditionSuccessorGraphClean
import PASoundness.PAtoCompactPointAdjoin
import PASoundness.PAtoCompactTransitiveSuccessor

/-! The common explicit K hypotheses for the distinct-top addition
right-bijection case. This file provides only a conjunction and capture-safe
vacuity; it does not prove either branch, bijectivity, or arithmetic totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionRightContext
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactAdditionSuccessorGraphClean
open PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactAdditionOldTargetFromBijection
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The old suffix as a literal filter formula. -/
def suffixF : Formula := .all 35 (namedFilterBody 32 34 35 (Formula.member 33 35).not)
/-- The supplied source successor. -/
def sourceS : Formula := namedSuccessor 31 38 39
/-- The supplied new graph obtained by adjoining the specified pair. -/
def graphA : Formula := namedAdjoin 6 11 9 16
/-- The explicitly supplied newly adjoined ordered pair. -/
def pairF : Formula := pairFormula 11 31 32
/-- The common hypotheses in the order used by the two branches. -/
def premises : Formula := namedBoth suffixF (namedBoth oldMatrixAt
  (namedBoth oldClean (namedBoth sourceS (namedBoth graphA pairF))))

theorem suffix_code : suffixF.encode = suffix := by rfl
theorem source_code : sourceS.encode = successorCode 31 38 39 := by rfl
theorem graph_code : graphA.encode = adjoinCode 6 11 9 16 := by rfl

/-- Generalization at the fresh target name 28 preserves all the common
hypotheses, including the supplied old bijection/order matrix. -/
def premises_vacuity : KDerivation (imp premises.encode (allCode 28 premises.encode)) :=
  premises.vacuity 28 (by decide)

theorem premises_vacuity_certificate : theoremCode (certificate premises_vacuity) =
    imp premises.encode (allCode 28 premises.encode) := certificate_correct premises_vacuity
end PASoundness.PAtoCompactAdditionRightContext
#print axioms PASoundness.PAtoCompactAdditionRightContext.premises_vacuity
#print axioms PASoundness.PAtoCompactAdditionRightContext.premises_vacuity_certificate
