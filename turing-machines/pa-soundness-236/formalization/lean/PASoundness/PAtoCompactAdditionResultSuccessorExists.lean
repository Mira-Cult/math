import PASoundness.PAtoCompactSuccessorQuotientExistence
import PASoundness.PAtoCompactRawSuccBridge

/-! A candidate old result has a candidate raw successor with labels that do
not collide with the addition graph's source successor. This is not addition
existence or the PA bridge. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionResultSuccessorExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactRawSuccBridge
open PASoundness.PAtoCompactSuccessorQuotientExistence
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- K constructs a candidate successor 45 of old result 32. Test label 46
is distinct from the separately used source-successor output label 38. -/
def result_successor_exists : KDerivation
    (imp (domainAt 100 32).encode (existsCode 45
      (both (successorCode 32 45 46) (domainAt 100 45).encode))) := by
  have hraw := raw_candidate_successor 100 32 45 (by decide) (by decide) (by decide)
  have halpha := raw_successor_alpha 32 45 110 46 (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have ha : KDerivation (imp (successorCode 32 45 110) (successorCode 32 45 46)) := by
    simpa [namedSuccessor, namedSuccessorBody, namedBoth, namedEither, successorCode,
      Formula.encode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using halpha
  have hmap : KDerivation (imp (both (successorCode 32 45 110) (domainAt 100 45).encode)
      (both (successorCode 32 45 46) (domainAt 100 45).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [both (successorCode 32 45 110) (domainAt 100 45).encode]
    have hp : Context Γ (both (successorCode 32 45 110) (domainAt 100 45).encode) := .head _ _
    exact Context.conjunctionIntro (.mp (Context.conjunctionLeft hp) (.closed ha))
      (Context.conjunctionRight hp)
  exact compose hraw (existsCongr 45 hmap)

theorem result_successor_exists_certificate : theoremCode (certificate result_successor_exists) =
    imp (domainAt 100 32).encode (existsCode 45
      (both (successorCode 32 45 46) (domainAt 100 45).encode)) :=
  certificate_correct result_successor_exists
end PASoundness.PAtoCompactAdditionResultSuccessorExists
#print axioms PASoundness.PAtoCompactAdditionResultSuccessorExists.result_successor_exists
#print axioms PASoundness.PAtoCompactAdditionResultSuccessorExists.result_successor_exists_certificate
