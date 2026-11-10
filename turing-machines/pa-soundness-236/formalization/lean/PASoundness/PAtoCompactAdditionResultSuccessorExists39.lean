import PASoundness.PAtoCompactAdditionResultSuccessorExists

/-! Bind the raw-result successor's test at the label expected by the
addition suffix proof. Result output 45 remains distinct from source output
38. This is not an addition totality proof. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionResultSuccessorExists39
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactRawSuccBridge
open PASoundness.PAtoCompactAdditionResultSuccessorExists
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Change only the bound test label of the result-successor graph. -/
def result_successor_alpha : KDerivation
    (imp (successorCode 32 45 46) (successorCode 32 45 39)) := by
  have h := raw_successor_alpha 32 45 46 39 (by decide) (by decide)
    (by decide) (by decide) (by decide)
  simpa [namedSuccessor, namedSuccessorBody, namedBoth, namedEither, successorCode,
    Formula.encode, CompactProof.both, CompactProof.neg, CompactDerivations.either] using h

/-- The actual raw candidate-result successor, with the suffix proof's bound
test label. The same existential witness is retained as a candidate. -/
def result_successor_exists39 : KDerivation
    (imp (domainAt 100 32).encode (existsCode 45
      (both (successorCode 32 45 39) (domainAt 100 45).encode))) := by
  have hm : KDerivation (imp (both (successorCode 32 45 46) (domainAt 100 45).encode)
      (both (successorCode 32 45 39) (domainAt 100 45).encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [both (successorCode 32 45 46) (domainAt 100 45).encode]
    have hp : Context Γ (both (successorCode 32 45 46) (domainAt 100 45).encode) := .head _ _
    exact Context.conjunctionIntro (.mp (Context.conjunctionLeft hp) (.closed result_successor_alpha))
      (Context.conjunctionRight hp)
  exact compose result_successor_exists (existsCongr 45 hm)

theorem result_successor_exists39_certificate : theoremCode (certificate result_successor_exists39) =
    imp (domainAt 100 32).encode (existsCode 45
      (both (successorCode 32 45 39) (domainAt 100 45).encode)) :=
  certificate_correct result_successor_exists39
end PASoundness.PAtoCompactAdditionResultSuccessorExists39
#print axioms PASoundness.PAtoCompactAdditionResultSuccessorExists39.result_successor_alpha
#print axioms PASoundness.PAtoCompactAdditionResultSuccessorExists39.result_successor_exists39
#print axioms PASoundness.PAtoCompactAdditionResultSuccessorExists39.result_successor_exists39_certificate
