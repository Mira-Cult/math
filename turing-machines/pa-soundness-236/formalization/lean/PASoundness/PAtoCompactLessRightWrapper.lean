import PASoundness.PAtoCompactQuotientOrder
import PASoundness.PAtoCompactPartialInverseAtSource
import PASoundness.PAtoCompactTransitiveWitness
import PASoundness.PAtoCompactCompositionSharedTransitivity
import PASoundness.PAtoCompactCandidateSymmetryObject
import PASoundness.CompactQuantifiers

/-! A K wrapper for right-order substitution under explicit derivations of
member transport and candidate-restricted transitivity. It does not construct
the restricted graph or discharge those proof-data inputs. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLessRightWrapper
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactQuotientOrder
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactPartialInverseAtSource PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactCandidateSymmetryObject
open PASoundness.PAtoCompactConditionalTransitivityWitnessInterface
open PASoundness.PAtoCompactCompositionSharedTransitivity
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def E18 : Formula := replace 0 1 (replace 1 8 equivalentFormula)
def E07 : Formula := replace 1 7 equivalentFormula
def E79 : Formula := replace 0 7 (replace 1 9 equivalentFormula)
def E09 : Formula := replace 1 9 equivalentFormula
def targetLess : Formula := replace 1 8 lessFormula
def sourceBody : Formula := namedBoth (.member 1 7) E07
def targetBody : Formula := namedBoth (.member 8 7) E07
def targetBody9 : Formula := replace 7 9 targetBody
def segmentBody9 : Formula := namedBoth (.member 8 9) E79
def sourceTrans : Nat := transitiveCode 1 11 12
def targetTrans : Nat := transitiveCode 8 16 18

def transBody : Formula := .imp (namedSymmetryCandidate 0)
  (.imp equivalentFormula (.imp secondEquivalent targetEquivalent))

theorem trans_body_code : transBody.encode =
    imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp equivalentFormula.encode (imp secondEquivalent.encode targetEquivalent.encode)) := rfl

theorem trans_specialization :
    replace 1 7 (replace 8 9 transBody) = .imp (namedSymmetryCandidate 0)
      (.imp E07 (.imp E79 E09)) := by decide

/-- The already proved candidate-restricted transitivity at names 0,7,9. -/
def trans_at_segment : KDerivation
    (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp E07.encode (imp E79.encode E09.encode))) := by
  have hall8 : KDerivation (allCode 8 transBody.encode) := by
    rw [trans_body_code]
    exact .generalize 8 shared_candidate_transitivity
  have h8 := universalInstance 8 9 transBody (by decide) (by decide) (by decide)
  have h9 : KDerivation (replace 8 9 transBody).encode := .mp hall8 h8
  have hall1 := KDerivation.generalize 1 h9
  have h1 := universalInstance 1 7 (replace 8 9 transBody)
    (by decide) (by decide) (by decide)
  rw [trans_specialization] at h1
  exact .mp hall1 h1

theorem source_shape : lessFormula = .ex 7 sourceBody := by decide
theorem target_shape : targetLess = .ex 7 targetBody := by decide
theorem target_body9_shape : targetBody9 = namedBoth (.member 8 9) E09 := by decide

/-- Introduce the ninth-name target witness into the actual order formula. -/
def target_intro9 : KDerivation (imp targetBody9.encode targetLess.encode) := by
  have hi := CompactNamed.existsIntroduce 9 targetBody9 (by decide)
  have ha := (CompactNamed.existentialAlpha 7 9 targetBody (by decide)
    (by decide) (by decide)).2
  have ht : targetLess.encode = existsCode 7 targetBody.encode := by
    rw [target_shape]; rfl
  rw [ht]
  exact compose hi ha

/-- The target order formula is vacuous at its own bound name after an
explicit alpha conversion to the fresh ninth name. -/
def target_vacuity7 : KDerivation (imp targetLess.encode (allCode 7 targetLess.encode)) := by
  have ha := CompactNamed.existentialAlpha 7 9 targetBody (by decide)
    (by decide) (by decide)
  have hv := (Formula.ex 9 targetBody9).vacuity 7 (by decide)
  have ht : targetLess.encode = existsCode 7 targetBody.encode := by
    rw [target_shape]; rfl
  rw [ht]
  exact compose ha.1 (compose hv (allCongr 7 ha.2))

/-- The graph-restriction/member-transport and transitivity inputs are explicit
finite K derivations, not consequences of semantic soundness. -/
def right_order_of_segment_transport
    (segment : KDerivation (imp sourceTrans (imp targetTrans (imp (member 1 7)
      (imp E18.encode (existsCode 9 segmentBody9.encode))))))
    (trans : KDerivation (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp E07.encode (imp E79.encode E09.encode)))) :
    KDerivation (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp sourceTrans (imp targetTrans
        (imp E18.encode (imp lessFormula.encode targetLess.encode))))) := by
  let D := candidateCode 0 37 32 33 34 30 35 10 36
  let E := E18.encode
  let A := sourceBody.encode
  let V := segmentBody9.encode
  let T := targetLess.encode
  let S := sourceTrans
  let R := targetTrans
  let Γ := [A,E,R,S,D]
  have hD : Context Γ D := .hypothesis (by simp [Γ])
  have hE : Context Γ E := .hypothesis (by simp [Γ])
  have hS : Context Γ S := .hypothesis (by simp [Γ])
  have hR : Context Γ R := .hypothesis (by simp [Γ])
  have hA : Context Γ A := Context.head _ _
  have hmem : Context Γ (member 1 7) := Context.conjunctionLeft hA
  have heq : Context Γ E07.encode := Context.conjunctionRight hA
  have hex : Context Γ (existsCode 9 V) := .mp hE (.mp hmem (.mp hR (.mp hS (.closed segment))))
  have hlocal : Context Γ (imp V T) := by
    apply Context.deduction
    let Δ := V :: Γ
    have hv : Context Δ V := Context.head _ _
    have hm : Context Δ (member 8 9) := Context.conjunctionLeft hv
    have h79 : Context Δ E79.encode := Context.conjunctionRight hv
    have h09 : Context Δ E09.encode :=
      .mp h79 (.mp (Context.under heq V) (.mp (Context.under hD V) (.closed trans)))
    have hbody : Context Δ targetBody9.encode := by
      rw [target_body9_shape]
      exact Context.conjunctionIntro hm h09
    exact .mp hbody (.closed target_intro9)
  have hvA : KDerivation (imp A (allCode 9 A)) := sourceBody.vacuity 9 (by decide)
  have hvE : KDerivation (imp E (allCode 9 E)) := E18.vacuity 9 (by decide)
  have hvR : KDerivation (imp R (allCode 9 R)) :=
    transitive_vacuity 8 16 18 9 (by decide) (by decide) (by decide)
  have hvS : KDerivation (imp S (allCode 9 S)) :=
    transitive_vacuity 1 11 12 9 (by decide) (by decide) (by decide)
  have hvD : KDerivation (imp D (allCode 9 D)) := by
    have h := (namedCandidate 0).vacuity 9 (by decide)
    simpa only [D,PAtoCompactPartialInverseAtSource.named_candidate_code] using h
  have hall : Context Γ (allCode 9 (imp V T)) := Context.generalize 9 (by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases ha : h = A
    · subst h; exact hvA
    by_cases he : h = E
    · subst h; exact hvE
    by_cases hr : h = R
    · subst h; exact hvR
    by_cases hs : h = S
    · subst h; exact hvS
    have hd : h = D := (((hh.resolve_left ha).resolve_left he).resolve_left hr).resolve_left hs
    subst h; exact hvD) hlocal
  have htarget : Context Γ T := Context.existsElim (targetLess.vacuity 9 (by decide)) hall hex
  let Γ' := [E,R,S,D]
  have hsource : Context Γ' (imp A T) := Context.deduction htarget
  have hall7 : Context Γ' (allCode 7 (imp A T)) := Context.generalize 7 (by
    intro h hh
    simp only [Γ',List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases he : h = E
    · subst h; exact E18.vacuity 7 (by decide)
    by_cases hr : h = R
    · subst h; exact transitive_vacuity 8 16 18 7 (by decide) (by decide) (by decide)
    by_cases hs : h = S
    · subst h; exact transitive_vacuity 1 11 12 7 (by decide) (by decide) (by decide)
    have hd : h = D := ((hh.resolve_left he).resolve_left hr).resolve_left hs
    subst h
    have hv := (namedCandidate 0).vacuity 7 (by decide)
    simpa only [D,PAtoCompactPartialInverseAtSource.named_candidate_code] using hv) hsource
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Δ := [lessFormula.encode,E,R,S,D]
  have hs : Context Δ (existsCode 7 A) := by
    have h := Context.head [E,R,S,D] lessFormula.encode
    simpa only [Δ,source_shape,Formula.encode,A] using h
  have ht : Context Δ (allCode 7 (imp A T)) := Context.weaken hall7 (by
    intro h hh
    simp only [Γ',List.mem_cons,List.not_mem_nil,or_false] at hh
    simp [Δ,hh])
  exact Context.existsElim target_vacuity7 ht hs

/-- Candidate-restricted right-order substitution, conditional only on the
specific K proof that an E-equivalent right endpoint transports each member
to an E-equivalent member. -/
def right_order_of_segment
    (segment : KDerivation (imp sourceTrans (imp targetTrans (imp (member 1 7)
      (imp E18.encode (existsCode 9 segmentBody9.encode)))))) :
    KDerivation (imp (candidateCode 0 37 32 33 34 30 35 10 36)
      (imp sourceTrans (imp targetTrans
        (imp E18.encode (imp lessFormula.encode targetLess.encode))))) :=
  right_order_of_segment_transport segment trans_at_segment

theorem right_order_of_segment_certificate
    (segment : KDerivation (imp sourceTrans (imp targetTrans (imp (member 1 7)
      (imp E18.encode (existsCode 9 segmentBody9.encode)))))) :
    theoremCode (certificate (right_order_of_segment segment)) =
      imp (candidateCode 0 37 32 33 34 30 35 10 36)
        (imp sourceTrans (imp targetTrans
          (imp E18.encode (imp lessFormula.encode targetLess.encode)))) :=
  certificate_correct (right_order_of_segment segment)

end PASoundness.PAtoCompactLessRightWrapper

#print axioms PASoundness.PAtoCompactLessRightWrapper.right_order_of_segment_transport
#print axioms PASoundness.PAtoCompactLessRightWrapper.right_order_of_segment
#print axioms PASoundness.PAtoCompactLessRightWrapper.right_order_of_segment_certificate
