import PASoundness.PAtoCompactMemberChosenFromOutput
import PASoundness.PAtoCompactMemberOutputDomainsTrans
import PASoundness.PAtoCompactMemberCutSelectedTarget
import PASoundness.PAtoCompactAdditionOutputStrongCases

/-! Construct the proper member-cut point from explicit output and operand
domains, retaining the actual cut/suffix and one original output graph. This
is a noncomputable finite K proof-data construction, not executable extraction. -/
namespace PASoundness.PAtoCompactAdditionMemberPointStrong
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactLessRightSegmentAliases
open PASoundness.PAtoCompactMemberOutputDomainsTrans PASoundness.PAtoCompactMemberChosenFromOutput
open PASoundness.PAtoCompactMemberCutSelectedTarget PASoundness.PAtoCompactAdditionOutputStrongCases
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Given the literal source addition's actual member cut and suffix, and
all four displayed operand/output domains plus the output equivalence, the
same operands add to the target output. No source cut or suffix is reselected. -/
noncomputable def member_point_strong : KDerivation (imp (member 32 33)
    (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
      (imp suffixFormula.encode
        (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode strongTarget.encode)))) := by
  change KDerivation (imp (member 32 33)
    (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
      (imp suffixFormula.encode
        (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode
          (imp (domainAt 100 32).encode (imp (domainAt 100 8).encode
            (imp (domainAt 100 31).encode (imp (domainAt 100 30).encode
              (imp (PASoundness.PAtoCompactTermTranslation.equivAt 100 32 8).encode
                (addAt 100 30 31 8).encode)))))))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(PASoundness.PAtoCompactTermTranslation.equivAt 100 32 8).encode,
    (domainAt 100 30).encode,(domainAt 100 31).encode,(domainAt 100 8).encode,
    (domainAt 100 32).encode,(PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode,
    suffixFormula.encode,(PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode,member 32 33]
  have he : Context Γ (PASoundness.PAtoCompactTermTranslation.equivAt 100 32 8).encode := .head _ _
  have hd30 : Context Γ (domainAt 100 30).encode := .hypothesis (by simp [Γ])
  have hd31 : Context Γ (domainAt 100 31).encode := .hypothesis (by simp [Γ])
  have hd8 : Context Γ (domainAt 100 8).encode := .hypothesis (by simp [Γ])
  have hd32 : Context Γ (domainAt 100 32).encode := .hypothesis (by simp [Γ])
  have hr : Context Γ (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode := .hypothesis (by simp [Γ])
  have hs : Context Γ suffixFormula.encode := .hypothesis (by simp [Γ])
  have hl : Context Γ (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 32 33) := .hypothesis (by simp [Γ])
  have ht32 : Context Γ (namedTrans 32 11 12).encode := .mp hd32 (.closed source_output_transitive)
  have ht8 : Context Γ (namedTrans 8 16 18).encode := .mp hd8 (.closed target_output_transitive)
  have hg : Context Γ outerGuard.encode := by
    have h := Context.conjunctionIntro ht32 (Context.conjunctionIntro ht8 (Context.conjunctionIntro hm hs))
    simpa only [outerGuard,namedBoth,Formula.not,Formula.encode,both,neg] using h
  have hchosen : Context Γ chosen.encode := .mp he (.mp hg (.closed chosen_from_output))
  have hb : Context Γ base.encode := by
    have h := Context.conjunctionIntro hd30 (Context.conjunctionIntro hd31 (Context.conjunctionIntro hl hr))
    simpa only [base,oldCut,oldSuffix,namedBoth,Formula.not,Formula.encode,both,neg] using h
  exact .mp hchosen (.mp hb (.closed target_from_selected))

theorem member_point_strong_certificate : theoremCode (certificate member_point_strong) =
    imp (member 32 33)
      (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
        (imp suffixFormula.encode
          (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode strongTarget.encode))) :=
  certificate_correct member_point_strong
end PASoundness.PAtoCompactAdditionMemberPointStrong

#print axioms PASoundness.PAtoCompactAdditionMemberPointStrong.member_point_strong
#print axioms PASoundness.PAtoCompactAdditionMemberPointStrong.member_point_strong_certificate
