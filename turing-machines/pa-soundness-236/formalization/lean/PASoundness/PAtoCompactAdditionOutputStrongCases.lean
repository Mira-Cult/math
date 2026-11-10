import PASoundness.PAtoCompactWholeCutPointClosed
import PASoundness.PAtoCompactAdditionOutputBranchCases
import PASoundness.PAtoCompactFreeNames

/-! Fixed-label addition output reduction with explicit source and target
output-domain guards. The proper member-cut proof remains an input. -/
namespace PASoundness.PAtoCompactAdditionOutputStrongCases
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactWholeCutWitnessElimination
open PASoundness.PAtoCompactWholeCutPointClosed PASoundness.PAtoCompactAdditionOutputBranchCases
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Explicit source-output and target-output candidate guards. The remaining
target requires the first-input candidate and old-to-new output equivalence. -/
def strongTarget : Formula := .imp (domainAt 100 32)
  (.imp (domainAt 100 8) (.imp (domainAt 100 31) target))

private theorem strong_target_free_fresh (n : Nat)
    (hn30 : n ≠ 30) (hn31 : n ≠ 31) (hn32 : n ≠ 32) (hn8 : n ≠ 8) :
    n ∉ strongTarget.free := by
  intro h
  simp only [strongTarget, target, Formula.free, Finset.mem_union] at h
  rcases h with h | h | h | h | h | h
  · have hh := domainAt_free 100 32 h
    simp only [Finset.mem_singleton] at hh
    exact hn32 hh
  · have hh := domainAt_free 100 8 h
    simp only [Finset.mem_singleton] at hh
    exact hn8 hh
  · have hh := domainAt_free 100 31 h
    simp only [Finset.mem_singleton] at hh
    exact hn31 hh
  · have hh := domainAt_free 100 30 h
    simp only [Finset.mem_singleton] at hh
    exact hn30 hh
  · have hh := equivAt_free 100 32 8 h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with hh | hh
    · exact hn32 hh
    · exact hn8 hh
  · have hh := addAt_free 100 30 31 8 h
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with hh | hh | hh
    · exact hn30 hh
    · exact hn31 hh
    · exact hn8 hh

private def strengthen_target : KDerivation (imp target.encode strongTarget.encode) := by
  change KDerivation (imp target.encode (imp (domainAt 100 32).encode
    (imp (domainAt 100 8).encode (imp (domainAt 100 31).encode target.encode))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(domainAt 100 31).encode, (domainAt 100 8).encode, (domainAt 100 32).encode, target.encode]
  exact Context.hypothesis (by simp [Γ])

/-- The already developed equal-cut proof also proves the stronger target by
weakening. Its source cut/suffix premises and actual witness names are kept. -/
noncomputable def equal_point_strong : KDerivation (imp (equal 33 32)
    (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
      (imp PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
        (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode strongTarget.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode,
    PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode,
    (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode, equal 33 32]
  have hr : Context Γ (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode := .head _ _
  have hs : Context Γ PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode := .hypothesis (by simp [Γ])
  have hl : Context Γ (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode := .hypothesis (by simp [Γ])
  have he : Context Γ (equal 33 32) := .hypothesis (by simp [Γ])
  have ht : Context Γ target.encode :=
    .mp hr (.mp hs (.mp hl (.mp he (.closed whole_cut_point))))
  exact .mp ht (.closed strengthen_target)

private theorem original_shape : PASoundness.PAtoCompactOrdinalAddition.additionFormula =
    .ex 33 (.ex 34 additionBody) := by rfl

/-- Given a point proof for the proper member cut, K proves output transport
for literal addition with all four displayed candidate-domain guards. -/
noncomputable def addition_output_of_member_point_strong
    (memberPoint : KDerivation (imp (member 32 33)
      (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
        (imp PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
          (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode strongTarget.encode))))) :
    KDerivation (imp PASoundness.PAtoCompactOrdinalAddition.additionFormula.encode strongTarget.encode) := by
  have hbody : KDerivation (imp additionBody.encode strongTarget.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [additionBody.encode]
    have hb : Context Γ additionBody.encode := .head _ _
    have hb' : Context Γ (both (either (equal 33 32) (member 32 33))
        (both (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
          (both PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
            (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode))) := by
      change Context Γ (both (either (equal 33 32) (member 32 33))
        (both (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
          (both PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
            (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode))) at hb
      exact hb
    have hcase := Context.conjunctionLeft hb'
    have hl := Context.conjunctionLeft (Context.conjunctionRight hb')
    have hs := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hb'))
    have hr := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hb'))
    apply Context.disjunctionElim hcase
    · let Δ := equal 33 32 :: Γ
      have he : Context Δ (equal 33 32) := .head _ _
      exact .mp (.under hr _) (.mp (.under hs _) (.mp (.under hl _) (.mp he (.closed equal_point_strong))))
    · let Δ := member 32 33 :: Γ
      have hm : Context Δ (member 32 33) := .head _ _
      exact .mp (.under hr _) (.mp (.under hs _) (.mp (.under hl _) (.mp hm (.closed memberPoint))))
  have hv34 : KDerivation (imp strongTarget.encode (allCode 34 strongTarget.encode)) :=
    free_vacuity 34 strongTarget (strong_target_free_fresh 34 (by decide) (by decide) (by decide) (by decide))
  have h34 : KDerivation (imp (existsCode 34 additionBody.encode) strongTarget.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim hv34 (.closed (.generalize 34 hbody))
      (Context.head [] (existsCode 34 additionBody.encode))
  have hv33 : KDerivation (imp strongTarget.encode (allCode 33 strongTarget.encode)) :=
    free_vacuity 33 strongTarget (strong_target_free_fresh 33 (by decide) (by decide) (by decide) (by decide))
  have h33 : KDerivation (imp (existsCode 33 (existsCode 34 additionBody.encode)) strongTarget.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim hv33 (.closed (.generalize 33 h34))
      (Context.head [] (existsCode 33 (existsCode 34 additionBody.encode)))
  simpa [original_shape, Formula.encode] using h33

theorem addition_output_of_member_point_strong_certificate
    (memberPoint : KDerivation (imp (member 32 33)
      (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
        (imp PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
          (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode strongTarget.encode))))) :
    theoremCode (certificate (addition_output_of_member_point_strong memberPoint)) =
      imp PASoundness.PAtoCompactOrdinalAddition.additionFormula.encode strongTarget.encode := certificate_correct _

end PASoundness.PAtoCompactAdditionOutputStrongCases

#print axioms PASoundness.PAtoCompactAdditionOutputStrongCases.strongTarget
#print axioms PASoundness.PAtoCompactAdditionOutputStrongCases.equal_point_strong
#print axioms PASoundness.PAtoCompactAdditionOutputStrongCases.addition_output_of_member_point_strong
#print axioms PASoundness.PAtoCompactAdditionOutputStrongCases.addition_output_of_member_point_strong_certificate
