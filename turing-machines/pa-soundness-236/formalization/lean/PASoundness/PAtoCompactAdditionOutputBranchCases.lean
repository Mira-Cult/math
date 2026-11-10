import PASoundness.PAtoCompactWholeCutWitnessElimination

/-! Eliminate the actual source addition witnesses once, splitting its cut
case into an explicitly supplied equal-cut proof and an explicitly supplied
member-cut proof. Neither branch proof is constructed by this module. -/
namespace PASoundness.PAtoCompactAdditionOutputBranchCases
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactWholeCutWitnessElimination
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def orF (a b : Formula) : Formula := a.not.imp b
/-- Literal body under the source addition cut and suffix binders. -/
def additionBody : Formula :=
  andF (orF (.equal 33 32) (.member 32 33))
    (andF (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33)
      (andF PASoundness.PAtoCompactOrdinalAddition.suffixFormula
        (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34)))

private theorem original_shape : PASoundness.PAtoCompactOrdinalAddition.additionFormula =
    .ex 33 (.ex 34 additionBody) := by rfl

private theorem target_free_fresh (n : Nat)
    (hn30 : n ≠ 30) (hn31 : n ≠ 31) (hn32 : n ≠ 32) (hn8 : n ≠ 8) :
    n ∉ target.free := by
  intro h
  simp only [target, Formula.free, Finset.mem_union] at h
  rcases h with h | h | h
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

/-- An equal-cut and a member-cut point proof give the target from the actual
literal addition body. The same cut and suffix names occur in both proofs. -/
def body_of_branches
    (equalPoint : KDerivation (imp (equal 33 32)
      (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
        (imp PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
          (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode target.encode)))))
    (memberPoint : KDerivation (imp (member 32 33)
      (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
        (imp PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
          (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode target.encode))))) :
    KDerivation (imp additionBody.encode target.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [additionBody.encode]
  have hb : Context Γ additionBody.encode := .head _ _
  have hb' : Context Γ (both (either (equal 33 32) (member 32 33))
      (both (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
        (both PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
          (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode))) := by
    simpa [additionBody, andF, orF, Formula.not, Formula.encode, both, either, neg] using hb
  have hcase := Context.conjunctionLeft hb'
  have hl := Context.conjunctionLeft (Context.conjunctionRight hb')
  have hs := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hb'))
  have hr := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hb'))
  apply Context.disjunctionElim hcase
  · let Δ := equal 33 32 :: Γ
    have he : Context Δ (equal 33 32) := .head _ _
    exact .mp (.under hr _) (.mp (.under hs _) (.mp (.under hl _) (.mp he (.closed equalPoint))))
  · let Δ := member 32 33 :: Γ
    have hm : Context Δ (member 32 33) := .head _ _
    exact .mp (.under hr _) (.mp (.under hs _) (.mp (.under hl _) (.mp hm (.closed memberPoint))))

/-- If both displayed point proofs exist, K derives the guarded target from
the original literal addition. No member-cut proof or graph law is assumed
constructed; those are explicit proof-data inputs. -/
def addition_output_of_branches
    (equalPoint : KDerivation (imp (equal 33 32)
      (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
        (imp PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
          (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode target.encode)))))
    (memberPoint : KDerivation (imp (member 32 33)
      (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
        (imp PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
          (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode target.encode))))) :
    KDerivation (imp PASoundness.PAtoCompactOrdinalAddition.additionFormula.encode target.encode) := by
  have hbody := body_of_branches equalPoint memberPoint
  have hv34 : KDerivation (imp target.encode (allCode 34 target.encode)) :=
    free_vacuity 34 target (target_free_fresh 34 (by decide) (by decide) (by decide) (by decide))
  have h34 : KDerivation (imp (existsCode 34 additionBody.encode) target.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim hv34 (.closed (.generalize 34 hbody))
      (Context.head [] (existsCode 34 additionBody.encode))
  have hv33 : KDerivation (imp target.encode (allCode 33 target.encode)) :=
    free_vacuity 33 target (target_free_fresh 33 (by decide) (by decide) (by decide) (by decide))
  have h33 : KDerivation (imp (existsCode 33 (existsCode 34 additionBody.encode)) target.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim hv33 (.closed (.generalize 33 h34))
      (Context.head [] (existsCode 33 (existsCode 34 additionBody.encode)))
  simpa [original_shape, Formula.encode] using h33

theorem addition_output_of_branches_certificate
    (equalPoint : KDerivation (imp (equal 33 32)
      (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
        (imp PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
          (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode target.encode)))))
    (memberPoint : KDerivation (imp (member 32 33)
      (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
        (imp PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
          (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode target.encode))))) :
    theoremCode (certificate (addition_output_of_branches equalPoint memberPoint)) =
      imp PASoundness.PAtoCompactOrdinalAddition.additionFormula.encode target.encode :=
  certificate_correct _

end PASoundness.PAtoCompactAdditionOutputBranchCases

#print axioms PASoundness.PAtoCompactAdditionOutputBranchCases.additionBody
#print axioms PASoundness.PAtoCompactAdditionOutputBranchCases.body_of_branches
#print axioms PASoundness.PAtoCompactAdditionOutputBranchCases.addition_output_of_branches
#print axioms PASoundness.PAtoCompactAdditionOutputBranchCases.addition_output_of_branches_certificate
