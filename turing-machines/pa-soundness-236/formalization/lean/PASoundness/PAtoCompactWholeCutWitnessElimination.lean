import PASoundness.PAtoCompactOrdinalAddition
import PASoundness.PAtoCompactTermGraphBinderRange
import PASoundness.PAtoCompactFreeVacuity

/-! Eliminate the actual equal-cut and suffix witnesses after a supplied
pointwise finite-K proof. This module does not construct the pointwise proof,
handle member cuts, or establish addition output transport. -/

namespace PASoundness.PAtoCompactWholeCutWitnessElimination

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactFreeNames

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The actual equal-cut branch of the fixed source addition body. Both the
cut at 33 and its filtered suffix at 34 are retained in one formula. -/
def wholeBody : Formula :=
  andF (.equal 33 32) (andF (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33)
    (andF PASoundness.PAtoCompactOrdinalAddition.suffixFormula
      (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34)))

/-- One pair of cut and suffix witnesses satisfying the equal-cut body. -/
def wholeWitness : Formula := .ex 33 (.ex 34 wholeBody)

/-- Under the original first-input candidate and output equivalence, the
target is the allocated addition relation at the same inputs and new output. -/
def target : Formula := .imp (domainAt 100 30)
  (.imp (PASoundness.PAtoCompactTermTranslation.equivAt 100 32 8)
    (addAt 100 30 31 8))

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

/-- A pointwise proof using the displayed equality, original cut-equivalence,
original suffix filter and suffix-equivalence yields a proof from the single
pair of existential witnesses. The pointwise implication remains an explicit
input; this is not the complete whole-cut or addition-output theorem. -/
def eliminate_witnesses
    (point : KDerivation (imp (equal 33 32)
      (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
        (imp PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
          (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode target.encode))))) :
    KDerivation (imp wholeWitness.encode target.encode) := by
  have hbody : KDerivation (imp wholeBody.encode target.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [wholeBody.encode]
    have hb : Context Γ wholeBody.encode := .head _ _
    have hb' : Context Γ (both (equal 33 32)
        (both (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
          (both PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
            (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode))) := by
      simpa [wholeBody, andF, Formula.not, Formula.encode, both, neg] using hb
    have hEq := Context.conjunctionLeft hb'
    have hLeft := Context.conjunctionLeft (Context.conjunctionRight hb')
    have hSuffix := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hb'))
    have hRight := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hb'))
    exact .mp hRight (.mp hSuffix (.mp hLeft (.mp hEq (.closed point))))
  have hv34 : KDerivation (imp target.encode (allCode 34 target.encode)) :=
    free_vacuity 34 target (target_free_fresh 34 (by decide) (by decide) (by decide) (by decide))
  have h34 : KDerivation (imp (existsCode 34 wholeBody.encode) target.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim hv34 (.closed (.generalize 34 hbody))
      (Context.head [] (existsCode 34 wholeBody.encode))
  have hv33 : KDerivation (imp target.encode (allCode 33 target.encode)) :=
    free_vacuity 33 target (target_free_fresh 33 (by decide) (by decide) (by decide) (by decide))
  have h33 : KDerivation (imp (existsCode 33 (existsCode 34 wholeBody.encode)) target.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim hv33 (.closed (.generalize 33 h34))
      (Context.head [] (existsCode 33 (existsCode 34 wholeBody.encode)))
  simpa [wholeWitness, Formula.encode] using h33

theorem eliminate_witnesses_certificate
    (point : KDerivation (imp (equal 33 32)
      (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33).encode
        (imp PASoundness.PAtoCompactOrdinalAddition.suffixFormula.encode
          (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34).encode target.encode))))) :
    theoremCode (certificate (eliminate_witnesses point)) =
      imp wholeWitness.encode target.encode := certificate_correct _

end PASoundness.PAtoCompactWholeCutWitnessElimination

#print axioms PASoundness.PAtoCompactWholeCutWitnessElimination.wholeBody
#print axioms PASoundness.PAtoCompactWholeCutWitnessElimination.wholeWitness
#print axioms PASoundness.PAtoCompactWholeCutWitnessElimination.target
#print axioms PASoundness.PAtoCompactWholeCutWitnessElimination.eliminate_witnesses
#print axioms PASoundness.PAtoCompactWholeCutWitnessElimination.eliminate_witnesses_certificate
