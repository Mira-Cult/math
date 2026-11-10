import PASoundness.PAtoCompactAdditionLiteralCutStepBase
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactLiteralCutAdditionDefinition

/-! Retain the actual left input as the cut in one successor step.  The old
and new suffixes are existentially quantified; the new result successor and
second-input successor remain explicit. This is not addition totality or a PA
bridge. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionLiteralCutStepSpecialize
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactFilterInstantiation
open PASoundness.PAtoCompactAdditionSuccessorLocalStep
open PASoundness.PAtoCompactAdditionLiteralCutStepBase
open PASoundness.PAtoCompactLiteralCutAdditionDefinition
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The input at 30 is itself the cut of result 32, with some suffix 34
isomorphic to the second input 31. -/
def oldLiteral : Formula := .ex 34 (namedBoth (replace 33 30 oldCut)
  (namedBoth (replace 33 30 oldFilter) oldRightEquiv))

/-- The same cut belongs to result 45 and its new suffix is isomorphic to the
new second input 38. -/
def newLiteral : Formula := namedBoth (.member 45 30) (replace 33 30 newSuffix)

private def specialized : KDerivation (imp fixedAssumptions.encode
    (imp (replace 33 30 oldCut).encode
      (imp (replace 33 30 oldFilter).encode
        (imp oldRightEquiv.encode newLiteral.encode)))) := by
  have h := universalInstance 33 30 baseStep (by decide) (by decide) (by decide)
  have hi := KDerivation.mp (.generalize 33 base_step) h
  have hs : replace 33 30 baseStep = .imp fixedAssumptions
      (.imp (replace 33 30 oldCut) (.imp (replace 33 30 oldFilter)
        (.imp oldRightEquiv newLiteral))) := by decide
  rw [hs] at hi
  exact hi

/-- A literal cut remains the same left input across the supplied successors. -/
def literal_cut_step : KDerivation (imp fixedAssumptions.encode
    (imp oldLiteral.encode newLiteral.encode)) := by
  let B := namedBoth (replace 33 30 oldCut)
    (namedBoth (replace 33 30 oldFilter) oldRightEquiv)
  let Γ := [oldLiteral.encode,fixedAssumptions.encode]
  have hp : Context Γ fixedAssumptions.encode := .hypothesis (by simp [Γ])
  have hw : Context Γ (existsCode 34 B.encode) := .head _ _
  have hbody : Context Γ (imp B.encode newLiteral.encode) := by
    apply Context.deduction
    let Δ := B.encode :: Γ
    have hb : Context Δ B.encode := .head _ _
    have hc : Context Δ (replace 33 30 oldCut).encode := Context.conjunctionLeft hb
    have hf : Context Δ (replace 33 30 oldFilter).encode := Context.conjunctionLeft (Context.conjunctionRight hb)
    have he : Context Δ oldRightEquiv.encode := Context.conjunctionRight (Context.conjunctionRight hb)
    exact .mp he (.mp hf (.mp hc (.mp (.under hp _) (.closed specialized))))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 34 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases h1 : h = oldLiteral.encode
    · subst h
      exact free_vacuity 34 oldLiteral (by decide)
    · have h2 : h = fixedAssumptions.encode := by simpa [h1] using hh
      subst h
      exact free_vacuity 34 fixedAssumptions (by decide)
  have hall : Context Γ (allCode 34 (imp B.encode newLiteral.encode)) :=
    Context.generalize 34 hv hbody
  have hout := Context.existsElim (free_vacuity 34 newLiteral (by decide)) hall hw
  exact Context.closeEmpty (Context.deduction (Context.deduction hout))

theorem literal_cut_step_certificate : theoremCode (certificate literal_cut_step) =
    imp fixedAssumptions.encode (imp oldLiteral.encode newLiteral.encode) :=
  certificate_correct literal_cut_step

/-- The exact shared strengthened relation at the new source and result. -/
def literalCut45 : Formula := replace 32 45 (replace 31 38 literalCut)

private def body45 : Formula := namedBoth (namedEither (.equal 30 45) (.member 45 30))
  (namedBoth (.all 35 (namedFilterBody 45 34 35 (Formula.member 30 35).not))
    (equivAt 38 34))

private def suffix40 : Formula := namedBoth
  (.all 35 (namedFilterBody 45 40 35 (Formula.member 30 35).not)) (equivAt 38 40)

private theorem old_shape : oldLiteral = literalCut := by decide
private theorem target_shape : literalCut45 = .ex 34 body45 := by decide
private theorem suffix_shape : replace 33 30 newSuffix = .ex 40 suffix40 := by decide

private def suffix_point : KDerivation (imp (member 45 30)
    (imp suffix40.encode literalCut45.encode)) := by
  have hi := exists_variable_intro 34 40 body45 (by decide) (by decide) (by decide)
  have hi' : KDerivation (imp (replace 34 40 body45).encode literalCut45.encode) := by
    simpa only [target_shape,Formula.encode] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [suffix40.encode,member 45 30]
  have hs : Context Γ suffix40.encode := .head _ _
  have hm : Context Γ (member 45 30) := .hypothesis (by simp [Γ])
  have hb : Context Γ (replace 34 40 body45).encode := by
    have heq : replace 34 40 body45 = namedBoth
        (namedEither (.equal 30 45) (.member 45 30)) suffix40 := by decide
    rw [heq]
    exact Context.conjunctionIntro (Context.disjunctionRight hm) hs
  exact .mp hb (.closed hi')

private def package : KDerivation (imp newLiteral.encode literalCut45.encode) := by
  let Γ := [newLiteral.encode]
  have h : Context Γ newLiteral.encode := .head _ _
  have hm : Context Γ (member 45 30) := Context.conjunctionLeft h
  have hex : Context Γ (existsCode 40 suffix40.encode) := by
    have hh := Context.conjunctionRight h
    simpa only [suffix_shape,Formula.encode] using hh
  have hpoint : Context Γ (imp suffix40.encode literalCut45.encode) :=
    .mp hm (.closed suffix_point)
  have hv : ∀ a, a ∈ Γ → KDerivation (imp a (allCode 40 a)) := by
    intro a ha
    have he : a = newLiteral.encode := by simpa [Γ] using ha
    subst a
    exact free_vacuity 40 newLiteral (by decide)
  have hall := Context.generalize 40 hv hpoint
  exact Context.closeEmpty (Context.deduction
    (Context.existsElim (free_vacuity 40 literalCut45 (by decide)) hall hex))

/-- The same cut proves the exact shared literal-cut relation at the new
second input and result. -/
def literal_cut_successor : KDerivation (imp fixedAssumptions.encode
    (imp literalCut.encode literalCut45.encode)) := by
  have hs : KDerivation (imp fixedAssumptions.encode
      (imp literalCut.encode newLiteral.encode)) := by
    simpa only [old_shape] using literal_cut_step
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [literalCut.encode,fixedAssumptions.encode]
  have hl : Context Γ literalCut.encode := .head _ _
  have hp : Context Γ fixedAssumptions.encode := .hypothesis (by simp [Γ])
  exact .mp (.mp hl (.mp hp (.closed hs))) (.closed package)

theorem literal_cut_successor_certificate : theoremCode (certificate literal_cut_successor) =
    imp fixedAssumptions.encode (imp literalCut.encode literalCut45.encode) :=
  certificate_correct literal_cut_successor
end PASoundness.PAtoCompactAdditionLiteralCutStepSpecialize
#print axioms PASoundness.PAtoCompactAdditionLiteralCutStepSpecialize.literal_cut_step
#print axioms PASoundness.PAtoCompactAdditionLiteralCutStepSpecialize.literal_cut_step_certificate
#print axioms PASoundness.PAtoCompactAdditionLiteralCutStepSpecialize.literal_cut_successor
#print axioms PASoundness.PAtoCompactAdditionLiteralCutStepSpecialize.literal_cut_successor_certificate
