import PASoundness.PAtoCompactLiteralCutAdditionDefinition
import PASoundness.PAtoCompactAdditionResultSuccessorExists39
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.CompactQuantifiers

/-! A pointwise existential-witness lift for candidate-guarded literal-cut addition
induction. The displayed local successor law is a finite K proof input. The
result successor is constructed inside K. No semantic soundness, general
induction, or addition totality is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLiteralCutInductionWitnessBind
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactLiteralCutAdditionDefinition
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactAdditionResultSuccessorExists39
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Old and new instances of the literal addition relation, with distinct
source and result names. -/
def oldAdd : Formula := replace 31 204 literalCut
def newAdd : Formula := replace 32 45 (replace 31 205 literalCut)
def oldOutput : Formula := andF (domainAt 100 32) oldAdd
def newOutput : Formula := andF (domainAt 100 32) (replace 31 205 literalCut)
def result : Formula := .ex 32 newOutput

private theorem result_inst : replace 32 45 newOutput = andF (domainAt 100 45) newAdd := by decide

/-- A single explicitly supplied local K successor law suffices to lift an
old candidate output to a new candidate output. The result successor is
constructed, and names 32 and 45 denote the old and new outputs respectively. -/
def witness_bind
    (hstep : KDerivation (imp (domainAt 100 204).encode
      (imp (domainAt 100 32).encode
        (imp (successorCode 204 205 208) (imp (successorCode 32 45 39)
          (imp oldAdd.encode newAdd.encode)))))) :
    KDerivation (imp (domainAt 100 204).encode
      (imp (successorCode 204 205 208)
        (imp (existsCode 32 oldOutput.encode) result.encode))) := by
  let D := (domainAt 100 204).encode
  let S := successorCode 204 205 208
  let R := result.encode
  let O := oldOutput.encode
  let E := both (successorCode 32 45 39) (domainAt 100 45).encode
  have hinner : KDerivation (imp D (imp S (imp O (imp E R)))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [E,O,S,D]
    have he : Context Γ E := .head _ _
    have ho : Context Γ O := .hypothesis (by simp [Γ])
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have hd : Context Γ D := .hypothesis (by simp [Γ])
    have hd32 : Context Γ (domainAt 100 32).encode := Context.conjunctionLeft ho
    have ha : Context Γ oldAdd.encode := Context.conjunctionRight ho
    have hs45 : Context Γ (successorCode 32 45 39) := Context.conjunctionLeft he
    have hd45 : Context Γ (domainAt 100 45).encode := Context.conjunctionRight he
    have ha45 : Context Γ newAdd.encode := .mp ha (.mp hs45 (.mp hs (.mp hd32 (.mp hd (.closed hstep)))))
    have hp : Context Γ (replace 32 45 newOutput).encode := by
      rw [result_inst]
      exact Context.conjunctionIntro hd45 ha45
    have hi := exists_variable_intro 32 45 newOutput (by decide) (by decide) (by decide)
    exact .mp hp (.closed hi)
  have hpoint : KDerivation (imp D (imp S (imp O R))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [O,S,D]
    have ho : Context Γ O := .head _ _
    have hs : Context Γ S := .hypothesis (by simp [Γ])
    have hd : Context Γ D := .hypothesis (by simp [Γ])
    have hd32 : Context Γ (domainAt 100 32).encode := Context.conjunctionLeft ho
    have hex : Context Γ (existsCode 45 E) := .mp hd32 (.closed result_successor_exists39)
    have hcond : Context Γ (imp E R) := .mp ho (.mp hs (.mp hd (.closed hinner)))
    have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 45 h)) := by
      intro h hh
      simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
      by_cases hO : h = O
      · subst h; exact oldOutput.vacuity 45 (by decide)
      by_cases hS : h = S
      · subst h; exact (namedSuccessor 204 205 208).vacuity 45 (by decide)
      have hD : h = D := by simpa [hO,hS] using hh
      subst h
      exact (domainAt 100 204).vacuity 45 (by decide)
    have hall := Context.generalize 45 hv hcond
    exact Context.existsElim (result.vacuity 45 (by decide)) hall hex
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [existsCode 32 O,S,D]
  have hex : Context Γ (existsCode 32 O) := .head _ _
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have hc : Context Γ (imp O R) := .mp hs (.mp hd (.closed hpoint))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 32 h)) := by
    intro h hh
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hh
    by_cases hE : h = existsCode 32 O
    · subst h; exact free_vacuity 32 (.ex 32 oldOutput) (by decide)
    by_cases hS : h = S
    · subst h; exact (namedSuccessor 204 205 208).vacuity 32 (by decide)
    have hD : h = D := by simpa [hE,hS] using hh
    subst h
    exact (domainAt 100 204).vacuity 32 (by decide)
  have hall := Context.generalize 32 hv hc
  exact Context.existsElim (free_vacuity 32 result (by decide)) hall hex

theorem witness_bind_certificate
    (hstep : KDerivation (imp (domainAt 100 204).encode
      (imp (domainAt 100 32).encode
        (imp (successorCode 204 205 208) (imp (successorCode 32 45 39)
          (imp oldAdd.encode newAdd.encode)))))) :
    theoremCode (certificate (witness_bind hstep)) =
      imp (domainAt 100 204).encode (imp (successorCode 204 205 208)
        (imp (existsCode 32 oldOutput.encode) result.encode)) := certificate_correct _
end PASoundness.PAtoCompactLiteralCutInductionWitnessBind
#print axioms PASoundness.PAtoCompactLiteralCutInductionWitnessBind.witness_bind
#print axioms PASoundness.PAtoCompactLiteralCutInductionWitnessBind.witness_bind_certificate
