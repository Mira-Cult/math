import PASoundness.PAtoCompactFirstAdditionOperandTransportPoint
import PASoundness.PAtoCompactFreeVacuity

/-! Transport one literal addition witness to two explicitly equivalent
candidate operands, retaining its actual cut and suffix. -/
namespace PASoundness.PAtoCompactFirstAdditionOperandTransport

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFirstAdditionCutAllocation PASoundness.PAtoCompactFirstAdditionOperandTransportPoint

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def newAddition : Formula := replace 32 0 (replace 31 27 (replace 30 29 additionFormula))
def fixedGuard : Formula := namedBoth (domainAt 100 29) (namedBoth (domainAt 100 27)
  (namedBoth (PASoundness.PAtoCompactTermTranslation.equivAt 100 29 28) (PASoundness.PAtoCompactTermTranslation.equivAt 100 27 1)))
def guard : Formula := namedBoth fixedGuard addition
private def newAllocated : Formula := .ex 40 (.ex 31 transportedBody)
private def rawBody : Formula := namedBoth (namedEither (.equal 33 32) (.member 32 33))
  (namedBoth (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 33)
    (namedBoth suffixFormula (PASoundness.PAtoCompactOrdinalAddition.equivAt 31 34)))
private def instantiatedBody : Formula := replace 32 0 (replace 31 27 (replace 30 29 rawBody))
private def cutBody : Formula := replace 33 40 instantiatedBody
private theorem new_shape : newAddition = .ex 33 (.ex 34 instantiatedBody) := by decide
private theorem cut_shape : replace 33 40 (.ex 34 instantiatedBody) = .ex 34 cutBody := by decide
private theorem body_shape : replace 34 31 cutBody = transportedBody := by decide

private def allocated_to_new : KDerivation (imp newAllocated.encode newAddition.encode) := by
  have hcut := (existentialAlpha 33 40 (.ex 34 instantiatedBody) (by decide) (by decide) (by decide)).2
  rw [cut_shape] at hcut
  have hsuffix := (existentialAlpha 34 31 cutBody (by decide) (by decide) (by decide)).2
  rw [body_shape] at hsuffix
  have h := compose (existsCongr 40 hsuffix) hcut
  rw [new_shape]
  simpa only [newAllocated,Formula.encode] using h

/-- Given candidate new operands and oriented equivalences to the old ones,
the same output satisfies the literal addition relation for the new pair. -/
def transport_first_addition_operands : KDerivation (imp guard.encode newAddition.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hf : Context Γ fixedGuard.encode := Context.conjunctionLeft hg
  have ha : Context Γ addition.encode := Context.conjunctionRight hg
  have hex : Context Γ allocated.encode := .mp ha (.closed allocate_first_addition)
  have hlocal : Context (allocatedBody.encode :: Γ) newAllocated.encode := by
    let Δ := allocatedBody.encode :: Γ
    have hb : Context Δ allocatedBody.encode := .head _ _
    have hf' : Context Δ fixedGuard.encode := .under hf _
    have hd29 : Context Δ (domainAt 100 29).encode := Context.conjunctionLeft hf'
    have hr := Context.conjunctionRight hf'
    have hd27 : Context Δ (domainAt 100 27).encode := Context.conjunctionLeft hr
    have hr := Context.conjunctionRight hr
    have heA : Context Δ (PASoundness.PAtoCompactTermTranslation.equivAt 100 29 28).encode := Context.conjunctionLeft hr
    have heB : Context Δ (PASoundness.PAtoCompactTermTranslation.equivAt 100 27 1).encode := Context.conjunctionRight hr
    have hp : Context Δ PASoundness.PAtoCompactFirstAdditionOperandTransportPoint.guard.encode :=
      Context.conjunctionIntro hd29 (Context.conjunctionIntro hd27 (Context.conjunctionIntro heA
        (Context.conjunctionIntro heB hb)))
    have hbody : Context Δ transportedBody.encode := .mp hp (.closed transport_operand_witness)
    have h31 : Context Δ (existsCode 31 transportedBody.encode) :=
      .mp hbody (.closed (existsIntroduce 31 transportedBody (by decide)))
    have hi : KDerivation (imp (existsCode 31 transportedBody.encode) newAllocated.encode) := by
      simpa only [newAllocated,Formula.encode] using existsIntroduce 40 (.ex 31 transportedBody) (by decide)
    exact .mp h31 (.closed hi)
  have hv31 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 31 h)) := by
    intro h hh
    have he : h = guard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 31 guard (by decide)
  have hall31 := Context.generalize 31 hv31 (Context.deduction hlocal)
  have hinner : Context ((.ex 31 allocatedBody : Formula).encode :: Γ) newAllocated.encode := by
    have he : Context ((.ex 31 allocatedBody : Formula).encode :: Γ) (existsCode 31 allocatedBody.encode) := .head _ _
    exact Context.existsElim (free_vacuity 31 newAllocated (by decide)) (.under hall31 _) he
  have hv40 : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 40 h)) := by
    intro h hh
    have he : h = guard.encode := by simpa [Γ] using hh
    subst h
    exact free_vacuity 40 guard (by decide)
  have halloc : Context Γ newAllocated.encode := Context.existsElim (free_vacuity 40 newAllocated (by decide))
    (Context.generalize 40 hv40 (Context.deduction hinner)) hex
  exact .mp halloc (.closed allocated_to_new)

theorem transport_first_addition_operands_certificate : theoremCode (certificate transport_first_addition_operands) =
    imp guard.encode newAddition.encode := certificate_correct transport_first_addition_operands

end PASoundness.PAtoCompactFirstAdditionOperandTransport

#print axioms PASoundness.PAtoCompactFirstAdditionOperandTransport.newAddition
#print axioms PASoundness.PAtoCompactFirstAdditionOperandTransport.fixedGuard
#print axioms PASoundness.PAtoCompactFirstAdditionOperandTransport.guard
#print axioms PASoundness.PAtoCompactFirstAdditionOperandTransport.transport_first_addition_operands
#print axioms PASoundness.PAtoCompactFirstAdditionOperandTransport.transport_first_addition_operands_certificate
