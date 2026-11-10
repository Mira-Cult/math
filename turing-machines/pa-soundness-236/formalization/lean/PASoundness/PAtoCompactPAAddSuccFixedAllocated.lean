import PASoundness.PAtoCompactAdditionSuccessorStepClosed
import PASoundness.PAtoCompactAdditionZeroAllocated
import PASoundness.PAtoCompactScopedActiveReplace
import PASoundness.PAtoCompactAddTermBody

/-! A fixed-name, allocated addition-successor relation. This constructs K
proof data from the existing fixed-name step and alpha transports; it does not
establish the PA axiom or arbitrary operand renaming. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddSuccFixedAllocated
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAdditionZeroAllocated PASoundness.PAtoCompactAdditionSuccessorPackage
open PASoundness.PAtoCompactAdditionSuccessorLocalStep PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactAddTermBody
open PASoundness.PAtoCompactAddBaseSyntax PASoundness.PAtoCompactAddBaseInventory
open PASoundness.PAtoCompactVacuousQuantifierFree

/-- Transport the output addition formula to the allocated template while
retaining its fixed operand names. -/
noncomputable def new_addition_allocated (b : Nat) (hb : 46 ≤ b) :
    KBoth addition45 (addAt b 30 38 45) := by
  have ha := original_allocated_alpha b (by omega)
  have hs : addTemplate = additionFormula := by decide
  rw [hs] at ha
  have hf31 : 31 ∉ additionFormula.binders := by decide
  have hf38 : 38 ∉ additionFormula.binders := by decide
  have hg31 : 31 ∉ (addAt b 30 31 32).binders := by
    intro h; have hh := addAt_private b 30 31 32 31 h; omega
  have hg38 : 38 ∉ (addAt b 30 31 32).binders := by
    intro h; have hh := addAt_private b 30 31 32 38 h; omega
  have h1 := replace_implications 31 38 additionFormula (addAt b 30 31 32)
    hf31 hg31 hf38 hg38 ha.forward ha.backward
  have hr1 : replace 31 38 (addAt b 30 31 32) = addAt b 30 38 32 := by
    rw [replace_addAt b 30 31 32 31 38 (by omega)]
    simp [rename]
  rw [hr1] at h1
  have hf32 : 32 ∉ (replace 31 38 additionFormula).binders := by
    simpa only [replace_binders] using (show 32 ∉ additionFormula.binders by decide)
  have hf45 : 45 ∉ (replace 31 38 additionFormula).binders := by
    simpa only [replace_binders] using (show 45 ∉ additionFormula.binders by decide)
  have hg32 : 32 ∉ (addAt b 30 38 32).binders := by
    intro h; have hh := addAt_private b 30 38 32 32 h; omega
  have hg45 : 45 ∉ (addAt b 30 38 32).binders := by
    intro h; have hh := addAt_private b 30 38 32 45 h; omega
  have h2 := replace_implications 32 45 (replace 31 38 additionFormula)
    (addAt b 30 38 32) hf32 hg32 hf45 hg45 h1.1 h1.2
  have hr2 : replace 32 45 (addAt b 30 38 32) = addAt b 30 38 45 := by
    rw [replace_addAt b 30 38 32 32 45 (by omega)]
    simp [rename]
  rw [hr2] at h2
  simpa only [addition45, KBoth] using h2

/-- Fixed-name successor compatibility at any sufficiently high private
allocation base. The two candidate and raw successor assumptions are the
literal antecedent `fixedAssumptions` of the existing K derivation. -/
noncomputable def fixed_allocated_step (b : Nat) (hb : 46 ≤ b) :
    KDerivation (imp fixedAssumptions.encode
      (imp (addAt b 30 31 32).encode (addAt b 30 38 45).encode)) := by
  have ha := original_allocated_alpha b (by omega)
  have hs : addTemplate = additionFormula := by decide
  rw [hs] at ha
  have hn := new_addition_allocated b hb
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(addAt b 30 31 32).encode, fixedAssumptions.encode]
  have hA : Context Γ (addAt b 30 31 32).encode := .head _ _
  have hP : Context Γ fixedAssumptions.encode := .hypothesis (by simp [Γ])
  have hOld : Context Γ additionFormula.encode := .mp hA (.closed ha.backward)
  have hNew : Context Γ addition45.encode :=
    .mp hOld (.mp hP (.closed PASoundness.PAtoCompactAdditionSuccessorStepClosed.addition_successor_step))
  exact .mp hNew (.closed hn.1)

theorem fixed_allocated_step_certificate (b : Nat) (hb : 46 ≤ b) :
    theoremCode (certificate (fixed_allocated_step b hb)) = imp fixedAssumptions.encode
      (imp (addAt b 30 31 32).encode (addAt b 30 38 45).encode) := certificate_correct _
end PASoundness.PAtoCompactPAAddSuccFixedAllocated
#print axioms PASoundness.PAtoCompactPAAddSuccFixedAllocated.new_addition_allocated
#print axioms PASoundness.PAtoCompactPAAddSuccFixedAllocated.fixed_allocated_step
#print axioms PASoundness.PAtoCompactPAAddSuccFixedAllocated.fixed_allocated_step_certificate
