import PASoundness.PAtoCompactSelectedCutRenamedGuard
import PASoundness.PAtoCompactSelectedCutAliasEliminate

/-! Retain the renamed selected cut's original graph edge while eliminating
its explicitly shifted endpoint guards into the allocated quotient formula.
No suffix isomorphism or whole-output equivalence is constructed here. -/
namespace PASoundness.PAtoCompactSelectedCutRenamedAllocated
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactLessRightSegmentAliases
open PASoundness.PAtoCompactSelectedCutRenamedGuard PASoundness.PAtoCompactSelectedCutAliasEliminate
set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The same target cut41 retains membership, original graph60 edge, and
allocated equivalence to the original cut33. Values may coincide. -/
def allocatedBody : Formula := namedBoth (namedBoth (.member 8 41) (graphFormula 60 33 41))
  (equivAt 100 33 41)
def allocatedSelected : Formula := .ex 41 allocatedBody

/-- Replace only the explicit shifted quotient guard by its K-proved allocated
consequence, without discarding or reselecting the cut witness. -/
def selected_cut_renamed_allocated : KDerivation
    (imp (namedTrans 32 11 12).encode (imp (namedTrans 8 16 18).encode
      (imp (member 32 33) (imp targetOrder.encode (imp targetBijection.encode allocatedSelected.encode))))) := by
  have hshape : shiftedGuard = freshGuard := by rfl
  have hp : KDerivation (imp targetBody.encode allocatedBody.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [targetBody.encode]
    have h : Context Γ targetBody.encode := .head _ _
    have hi : Context Γ (namedBoth (.member 8 41) (graphFormula 60 33 41)).encode :=
      Context.conjunctionLeft h
    have hg : Context Γ shiftedGuard.encode := Context.conjunctionRight h
    have he : Context Γ (equivAt 100 33 41).encode := by
      rw [hshape] at hg
      exact .mp hg (.closed fresh_guard_to_allocated)
    simpa only [allocatedBody,namedBoth,Formula.not,Formula.encode,both,neg] using
      Context.conjunctionIntro hi he
  have hlift : KDerivation (imp targetSelected.encode allocatedSelected.encode) := by
    change KDerivation (imp (existsCode 41 targetBody.encode) (existsCode 41 allocatedBody.encode))
    exact existsCongr 41 hp
  have hframe : KDerivation
      (imp (namedTrans 32 11 12).encode (imp (namedTrans 8 16 18).encode
        (imp (member 32 33) (imp targetOrder.encode (imp targetBijection.encode targetSelected.encode))))) := by
    simpa only [targetFrame,Formula.encode] using selected_cut_renamed_guard
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [targetBijection.encode,targetOrder.encode,member 32 33,
    (namedTrans 8 16 18).encode,(namedTrans 32 11 12).encode]
  have hi : Context Γ targetBijection.encode := .head _ _
  have ho : Context Γ targetOrder.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 32 33) := .hypothesis (by simp [Γ])
  have ht : Context Γ (namedTrans 8 16 18).encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (namedTrans 32 11 12).encode := .hypothesis (by simp [Γ])
  have hcut : Context Γ targetSelected.encode := .mp hi (.mp ho (.mp hm (.mp ht (.mp hs (.closed hframe)))))
  exact .mp hcut (.closed hlift)

theorem selected_cut_renamed_allocated_certificate :
    theoremCode (certificate selected_cut_renamed_allocated) =
      imp (namedTrans 32 11 12).encode (imp (namedTrans 8 16 18).encode
        (imp (member 32 33) (imp targetOrder.encode (imp targetBijection.encode allocatedSelected.encode)))) :=
  certificate_correct selected_cut_renamed_allocated
end PASoundness.PAtoCompactSelectedCutRenamedAllocated

#print axioms PASoundness.PAtoCompactSelectedCutRenamedAllocated.selected_cut_renamed_allocated
#print axioms PASoundness.PAtoCompactSelectedCutRenamedAllocated.selected_cut_renamed_allocated_certificate
