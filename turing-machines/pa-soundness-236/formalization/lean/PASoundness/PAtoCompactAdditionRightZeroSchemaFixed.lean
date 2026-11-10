import PASoundness.PAtoCompactAdditionZeroAllocated
import PASoundness.PAtoCompactAdditionRightZeroConverse
import PASoundness.PAtoCompactAdditionIdentityClosedCut
import PASoundness.PAtoCompactUnaryGraphFunctional

namespace PASoundness.PAtoCompactAdditionRightZeroSchemaFixed
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroBaseTransport
open PASoundness.PAtoCompactAdditionZeroAllocated PASoundness.PAtoCompactUnaryGraphFunctional
open PASoundness.PAtoCompactAddBaseInventory
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactTemplateBlockShift PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactEquivNoShadow
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] PASoundness.CompactProof.imp Cantor.pair Cantor.triangle

private theorem bfree0 : (0:Nat) ∉ equivTemplate.binders := by decide
private theorem bfree1 : (1:Nat) ∉ equivTemplate.binders := by decide
private theorem bfree30 : (30:Nat) ∉ equivTemplate.binders := by decide
private theorem bfree32 : (32:Nat) ∉ equivTemplate.binders := by decide

private theorem allocated_replace (b x y a z : Nat) (ha : a < b) :
    replace a z (equivAt b x y) = equivAt b (rename a z x) (rename a z y) := by
  rw [← map_eq_replace a z _ (by intro h; have := equivAt_private b x y a h; omega)]
  exact equivAt_shift (rename a z) b b x y (by intro i hi; simp [rename, show b+i ≠ a by omega])

private def equiv_fixed_alpha (b : Nat) (hb : 40 ≤ b) :
    KDerivation (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 32).encode
      (equivAt b 30 32).encode) ×
    KDerivation (imp (equivAt b 30 32).encode
      (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 32).encode) := by
  let E := equivTemplate
  let F := equivAt b 0 1
  have ah := canonical_equiv_alpha b hb
  have h30 : 30 ∉ F.binders := by intro h; have := equivAt_private b 0 1 30 h; omega
  have h0 : 0 ∉ F.binders := by intro h; have := equivAt_private b 0 1 0 h; omega
  have h1 : 1 ∉ F.binders := by intro h; have := equivAt_private b 0 1 1 h; omega
  have h32 : 32 ∉ F.binders := by intro h; have := equivAt_private b 0 1 32 h; omega
  have r := replace_implications 0 30 E F bfree0 h0 bfree30 h30 ah.forward ah.backward
  have he : replace 0 30 F = equivAt b 30 1 := by simpa [F, rename] using allocated_replace b 0 1 0 30 (by omega)
  have ha : 1 ∉ (replace 0 30 E).binders := by simpa [replace_binders] using bfree1
  have hb' : 32 ∉ (replace 0 30 E).binders := by simpa [replace_binders] using bfree32
  have hc : 1 ∉ (replace 0 30 F).binders := by simpa [replace_binders] using h1
  have hd : 32 ∉ (replace 0 30 F).binders := by simpa [replace_binders] using h32
  have r2 := replace_implications 1 32 (replace 0 30 E) (replace 0 30 F) ha hc hb' hd r.1 r.2
  have he2 : replace 1 32 (replace 0 30 F) = equivAt b 30 32 := by
    rw [he]
    simpa [rename] using allocated_replace b 30 1 1 32 (by omega)
  rw [he2] at r2
  have hsFormula : replace 1 32 (replace 0 30 E) =
      normalizeBottom (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 32) := by
    decide
  have hs : (replace 1 32 (replace 0 30 E)).encode =
      (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 32).encode := by
    rw [hsFormula, normalizeBottom_encode]
  exact ⟨by simpa only [hs] using r2.1, by simpa only [hs] using r2.2⟩



/-- At fixed inputs, transport the canonical right-zero converse to the
allocated templates. No graph totality or arithmetic soundness is assumed. -/
def fixed_forward (b : Nat) (hb : 40 ≤ b) :
    KDerivation (imp (zeroAt b 31).encode
      (imp (addAt b 30 31 32).encode (equivAt b 30 32).encode)) := by
  have hz0 := zeroAt_base_forward b 33 31 (by omega) (by omega)
  have hzero : KDerivation (imp (zeroAt b 31).encode (zeroCode 31 36)) := by
    have he : (zeroAt 33 31).encode = zeroCode 31 36 := rfl
    rw [← he]
    exact hz0
  have aa := original_allocated_alpha b (by omega)
  have htemplate : addTemplate = PASoundness.PAtoCompactOrdinalAddition.additionFormula := by decide
  rw [htemplate] at aa
  have ar : KDerivation (imp (addAt b 30 31 32).encode
      PASoundness.PAtoCompactOrdinalAddition.additionFormula.encode) := aa.backward
  have eq := equiv_fixed_alpha b hb
  have eqf : KDerivation (imp (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 32).encode
      (equivAt b 30 32).encode) := eq.1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(addAt b 30 31 32).encode, (zeroAt b 31).encode]
  have hA : Context Γ (addAt b 30 31 32).encode := Context.head _ _
  have hZ : Context Γ (zeroAt b 31).encode := .hypothesis (by simp [Γ])
  have hZ' : Context Γ (zeroCode 31 36) := .mp hZ (.closed hzero)
  have hA' : Context Γ PASoundness.PAtoCompactOrdinalAddition.additionFormula.encode :=
    .mp hA (.closed ar)
  have hE : Context Γ (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 32).encode :=
    .mp hA' (.mp hZ' (.closed PASoundness.PAtoCompactAdditionRightZeroConverse.addition_zero_right_converse))
  exact .mp hE (.closed eqf)

/-- The reverse direction uses the same fixed source names and allocators. -/
def fixed_backward (b : Nat) (hb : 40 ≤ b) :
    KDerivation (imp (zeroAt b 31).encode
      (imp (equivAt b 30 32).encode (addAt b 30 31 32).encode)) := by
  have hz0 := zeroAt_base_forward b 33 31 (by omega) (by omega)
  have hzero : KDerivation (imp (zeroAt b 31).encode (zeroCode 31 36)) := by
    have he : (zeroAt 33 31).encode = zeroCode 31 36 := rfl
    rw [← he]
    exact hz0
  have aa := original_allocated_alpha b (by omega)
  have htemplate : addTemplate = PASoundness.PAtoCompactOrdinalAddition.additionFormula := by decide
  rw [htemplate] at aa
  have af : KDerivation (imp PASoundness.PAtoCompactOrdinalAddition.additionFormula.encode
      (addAt b 30 31 32).encode) := aa.forward
  have eq := equiv_fixed_alpha b hb
  have eqr : KDerivation (imp (equivAt b 30 32).encode
      (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 32).encode) := eq.2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(equivAt b 30 32).encode, (zeroAt b 31).encode]
  have hE : Context Γ (equivAt b 30 32).encode := Context.head _ _
  have hZ : Context Γ (zeroAt b 31).encode := .hypothesis (by simp [Γ])
  have hZ' : Context Γ (zeroCode 31 36) := .mp hZ (.closed hzero)
  have hE' : Context Γ (PASoundness.PAtoCompactOrdinalAddition.equivAt 30 32).encode :=
    .mp hE (.closed eqr)
  have hA : Context Γ PASoundness.PAtoCompactOrdinalAddition.additionFormula.encode :=
    .mp hE' (.mp hZ' (.closed PASoundness.PAtoCompactAdditionIdentityClosedCut.addition_of_zero_right))
  exact .mp hA (.closed af)

end PASoundness.PAtoCompactAdditionRightZeroSchemaFixed

#print axioms PASoundness.PAtoCompactAdditionRightZeroSchemaFixed.equiv_fixed_alpha

#print axioms PASoundness.PAtoCompactAdditionRightZeroSchemaFixed.fixed_forward
#print axioms PASoundness.PAtoCompactAdditionRightZeroSchemaFixed.fixed_backward
