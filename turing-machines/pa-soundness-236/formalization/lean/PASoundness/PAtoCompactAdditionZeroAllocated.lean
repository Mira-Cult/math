import PASoundness.PAtoCompactAdditionZeroCandidateOutput
import PASoundness.PAtoCompactAddBaseMultiAlpha
import PASoundness.PAtoCompactZeroBaseTransport
import PASoundness.PAtoCompactAlphaCongruence

/-! Capture-safe alignment toward the allocated right-zero addition witness.
This preliminary candidate bridge does not establish arbitrary addition. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionZeroAllocated

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactCandidateExact PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactOrdinalAddition PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactCandidateFieldTransport PASoundness.PAtoCompactCandidateBinderBridge
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactAdditionZeroCandidateOutput

open PASoundness.PAtoCompactMultiAlpha PASoundness.PAtoCompactSafeStepsInitial
open PASoundness.PAtoCompactAddBaseInventory PASoundness.PAtoCompactAddBaseSyntax
open PASoundness.PAtoCompactEquivStepsSyntax PASoundness.PAtoCompactMapNamesCongr

def oldSteps (b : Nat) : List (Nat × Nat) := addOffsets.map (fun k => (k, b+2+k))

theorem step_fix (b z : Nat) (hz : z = 30 ∨ z = 31 ∨ z = 32) : applySteps (oldSteps b) z = z := by
  apply applySteps_avoid
  intro p hp
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
  simp only
  simp [addOffsets] at hk
  omega

theorem step_hit (b k : Nat) (hb : 38 ≤ b) (hk : k ∈ addOffsets) :
    applySteps (oldSteps b) k = b+2+k := by
  apply applySteps_hit
  · exact List.mem_map.mpr ⟨k,hk,rfl⟩
  · intro z hz
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hz
    have hi1 := congrArg Prod.fst he
    have hi2 := congrArg Prod.snd he
    simp only at hi1 hi2
    omega
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    have hil := addOffsets_lt i hi
    omega

theorem old_safe (b : Nat) (hb : 38 ≤ b) : InitialSafe (oldSteps b) addTemplate := by
  refine ⟨?_, ?_, addition_allNoShadow⟩
  · intro p hp
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    have hl := addOffsets_lt k hk
    simp only [addition_free, addition_names, Finset.mem_insert, Finset.mem_singleton, not_or]
    simp [addOffsets] at hk
    omega
  · have hn : addOffsets.Nodup := by decide
    have hi : Function.Injective (fun k : Nat => b + 2 + k) := by
      intro x y h
      change b + 2 + x = b + 2 + y at h
      omega
    simpa [oldSteps, List.map_map, Function.comp_def] using List.Nodup.map hi hn

theorem old_shape (b : Nat) (hb : 38 ≤ b) :
    renameSteps (oldSteps b) addTemplate = addAt b 30 31 32 := by
  rw [renameSteps_eq_map]
  unfold addAt
  change mapNames (applySteps (oldSteps b)) addTemplate =
    mapNames (threeMap b 30 31 32 30 31 32) addTemplate
  apply mapNames_congr
  intro k hk
  have hs := addition_names_subset hk
  simp only [Finset.mem_insert, List.mem_toFinset] at hs
  rcases hs with rfl | rfl | rfl | hs
  · simpa [threeMap] using step_fix b 30 (Or.inl rfl)
  · simpa [threeMap] using step_fix b 31 (Or.inr (Or.inl rfl))
  · simpa [threeMap] using step_fix b 32 (Or.inr (Or.inr rfl))
  · have h30 : k ≠ 30 := by simp [addOffsets] at hs; omega
    have h31 : k ≠ 31 := by simp [addOffsets] at hs; omega
    have h32 : k ≠ 32 := by simp [addOffsets] at hs; omega
    simpa [threeMap, h30,h31,h32] using step_hit b k hb hs

def original_allocated_alpha (b : Nat) (hb : 38 ≤ b) : ProofEquiv addTemplate (addAt b 30 31 32) := by
  have h := multiAlpha (oldSteps b) addTemplate (initial_safe_steps _ _ (old_safe b hb))
  rw [old_shape b hb] at h
  exact h

/-- Reverse the seven fixed candidate-binder moves. The represented object
is unchanged, and all intermediate name conditions are checked in K. -/
def guard_to_input_candidate : KDerivation
    (imp (domainAt 100 30).encode (candidateCode 30 41 37 38 32 0 31 34 35)) := by
  have h1 := order_field 30 132 133 134 135 136 137 138 139 35 (by decide) (by decide)
  have h2 := witness_field 30 132 133 134 135 136 137 138 35 34 (by decide) (by decide)
  have h3 := nonempty_field 30 132 133 134 135 136 137 34 35 31 (by decide)
  have h4 := subset_test_field 30 132 133 134 135 136 31 34 35 0 (by decide) (by decide)
  have h5 := subset_field 30 132 133 134 135 0 31 34 35 32 (by decide) (by decide)
  have h6 := member_field 30 132 133 134 32 0 31 34 35 41 (by decide)
  have h7 := transitivity_field 30 41 133 134 32 0 31 34 35 37 38 (by decide)
  rw [domainAt_encode]
  exact compose h1 (compose h2 (compose h3 (compose h4 (compose h5 (compose h6 h7)))))

/-- The fixed right-zero witness can therefore be used under a standard
allocated candidate guard. The right-zero and literal output relation remain
as in the imported fixed theorem. -/
def guarded_fixed_right_zero : KDerivation
    (imp (domainAt 100 30).encode
      (imp (zeroCode 31 36) (existsCode 32 outputBody.encode))) :=
  compose guard_to_input_candidate right_zero_candidate_output

/-- The standard zero guard implies the fixed zero formula by safe alpha conversion. -/
def zero_to_fixed : KDerivation (imp (zeroAt 100 31).encode (zeroCode 31 36)) := by
  have h := PAtoCompactZeroBaseTransport.zeroAt_base_forward 100 33 31 (by decide) (by decide)
  simpa [PAtoCompactZeroBaseTransport.zeroAt_shape, Formula.encode, zeroCode, neg] using h

/-- Right-zero addition with standard guards and an allocated addition body.
The operands and output are the displayed fixed variables. -/
def guarded_allocated_right_zero (c : Nat) (hc : 38 ≤ c) : KDerivation
    (imp (domainAt 100 30).encode (imp (zeroAt 100 31).encode
      (existsCode 32 (andF (domainAt 100 32) (addAt c 30 31 32)).encode))) := by
  have hbody : ProofEquiv outputBody (andF (domainAt 100 32) (addAt c 30 31 32)) := by
    have ha := original_allocated_alpha c hc
    have hs : addTemplate = additionFormula := by decide
    rw [hs] at ha
    exact PAtoCompactAlphaCongruence.andF_congr (ProofEquiv.refl _) ha
  have hex := (ProofEquiv.existential 32 hbody).forward
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(zeroAt 100 31).encode, (domainAt 100 30).encode]
  have hz : Context Γ (zeroAt 100 31).encode := .head _ _
  have hd : Context Γ (domainAt 100 30).encode := .hypothesis (by simp [Γ])
  have hzf : Context Γ (zeroCode 31 36) := .mp hz (.closed zero_to_fixed)
  have ho : Context Γ (existsCode 32 outputBody.encode) :=
    .mp hzf (.mp hd (.closed guarded_fixed_right_zero))
  exact .mp ho (.closed hex)

theorem guarded_fixed_right_zero_certificate :
    theoremCode (certificate guarded_fixed_right_zero) =
      imp (domainAt 100 30).encode
        (imp (zeroCode 31 36) (existsCode 32 outputBody.encode)) :=
  certificate_correct _

end PASoundness.PAtoCompactAdditionZeroAllocated

#print axioms PASoundness.PAtoCompactAdditionZeroAllocated.guard_to_input_candidate
#print axioms PASoundness.PAtoCompactAdditionZeroAllocated.guarded_fixed_right_zero
#print axioms PASoundness.PAtoCompactAdditionZeroAllocated.guarded_fixed_right_zero_certificate

#print axioms PASoundness.PAtoCompactAdditionZeroAllocated.guarded_allocated_right_zero
