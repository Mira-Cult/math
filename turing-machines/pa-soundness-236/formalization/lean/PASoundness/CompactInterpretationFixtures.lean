import PASoundness.CompactSyntaxBridge
import PASoundness.HFCoding

/-! Scope and coding regressions for the quantified interpretation proofs. -/
namespace PASoundness.CompactInterpretationFixtures
open FirstOrder FirstOrder.Language CompactArithmetic CompactMatrix

/-- Input free names deliberately coincide with internal template binder names.
Canonical substitution keeps those input names free. -/
theorem occupied_template_names :
    (bitFormula (v 2) (v 3)).Realize
      (fun x => if x = 2 then 42 else if x = 3 then 1 else 99) := by
  rw [realize_bitFormula_exact]
  decide

theorem template_names_remain_free :
    (bitFormula (v 2) (v 3)).freeVarFinset = {2,3} := by
  simp [bitFormula_freeVars,v]

/-- This is standard-model irreflexivity, not a claimed finite PA proof. -/
theorem bit_self_false (t : Peano.Term) (ρ : Nat → Nat) :
    ¬ (bitFormula t t).Realize ρ := by
  rw [realize_bitFormula_exact,CompactMatrix.bit_self_false]
  decide

theorem beta_remainder_is_strict : ¬ Beta 7 1 1 3 := by
  rw [beta_iff_mod]
  decide

theorem pow_zero_exact : Pow2 0 1 ∧ ¬ Pow2 0 0 := by
  simp [pow2_iff]

/-- Substituting free name 1 by free name 0 under an existing binder for
name 0 leaves the substituted occurrence free. The resulting universal
equality is false, rather than the tautology forall x, x=x. -/
theorem substitution_avoids_capture (ρ : Nat → Nat) :
    ¬ FirstOrder.Language.Formula.Realize
      ((translate (.all 0 (.equal 1 0))).subst
        (fun x => if x = 1 then (v 0) else v x)) ρ := by
  rw [realize_translate_subst]
  intro h
  have hh := h (ρ 0 + 1)
  simp [CompactMatrix.Formula.Realize,CompactMatrix.update,v] at hh

/-- The actual producer closes unbound names with zero, while an explicit
quantifier remains a genuine quantifier. These two cases must differ. -/
theorem free_zero_equality_true :
    Nat ⊨ toPA (CompactProof.equal 0 1) := by
  rw [truth_toPA,CompactSemantics.decode_equal]
  rfl

theorem bound_equality_false :
    ¬ (Nat ⊨ toPA (CompactProof.allCode 0 (CompactProof.equal 0 1))) := by
  rw [truth_toPA,CompactSemantics.decode_all,CompactSemantics.decode_equal]
  intro h
  have hh := h 1
  simp [CompactMatrix.Formula.Realize,CompactMatrix.update] at hh

theorem hf_membership_orientation :
    (HFCoding.Object.mk 0 ∈ HFCoding.Object.mk 1) ∧
      ¬ (HFCoding.Object.mk 1 ∈ HFCoding.Object.mk 0) := by decide

end PASoundness.CompactInterpretationFixtures
