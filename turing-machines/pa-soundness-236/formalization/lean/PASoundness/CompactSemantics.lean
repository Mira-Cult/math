import PASoundness.CompactProof
import PASoundness.CompactMatrix
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Finset.Basic

/-!
# Standard finite-set semantics of the exact compact calculus

The semantic domain is Nat with Ackermann membership: `member a b` means
that the number assigned to b is a member of the finite set coded by the
number assigned to a. This module proves variable freshness and the literal
compact axiom semantics. It does not identify compact provability with PA
provability or use consistency to fabricate a proof translation.
-/

namespace PASoundness.CompactMatrix.Formula

/-- All mentioned names, including bound-variable labels. -/
def vars : Formula → Finset Nat
  | .truth => ∅
  | .imp a b => a.vars ∪ b.vars
  | .member a b | .equal a b => {a,b}
  | .all x a => insert x a.vars

/-- Free names, with the actual named binder removing its own occurrences. -/
def freeVars : Formula → Finset Nat
  | .truth => ∅
  | .imp a b => a.freeVars ∪ b.freeVars
  | .member a b | .equal a b => {a,b}
  | .all x a => a.freeVars.erase x

theorem freeVars_subset_vars (f : Formula) : f.freeVars ⊆ f.vars := by
  induction f with
  | truth | member | equal => exact Finset.Subset.refl _
  | imp a b ia ib => exact Finset.union_subset_union ia ib
  | all x f ih =>
    exact (Finset.erase_subset x f.freeVars).trans
      (ih.trans (Finset.subset_insert x f.vars))

end PASoundness.CompactMatrix.Formula

namespace PASoundness.CompactSemantics

open Cantor CompactProof CompactMatrix

@[simp] theorem update_same (ρ : Environment) (x a : Nat) : update ρ x a x = a := by
  simp [update]

@[simp] theorem update_other (ρ : Environment) (x y a : Nat) (h : y ≠ x) :
    update ρ x a y = ρ y := by simp [update, h]

@[simp] theorem update_restore (ρ : Environment) (x a : Nat) :
    update (update ρ x a) x (ρ x) = ρ := by
  funext y
  by_cases h : y = x <;> simp [update, h]

@[simp] theorem update_self (ρ : Environment) (x : Nat) : update ρ x (ρ x) = ρ := by
  funext y
  by_cases h : y = x <;> simp [update, h]

theorem update_commute (ρ : Environment) (x y a b : Nat) (h : x ≠ y) :
    update (update ρ x a) y b = update (update ρ y b) x a := by
  funext z
  by_cases hx : z = x <;> by_cases hy : z = y <;> simp_all [update]

/-- Realization depends only on free names, including under shadowing. -/
theorem realize_agree (f : Formula) (ρ σ : Environment)
    (h : ∀ x ∈ f.freeVars, ρ x = σ x) : f.Realize ρ ↔ f.Realize σ := by
  induction f generalizing ρ σ with
  | truth => rfl
  | member a b =>
    have ha := h a (by simp [Formula.freeVars])
    have hb := h b (by simp [Formula.freeVars])
    simp only [Formula.Realize, ha, hb]
  | equal a b =>
    have ha := h a (by simp [Formula.freeVars])
    have hb := h b (by simp [Formula.freeVars])
    simp only [Formula.Realize, ha, hb]
  | imp a b ia ib =>
    exact imp_congr (ia ρ σ (fun x hx => h x (Finset.mem_union_left _ hx)))
      (ib ρ σ (fun x hx => h x (Finset.mem_union_right _ hx)))
  | all x f ih =>
    apply forall_congr'
    intro value
    apply ih
    intro y hy
    by_cases he : y = x
    · simp [update, he]
    · simp only [update, if_neg he]
      exact h y (by simpa [Formula.freeVars, he] using hy)

theorem realize_update_fresh (f : Formula) (ρ : Environment) (x a : Nat)
    (h : x ∉ f.freeVars) : f.Realize (update ρ x a) ↔ f.Realize ρ := by
  apply realize_agree
  intro y hy
  apply update_other
  intro he
  exact h (he ▸ hy)

@[simp] theorem decode_zero : decode 0 = .truth := by rw [decode]; rfl

theorem decode_member (a b : Nat) : decode (member a b) = .member a b := by
  rw [decode]
  simp [member, Nat.add_mod, Nat.mul_add_div]

theorem decode_equal (a b : Nat) : decode (equal a b) = .equal a b := by
  rw [decode]
  simp [equal, Nat.add_mod, Nat.mul_add_div]

theorem decode_all (a b : Nat) : decode (allCode a b) = .all a (decode b) := by
  rw [decode]
  simp [allCode, Nat.add_mod, Nat.mul_add_div]

theorem decode_imp (a b : Nat) (h : imp a b ≠ 0) :
    decode (imp a b) = .imp (decode a) (decode b) := by
  rw [decode]
  simp only [if_neg h]
  simp [imp]

@[simp] theorem imp_eq_zero (a b : Nat) : imp a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    have hp : pair a b = 0 := by unfold imp at h; omega
    have hh := congrArg unpair hp
    simpa only [unpair_pair, CompactProof.unpair_zero, Prod.mk.injEq] using hh
  · rintro ⟨rfl,rfl⟩
    rfl

@[simp] theorem realize_zero (ρ : Environment) : (decode 0).Realize ρ := by
  rw [decode_zero]
  trivial

@[simp] theorem realize_one (ρ : Environment) : ¬ (decode 1).Realize ρ := by
  have h : decode 1 = .member 0 0 := decode_member 0 0
  rw [h]
  simp [Formula.Realize]

/-- Code zero is the collision of implication of truth by truth. Its
realization still has the ordinary implication meaning. -/
@[simp] theorem realize_imp (a b : Nat) (ρ : Environment) :
    (decode (imp a b)).Realize ρ ↔ ((decode a).Realize ρ → (decode b).Realize ρ) := by
  by_cases h : imp a b = 0
  · obtain ⟨rfl,rfl⟩ := (imp_eq_zero a b).mp h
    simp [h, Formula.Realize]
  · rw [decode_imp a b h]
    rfl

@[simp] theorem realize_member (a b : Nat) (ρ : Environment) :
    (decode (member a b)).Realize ρ ↔ bit (ρ a) (ρ b) = true := by
  rw [decode_member]
  rfl

@[simp] theorem realize_equal (a b : Nat) (ρ : Environment) :
    (decode (equal a b)).Realize ρ ↔ ρ a = ρ b := by
  rw [decode_equal]
  rfl

@[simp] theorem realize_all (a b : Nat) (ρ : Environment) :
    (decode (allCode a b)).Realize ρ ↔ ∀ x, (decode b).Realize (update ρ a x) := by
  rw [decode_all]
  rfl

@[simp] theorem realize_neg (a : Nat) (ρ : Environment) :
    (decode (neg a)).Realize ρ ↔ ¬ (decode a).Realize ρ := by simp [neg]

@[simp] theorem realize_exists (a b : Nat) (ρ : Environment) :
    (decode (existsCode a b)).Realize ρ ↔ ∃ x, (decode b).Realize (update ρ a x) := by
  classical
  simp [existsCode, Classical.not_forall]

@[simp] theorem realize_both (a b : Nat) (ρ : Environment) :
    (decode (both a b)).Realize ρ ↔ (decode a).Realize ρ ∧ (decode b).Realize ρ := by
  classical
  simp [both]

/-- Every name in a decoded formula, including every binder, is strictly
smaller than the formula's code. The code itself is therefore a fresh name. -/
theorem vars_decode_lt (code x : Nat) (hx : x ∈ (decode code).vars) : x < code := by
  induction code using Nat.strong_induction_on generalizing x with
  | h code ih =>
    by_cases hz : code = 0
    · subst code
      simp [Formula.vars] at hx
    have ha := unpair_fst_le (code / 4)
    have hb := unpair_snd_le (code / 4)
    have hfa : (unpair (code / 4)).1 < code := by omega
    have hfb : (unpair (code / 4)).2 < code := by omega
    rw [decode, if_neg hz] at hx
    split at hx
    · simp only [Formula.vars, Finset.mem_union] at hx
      rcases hx with hx | hx
      · exact (ih _ hfa _ hx).trans hfa
      · exact (ih _ hfb _ hx).trans hfb
    · simp only [Formula.vars, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    · simp only [Formula.vars, Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · exact hfa
      · exact (ih _ hfb _ hx).trans hfb
    · simp only [Formula.vars, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption

theorem decode_self_fresh (code : Nat) : code ∉ (decode code).vars :=
  fun h => (Nat.lt_irrefl _) (vars_decode_lt code code h)

theorem decode_self_free_fresh (code : Nat) : code ∉ (decode code).freeVars :=
  fun h => decode_self_fresh code ((decode code).freeVars_subset_vars h)

theorem realize_update_code (code : Nat) (ρ : Environment) (a : Nat) :
    (decode code).Realize (update ρ code a) ↔ (decode code).Realize ρ :=
  realize_update_fresh _ _ _ _ (decode_self_free_fresh code)

/-- A finite list of natural members has its explicit binary set code. -/
def finiteSetCode : List Nat → Nat
  | [] => 0
  | x :: xs => (2^x) ||| finiteSetCode xs

theorem finiteSetCode_spec (xs : List Nat) (x : Nat) :
    bit (finiteSetCode xs) x = true ↔ x ∈ xs := by
  rw [bit_eq_testBit]
  induction xs with
  | nil => simp [finiteSetCode]
  | cons a xs ih =>
    simp only [finiteSetCode, Nat.testBit_lor, Bool.or_eq_true, Nat.testBit_two_pow,
      decide_eq_true_eq, List.mem_cons, ih]
    exact or_congr eq_comm Iff.rfl

theorem member_lt (a x : Nat) (h : bit a x = true) : x < a := by
  by_contra hn
  have hax : a ≤ x := Nat.le_of_not_gt hn
  have hp : a < 2^x := Nat.lt_two_pow_self.trans_le
    (Nat.pow_le_pow_right (by decide : 0 < 2) hax)
  rw [bit_eq_testBit, Nat.testBit_lt_two_pow hp] at h
  cases h

/-- Finite separation with an optional distinguished member, for an arbitrary
semantic property. This metatheoretic finite-set existence theorem is not an
executable truth test and is never used by the observer or matrix evaluator. -/
theorem finite_comprehension (a b : Nat) (P : Nat → Prop) :
    ∃ z : Nat, ∀ x : Nat, bit z x = true ↔ (bit a x = true ∨ x = b) ∧ P x := by
  classical
  let xs := (List.range (a+b+1)).filter (fun x => decide ((bit a x = true ∨ x = b) ∧ P x))
  refine ⟨finiteSetCode xs, ?_⟩
  intro x
  rw [finiteSetCode_spec]
  simp only [xs, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    rcases h.1 with hm | rfl
    · have := member_lt a x hm
      omega
    · omega

theorem axiom0_sound (a b : Nat) (ρ : Environment) :
    (decode (axiomCode 0 a b 0 0)).Realize ρ := by
  simp only [axiomCode, realize_exists, realize_equal]
  refine ⟨ρ b, ?_⟩
  simp [update]

theorem axiom1_sound (a b c : Nat) (ρ : Environment) :
    (decode (axiomCode 1 a b c 0)).Realize ρ := by
  simp only [axiomCode, realize_imp, realize_all]
  exact fun hi hb x => hi x (hb x)

theorem axiom2_sound (a b c : Nat) (ρ : Environment) :
    (decode (axiomCode 2 a b c 0)).Realize ρ := by
  simp only [axiomCode, realize_imp, realize_member, realize_equal]
  intro hab heq
  rw [← heq]
  exact hab

theorem axiom3_sound (a b c : Nat) (ρ : Environment) :
    (decode (axiomCode 3 a b c 0)).Realize ρ := by
  simp only [axiomCode, realize_imp, realize_all]
  by_cases he : a = b
  · subst b
    exact id
  · intro h y x
    rw [← update_commute ρ a b x y he]
    exact h x y

theorem axiom4_sound (a b c : Nat) (ρ : Environment) :
    (decode (axiomCode 4 a b c 0)).Realize ρ := by
  simp only [axiomCode, realize_imp, realize_member, realize_equal]
  intro heq hab
  rw [← heq]
  exact hab

theorem axiom5_sound (a b : Nat) (ρ : Environment) :
    (decode (axiomCode 5 a b 0 0)).Realize ρ := by
  simp only [axiomCode, realize_imp, realize_exists, realize_all]
  rintro ⟨x,hx⟩
  simpa only [update_restore] using hx (ρ a)

theorem axiom6_sound (a b c : Nat) (ρ : Environment) :
    (decode (axiomCode 6 a b c 0)).Realize ρ := by
  simp only [axiomCode, realize_imp, realize_equal]
  exact fun hab hac => hab.symm.trans hac

theorem axiom7_sound (a b c u : Nat) (ρ : Environment) :
    (decode (axiomCode 7 a b c u)).Realize ρ := by
  classical
  simp only [axiomCode, realize_imp]
  intro hca hac _
  by_contra hc
  exact hc (hac (hca (fun h => (hc h).elim)))

/-- The substantive finite-set axiom. Its formula-code parameter is also the
new set-variable name; numeric freshness, not an unstated side condition,
justifies that use. The two possible names a=b are handled explicitly. -/
theorem axiom8_sound (a b c u : Nat) (ρ : Environment) :
    (decode (axiomCode 8 a b c u)).Realize ρ := by
  classical
  by_cases hcollision : c = a ∨ c = b
  · simp [axiomCode, hcollision, Formula.Realize]
  have hca : c ≠ a := fun h => hcollision (Or.inl h)
  have hcb : c ≠ b := fun h => hcollision (Or.inr h)
  simp only [axiomCode, if_neg hcollision, realize_both, realize_exists, realize_all,
    realize_imp, realize_member, realize_equal]
  obtain ⟨z,hz⟩ := finite_comprehension (ρ a) (ρ b)
    (fun x => (decode c).Realize (update ρ b x))
  have hfresh (y : Nat) :
      (decode c).Realize (update (update ρ c z) b y) ↔
        (decode c).Realize (update ρ b y) := by
    rw [update_commute ρ c b z y hcb]
    exact realize_update_code c (update ρ b y) z
  refine ⟨⟨z, ?_, ?_⟩, ?_, ?_⟩
  · intro y
    simp only [hfresh, update_same, update_other (update ρ c z) b c y hcb]
    constructor
    · intro hmem hφ
      apply (hz y).mpr
      refine ⟨Or.inl ?_, hφ⟩
      by_cases hab : a = b
      · subst a
        simp only [update_same, bit_self_false] at hmem
        contradiction
      · simpa [update, hab, Ne.symm hca] using hmem
    · exact fun hm => ((hz y).mp hm).2
  · intro hφ
    have hφ' := (realize_update_code c ρ z).mp hφ
    have hp : (decode c).Realize (update ρ b (ρ b)) := by
      simpa only [update_self] using hφ'
    have hm := (hz (ρ b)).mpr ⟨Or.inr rfl, hp⟩
    simpa only [update_same, update_other ρ c b z (Ne.symm hcb)] using hm
  · intro heq x
    simpa [update, Ne.symm hca, Ne.symm hcb] using heq
  · intro hmem x
    simpa [update, Ne.symm hca, Ne.symm hcb] using hmem

/-- Every axiom of the literal nine-selector calculus is true in the
standard Ackermann finite-set interpretation, for every assignment. -/
theorem axiom_sound (selector : Fin 9) (a b c u : Nat) (ρ : Environment) :
    (decode (axiomCode selector a b c u)).Realize ρ := by
  rcases selector with ⟨s,hs⟩
  have h : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨
      s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [axiomCode] using axiom0_sound a b ρ
  · simpa only [axiomCode] using axiom1_sound a b c ρ
  · simpa only [axiomCode] using axiom2_sound a b c ρ
  · simpa only [axiomCode] using axiom3_sound a b c ρ
  · simpa only [axiomCode] using axiom4_sound a b c ρ
  · simpa only [axiomCode] using axiom5_sound a b ρ
  · simpa only [axiomCode] using axiom6_sound a b c ρ
  · simpa only [axiomCode] using axiom7_sound a b c u ρ
  · simpa only [axiomCode] using axiom8_sound a b c u ρ

/-- Closed standard-model soundness for the displayed compact calculus.
This is a theorem in Lean's metatheory, not a proof internal to K or PA. -/
theorem derivation_sound {f : Nat} (d : KDerivation f) (ρ : Environment) :
    (decode f).Realize ρ := by
  induction d generalizing ρ with
  | truth => exact realize_zero ρ
  | «axiom» s a b c u => exact axiom_sound s a b c u ρ
  | generalize x d ih =>
    apply (realize_all _ _ ρ).mpr
    exact fun value => ih (update ρ x value)
  | @mp a b da dab ia iab => exact (realize_imp a b ρ).mp (iab ρ) (ia ρ)

theorem proves_sound {f : Nat} (h : KProves f) (ρ : Environment) :
    (decode f).Realize ρ := by
  obtain ⟨d⟩ := h
  exact derivation_sound d ρ

theorem theoremCode_sound (code : Nat) (ρ : Environment) :
    (decode (theoremCode code)).Realize ρ := proves_sound (theorem_origin code) ρ

/-- Independent compact consistency. This corollary is not used to fabricate
an arbitrary-conclusion syntactic translation into genuine PA. -/
theorem consistent : ¬ KProves 1 := fun h => realize_one (fun _ => 0) (proves_sound h _)

end PASoundness.CompactSemantics
