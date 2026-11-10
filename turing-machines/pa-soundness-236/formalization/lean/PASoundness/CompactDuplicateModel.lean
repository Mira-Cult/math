import PASoundness.PAtoCompactSuccessorInjective

/-!
A well-founded, nonextensional finite-membership model of the exact compact
calculus. Two distinct objects represent every finite member set; in particular
both 2 and 3 satisfy the current zero graph. This tests unrestricted equality
in K and does not rule out a domain-restricted or quotient interpretation.

The formula semantics and selector verification follow the proof structure in
`CompactCycleModel`, but are checked independently for this interpretation.
-/
namespace PASoundness.CompactDuplicateModel

open PASoundness.CompactProof PASoundness.CompactMatrix PASoundness.CompactSemantics
open PASoundness.PAtoCompactZeroSuccessor

/-- Containers `2 + 2*n` and `3 + 2*n` both have bitcode `n`. -/
def mem (z x : Nat) : Bool := bit ((z - 2) / 2) x

/-- Every membership edge points down in the ordinary order. -/
theorem mem_lt (z x : Nat) (h : mem z x = true) : x < z := by
  have hlt := member_lt ((z - 2) / 2) x h
  omega

theorem mem_self_false (z : Nat) : mem z z = false := by
  cases h : mem z z with
  | false => rfl
  | true =>
    have hlt := member_lt ((z-2)/2) z h
    omega

/-- The first of two distinct representatives for a finite list. -/
theorem represents_list (xs : List Nat) (x : Nat) :
    mem (2 + 2 * finiteSetCode xs) x = true ↔ x ∈ xs := by
  have h : (2 + 2 * finiteSetCode xs - 2) / 2 = finiteSetCode xs := by omega
  simpa only [mem, h] using finiteSetCode_spec xs x

/-- Every finite member set has two distinct representatives. -/
theorem represents_list_pair (xs : List Nat) :
    ∃ z₁ z₂, z₁ ≠ z₂ ∧ ∀ x,
      (mem z₁ x = true ↔ x ∈ xs) ∧ (mem z₂ x = true ↔ x ∈ xs) := by
  refine ⟨2 + 2 * finiteSetCode xs, 3 + 2 * finiteSetCode xs, by omega, ?_⟩
  intro x
  refine ⟨represents_list xs x, ?_⟩
  have h : (3 + 2 * finiteSetCode xs - 2) / 2 = finiteSetCode xs := by omega
  simpa only [mem, h] using finiteSetCode_spec xs x

/-- Finite separation holds for arbitrary predicates, with no computability
or uniformity assumption. -/

theorem finite_separation (a b : Nat) (P : Nat → Prop) :
    ∃ z, ∀ x, mem z x = true ↔ (mem a x = true ∨ x = b) ∧ P x := by
  classical
  let xs := (List.range (a + b + 1)).filter (fun x => decide ((mem a x = true ∨ x = b) ∧ P x))
  refine ⟨2 + 2 * finiteSetCode xs, ?_⟩
  intro x
  rw [represents_list]
  simp only [xs, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    rcases h.1 with hm | rfl
    · have := member_lt ((a-2)/2) x hm
      omega
    · omega

/-- Formula evaluation in the duplicate-representative structure. Equality is ordinary equality
of distinct domain elements; no extensionality principle is assumed. -/
def Realize (ρ : Environment) : Formula → Prop
  | .truth => True
  | .imp a b => Realize ρ a → Realize ρ b
  | .member a b => mem (ρ a) (ρ b) = true
  | .all x a => ∀ value, Realize (update ρ x value) a
  | .equal a b => ρ a = ρ b

theorem realize_agree (f : Formula) (ρ σ : Environment)
    (h : ∀ x ∈ f.freeVars, ρ x = σ x) : Realize ρ f ↔ Realize σ f := by
  induction f generalizing ρ σ with
  | truth | member _ _ | equal _ _ => simp_all [Realize, Formula.freeVars]
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

theorem realize_update_code (code : Nat) (ρ : Environment) (a : Nat) :
    Realize (update ρ code a) (decode code) ↔ Realize ρ (decode code) := by
  apply realize_agree
  intro y hy
  apply update_other
  intro he
  exact decode_self_free_fresh code (he ▸ hy)

@[simp] theorem realize_zero (ρ : Environment) : Realize ρ (decode 0) := by
  rw [decode_zero]; trivial

@[simp] theorem realize_one (ρ : Environment) : ¬ Realize ρ (decode 1) := by
  change ¬ Realize ρ (decode (member 0 0))
  rw [decode_member]
  simp [Realize, mem_self_false]

@[simp] theorem realize_imp (a b : Nat) (ρ : Environment) :
    Realize ρ (decode (imp a b)) ↔ (Realize ρ (decode a) → Realize ρ (decode b)) := by
  by_cases h : imp a b = 0
  · obtain ⟨rfl,rfl⟩ := (imp_eq_zero a b).mp h
    simp [h, Realize]
  · rw [decode_imp a b h]; rfl

@[simp] theorem realize_member (a b : Nat) (ρ : Environment) :
    Realize ρ (decode (member a b)) ↔ mem (ρ a) (ρ b) = true := by
  rw [decode_member]; rfl

@[simp] theorem realize_equal (a b : Nat) (ρ : Environment) :
    Realize ρ (decode (equal a b)) ↔ ρ a = ρ b := by
  rw [decode_equal]; rfl

@[simp] theorem realize_all (a b : Nat) (ρ : Environment) :
    Realize ρ (decode (allCode a b)) ↔ ∀ x, Realize (update ρ a x) (decode b) := by
  rw [decode_all]; rfl

@[simp] theorem realize_neg (a : Nat) (ρ : Environment) :
    Realize ρ (decode (neg a)) ↔ ¬ Realize ρ (decode a) := by
  unfold neg
  rw [realize_imp]
  constructor
  · intro h ha; exact realize_one ρ (h ha)
  · intro h ha; exact False.elim (h ha)

@[simp] theorem realize_exists (a b : Nat) (ρ : Environment) :
    Realize ρ (decode (existsCode a b)) ↔ ∃ x, Realize (update ρ a x) (decode b) := by
  classical
  simp only [existsCode, realize_neg, realize_all, Classical.not_forall, not_not]

@[simp] theorem realize_both (a b : Nat) (ρ : Environment) :
    Realize ρ (decode (both a b)) ↔ Realize ρ (decode a) ∧ Realize ρ (decode b) := by
  classical
  simp only [both, realize_neg, realize_imp]
  tauto

theorem axiom0_sound (a b : Nat) (ρ : Environment) :
    Realize ρ (decode (axiomCode 0 a b 0 0)) := by
  simp only [axiomCode, realize_exists, realize_equal]
  refine ⟨ρ b, ?_⟩
  simp [update]

theorem axiom1_sound (a b c : Nat) (ρ : Environment) :
    Realize ρ (decode (axiomCode 1 a b c 0)) := by
  simp only [axiomCode, realize_imp, realize_all]
  exact fun hi hb x => hi x (hb x)

theorem axiom2_sound (a b c : Nat) (ρ : Environment) :
    Realize ρ (decode (axiomCode 2 a b c 0)) := by
  simp only [axiomCode, realize_imp, realize_member, realize_equal]
  intro hab heq
  rw [← heq]
  exact hab

theorem axiom3_sound (a b c : Nat) (ρ : Environment) :
    Realize ρ (decode (axiomCode 3 a b c 0)) := by
  simp only [axiomCode, realize_imp, realize_all]
  by_cases he : a = b
  · subst b; exact id
  · intro h y x
    rw [← update_commute ρ a b x y he]
    exact h x y

theorem axiom4_sound (a b c : Nat) (ρ : Environment) :
    Realize ρ (decode (axiomCode 4 a b c 0)) := by
  simp only [axiomCode, realize_imp, realize_member, realize_equal]
  intro heq hab
  rw [← heq]
  exact hab

theorem axiom5_sound (a b : Nat) (ρ : Environment) :
    Realize ρ (decode (axiomCode 5 a b 0 0)) := by
  simp only [axiomCode, realize_imp, realize_exists, realize_all]
  rintro ⟨x,hx⟩
  simpa only [update_restore] using hx (ρ a)

theorem axiom6_sound (a b c : Nat) (ρ : Environment) :
    Realize ρ (decode (axiomCode 6 a b c 0)) := by
  simp only [axiomCode, realize_imp, realize_equal]
  exact fun hab hac => hab.symm.trans hac

theorem axiom7_sound (a b c u : Nat) (ρ : Environment) :
    Realize ρ (decode (axiomCode 7 a b c u)) := by
  classical
  simp only [axiomCode, realize_imp]
  intro hca hac _
  by_contra hc
  exact hc (hac (hca (fun h => (hc h).elim)))

/-- Every literal instance of selector 8 holds, including name collisions.
The separating witness is chosen from the explicitly finite member set. -/
theorem axiom8_sound (a b c u : Nat) (ρ : Environment) :
    Realize ρ (decode (axiomCode 8 a b c u)) := by
  classical
  by_cases hcollision : c = a ∨ c = b
  · simp [axiomCode, hcollision, Realize]
  have hca : c ≠ a := fun h => hcollision (Or.inl h)
  have hcb : c ≠ b := fun h => hcollision (Or.inr h)
  simp only [axiomCode, if_neg hcollision, realize_both, realize_exists, realize_all,
    realize_imp, realize_member, realize_equal]
  obtain ⟨z,hz⟩ := finite_separation (ρ a) (ρ b)
    (fun x => Realize (update ρ b x) (decode c))
  have hfresh (y : Nat) :
      Realize (update (update ρ c z) b y) (decode c) ↔
        Realize (update ρ b y) (decode c) := by
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
        simp only [update_same, mem_self_false] at hmem
        contradiction
      · simpa [update, hab, Ne.symm hca] using hmem
    · exact fun hm => ((hz y).mp hm).2
  · intro hφ
    have hφ' := (realize_update_code c ρ z).mp hφ
    have hp : Realize (update ρ b (ρ b)) (decode c) := by
      simpa only [update_self] using hφ'
    have hm := (hz (ρ b)).mpr ⟨Or.inr rfl, hp⟩
    simpa only [update_same, update_other ρ c b z (Ne.symm hcb)] using hm
  · intro heq x
    simpa [update, Ne.symm hca, Ne.symm hcb] using heq
  · intro hmem x
    simpa [update, Ne.symm hca, Ne.symm hcb] using hmem

theorem axiom_sound (selector : Fin 9) (a b c u : Nat) (ρ : Environment) :
    Realize ρ (decode (axiomCode selector a b c u)) := by
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

/-- Every actual compact proof tree is valid under the duplicate-representative interpretation. -/
theorem derivation_sound {f : Nat} (d : KDerivation f) (ρ : Environment) :
    Realize ρ (decode f) := by
  induction d generalizing ρ with
  | truth => exact realize_zero ρ
  | «axiom» s a b c u => exact axiom_sound s a b c u ρ
  | generalize x d ih =>
    apply (realize_all _ _ ρ).mpr
    exact fun value => ih (update ρ x value)
  | @mp a b da dab ia iab => exact (realize_imp a b ρ).mp (iab ρ) (ia ρ)


def zeroAssignment (x : Nat) : Nat := if x = 1 then 2 else if x = 2 then 3 else 0

theorem empty_two (x : Nat) : mem 2 x = false := by
  simp [mem, bit_eq_testBit]

theorem empty_three (x : Nat) : mem 3 x = false := by
  simp [mem, bit_eq_testBit]

/-- Equal immediate member sets do not form a membership congruence in this
model: 2 and 3 are both empty, but container 10 distinguishes them. -/
theorem same_members_not_congruent :
    (∀ x, mem 2 x = mem 3 x) ∧ mem 10 2 = true ∧ mem 10 3 = false := by
  refine ⟨?_, ?_, ?_⟩
  · intro x
    simp [empty_two, empty_three]
  · decide
  · decide

theorem zeroCode_realize (z w : Nat) (ρ : Environment) (hw : z ≠ w) :
    Realize ρ (decode (zeroCode z w)) ↔ ∀ x, mem (ρ z) x = false := by
  simp only [zeroCode, realize_all, realize_neg, realize_member, update_other ρ w z _ hw, update_same]
  simp only [Bool.not_eq_true]

/-- Two unequal empty objects satisfy both zero graphs. -/
theorem zero_uniqueness_fails :
    ¬ Realize zeroAssignment (decode
      (imp (zeroCode 1 3) (imp (zeroCode 2 3) (equal 1 2)))) := by
  rw [realize_imp, realize_imp, realize_equal]
  intro h
  have h₁ : Realize zeroAssignment (decode (zeroCode 1 3)) := by
    apply (zeroCode_realize 1 3 zeroAssignment (by decide)).mpr
    simpa [zeroAssignment] using empty_two
  have h₂ : Realize zeroAssignment (decode (zeroCode 2 3)) := by
    apply (zeroCode_realize 2 3 zeroAssignment (by decide)).mpr
    simpa [zeroAssignment] using empty_three
  have hne := h h₁ h₂
  simp [zeroAssignment] at hne

/-- The stated unrelativized zero-uniqueness formula has no K derivation.
This does not exclude a domain-restricted or quotient interpretation of PA. -/
theorem zero_uniqueness_not_provable :
    ¬ KProves (imp (zeroCode 1 3) (imp (zeroCode 2 3) (equal 1 2))) := by
  rintro ⟨d⟩
  exact zero_uniqueness_fails (derivation_sound d zeroAssignment)

end PASoundness.CompactDuplicateModel
