import PASoundness.PAtoCompactSuccessorInjective

/-!
An extensional finite-membership structure with a two-cycle. Its purpose is
to test derivability in the exact compact calculus, not to replace the standard
hereditarily finite interpretation or to rule out domain-restricted arithmetic
interpretations. All validity claims below use the literal nine selectors.
-/
namespace PASoundness.CompactCycleModel

open PASoundness.CompactProof PASoundness.CompactMatrix PASoundness.CompactSemantics
open PASoundness.PAtoCompactZeroSuccessor

/-- Swap the empty code and the singleton-of-one code. -/
def perm (n : Nat) : Nat := if n = 0 then 2 else if n = 2 then 0 else n

theorem perm_involution (n : Nat) : perm (perm n) = n := by
  by_cases h0 : n = 0
  · subst n; decide
  by_cases h2 : n = 2
  · subst n; decide
  simp [perm, h0, h2]

/-- The permutation gives extensional finite-member sets, including a
two-cycle between 0 and 1. -/
def mem (z x : Nat) : Bool := bit (perm z) x

theorem mem_self_false (z : Nat) : mem z z = false := by
  by_cases h0 : z = 0
  · subst z; decide
  by_cases h2 : z = 2
  · subst z; decide
  simp [mem, perm, h0, h2]

/-- Every finite list of members has a container, even when its members are the
exceptional cycle nodes. -/
theorem represents_list (xs : List Nat) (x : Nat) :
    mem (perm (finiteSetCode xs)) x = true ↔ x ∈ xs := by
  simpa [mem, perm_involution] using finiteSetCode_spec xs x

theorem finite_separation (a b : Nat) (P : Nat → Prop) :
    ∃ z, ∀ x, mem z x = true ↔ (mem a x = true ∨ x = b) ∧ P x := by
  classical
  let xs := (List.range (perm a + b + 1)).filter (fun x => decide ((mem a x = true ∨ x = b) ∧ P x))
  refine ⟨perm (finiteSetCode xs), ?_⟩
  intro x
  rw [represents_list]
  simp only [xs, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    rcases h.1 with hm | rfl
    · have := member_lt (perm a) x hm
      omega
    · omega

/-- Formula evaluation in the cyclic structure. Equality is ordinary equality
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

/-- Every actual compact proof tree is valid under the cyclic interpretation. -/
theorem derivation_sound {f : Nat} (d : KDerivation f) (ρ : Environment) :
    Realize ρ (decode f) := by
  induction d generalizing ρ with
  | truth => exact realize_zero ρ
  | «axiom» s a b c u => exact axiom_sound s a b c u ρ
  | generalize x d ih =>
    apply (realize_all _ _ ρ).mpr
    exact fun value => ih (update ρ x value)
  | @mp a b da dab ia iab => exact (realize_imp a b ρ).mp (iab ρ) (ia ρ)

/-- The model is extensional even though its membership relation has a cycle. -/
theorem extensionality (a b : Nat) (h : ∀ x, mem a x = true ↔ mem b x = true) : a = b := by
  have hp : perm a = perm b := by
    apply Nat.eq_of_testBit_eq
    intro i
    have hi := h i
    simp only [mem, bit_eq_testBit] at hi
    cases ha : (perm a).testBit i <;> cases hb : (perm b).testBit i <;> simp_all
  calc
    a = perm (perm a) := (perm_involution a).symm
    _ = perm (perm b) := congrArg perm hp
    _ = b := perm_involution b

/-- Distinct points 0 and 1 form a membership cycle, while 2 is empty. -/
theorem mutual_cycle : mem 0 1 = true ∧ mem 1 0 = true := by decide

theorem empty_set (x : Nat) : mem 2 x = false := by
  simp [mem, perm, bit_eq_testBit]

/-- A concrete closed refutation of the unrestricted no-two-cycle candidate.
Names 1 and 2 denote the two cycle points; name 0 denotes the empty set. -/
def cycleAssignment (x : Nat) : Nat := if x = 1 then 0 else if x = 2 then 1 else 2

theorem no_two_cycle_fails :
    ¬ Realize cycleAssignment (decode (imp (member 2 1) (neg (member 1 2)))) := by
  rw [realize_imp, realize_neg, realize_member, realize_member]
  simp [cycleAssignment, mem, perm, bit]

/-- The exact raw K calculus cannot prove the unrestricted no-two-cycle
candidate. This does not preclude a domain-restricted arithmetic interpretation. -/
theorem no_two_cycle_not_provable :
    ¬ KProves (imp (member 2 1) (neg (member 1 2))) := by
  rintro ⟨d⟩
  exact no_two_cycle_fails (derivation_sound d cycleAssignment)

/-- The cycle points have the same finite-set successor, namely container 3. -/
theorem common_successor :
    (∀ x, mem 3 x = true ↔ x = 0 ∨ mem 0 x = true) ∧
      (∀ x, mem 3 x = true ↔ x = 1 ∨ mem 1 x = true) := by
  have hcode : perm (finiteSetCode [0, 1]) = 3 := by decide
  have h (x : Nat) : mem 3 x = true ↔ x = 0 ∨ x = 1 := by
    have hr := represents_list [0, 1] x
    rw [hcode] at hr
    simpa using hr
  have h01 (x : Nat) : mem 0 x = true ↔ x = 1 := by
    have hr := represents_list [1] x
    have hc : perm (finiteSetCode [1]) = 0 := by decide
    rw [hc] at hr
    simpa using hr
  have h10 (x : Nat) : mem 1 x = true ↔ x = 0 := by
    have hr := represents_list [0] x
    have hc : perm (finiteSetCode [0]) = 1 := by decide
    rw [hc] at hr
    simpa using hr
  constructor <;> intro x <;> simpa [h01, h10, or_comm] using h x

theorem successorCode_realize (x y w : Nat) (ρ : Environment)
    (hx : x ≠ w) (hy : y ≠ w) :
    Realize ρ (decode (successorCode x y w)) ↔
      ∀ v, mem (ρ y) v = true ↔ v = ρ x ∨ mem (ρ x) v = true := by
  simp only [successorCode, realize_all, realize_both, realize_imp,
    PASoundness.CompactDerivations.either, realize_neg, realize_equal, realize_member]
  simp only [update_other ρ w x _ hx, update_other ρ w y _ hy, update_same]
  classical
  constructor <;> intro h v <;> specialize h v <;> tauto

def successorAssignment (x : Nat) : Nat :=
  if x = 1 then 0 else if x = 2 then 1 else if x = 3 ∨ x = 4 then 3 else 2

/-- Even with extensionality and false compact falsum, the two explicit
successor graphs can share an output for unequal inputs. -/
theorem successor_injectivity_fails :
    ¬ Realize successorAssignment (decode
      (imp (successorCode 1 3 5)
        (imp (successorCode 2 4 5) (imp (equal 3 4) (equal 1 2))))) := by
  rw [realize_imp, realize_imp, realize_imp, realize_equal, realize_equal]
  intro h
  have h₁ : Realize successorAssignment (decode (successorCode 1 3 5)) := by
    apply (successorCode_realize 1 3 5 successorAssignment (by decide) (by decide)).mpr
    simpa [successorAssignment] using common_successor.1
  have h₂ : Realize successorAssignment (decode (successorCode 2 4 5)) := by
    apply (successorCode_realize 2 4 5 successorAssignment (by decide) (by decide)).mpr
    simpa [successorAssignment] using common_successor.2
  have h₃ : successorAssignment 3 = successorAssignment 4 := by decide
  have h₄ := h h₁ h₂ h₃
  simp [successorAssignment] at h₄

theorem successor_injectivity_not_provable :
    ¬ KProves (imp (successorCode 1 3 5)
      (imp (successorCode 2 4 5) (imp (equal 3 4) (equal 1 2)))) := by
  rintro ⟨d⟩
  exact successor_injectivity_fails (derivation_sound d successorAssignment)

end PASoundness.CompactCycleModel
