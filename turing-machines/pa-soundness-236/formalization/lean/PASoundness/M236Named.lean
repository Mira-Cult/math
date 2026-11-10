import PASoundness.M236Positional
import PASoundness.CompactSemantics
import Mathlib.Data.Finset.Lattice.Fold

/-!
Capture-aware translation from the existing named compact formula syntax to
four-tag positional syntax. This is standard-truth preservation, not a
transport of finite derivations or an equivalence of PA and K proofs.
-/
namespace PASoundness.M236Named

open PASoundness.CompactMatrix PASoundness.M236Positional
open PASoundness.M236Definitions

/-- Nearest active binder wins. An unbound name uses its supplied free slot. -/
def index (free : Nat → Nat) : List Nat → Nat → Nat
  | [], x => free x
  | binder :: rest, x => if x = binder then 0 else index free rest x + 1

def Rel (names : Finset Nat) (free : Nat → Nat) (scope env : List Nat)
    (ρ : Environment) : Prop :=
  ∀ x ∈ names, env.getD (index free scope x) 0 = ρ x

theorem rel_mono {names larger : Finset Nat} {free : Nat → Nat}
    {scope env : List Nat} {ρ : Environment}
    (h : Rel larger free scope env ρ) (hs : names ⊆ larger) : Rel names free scope env ρ := by
  intro x hx
  exact h x (hs hx)

/-- Prepending a bound value agrees with named assignment update, including
repeated binder names and shadowing. -/
theorem rel_bind {names : Finset Nat} {free : Nat → Nat} {scope env : List Nat}
    {ρ : Environment} (h : Rel names free scope env ρ) (x v : Nat) :
    Rel names free (x :: scope) (v :: env) (update ρ x v) := by
  intro y hy
  by_cases hxy : y = x
  · subst y
    simp [index, update]
  · simpa [index, update, hxy] using h y hy

def toFour : Formula → List Nat → (Nat → Nat) → Nat
  | .truth, _, _ => 0
  | .imp a b, scope, free => imp4 (toFour a scope free) (toFour b scope free)
  | .member a b, scope, free => member4 (index free scope a) (index free scope b)
  | .equal a b, scope, free => equal4 (index free scope a) (index free scope b)
  | .all x a, scope, free => all4 (toFour a (x :: scope) free)

/-- The finite mentioned-name relation is sufficient at every binder; no
finite-domain restriction on quantified values is imposed. -/
theorem toFour_truth (f : Formula) : ∀ (scope env : List Nat) (ρ : Environment)
    (free : Nat → Nat), Rel f.vars free scope env ρ →
      (Truth4 (toFour f scope free) env ↔ f.Realize ρ) := by
  induction f with
  | truth => intro scope env ρ free h; simp [toFour, Formula.Realize]
  | member a b =>
    intro scope env ρ free h
    rw [toFour, member4_truth]
    have ha := h a (by simp [Formula.vars])
    have hb := h b (by simp [Formula.vars])
    change (env.getD (index free scope a) 0).testBit (env.getD (index free scope b) 0) = true ↔
      bit (ρ a) (ρ b) = true
    rw [ha, hb, bit_eq_testBit]
  | equal a b =>
    intro scope env ρ free h
    rw [toFour, equal4_truth]
    have ha := h a (by simp [Formula.vars])
    have hb := h b (by simp [Formula.vars])
    change (env.getD (index free scope a) 0 = env.getD (index free scope b) 0) ↔ ρ a = ρ b
    rw [ha, hb]
  | imp a b ia ib =>
    intro scope env ρ free h
    rw [toFour, imp4_truth]
    change (Truth4 (toFour a scope free) env → Truth4 (toFour b scope free) env) ↔
      (a.Realize ρ → b.Realize ρ)
    apply imp_congr
    · apply ia scope env ρ free
      exact rel_mono h (Finset.subset_union_left)
    · apply ib scope env ρ free
      exact rel_mono h (Finset.subset_union_right)
  | all x a ih =>
    intro scope env ρ free h
    rw [toFour, all4_truth]
    change (∀ v, Truth4 (toFour a (x :: scope) free) (v :: env)) ↔
      ∀ v, a.Realize (update ρ x v)
    apply forall_congr'
    intro v
    apply ih
    apply rel_bind
    exact rel_mono h (Finset.subset_insert _ _)

/-- Materialize only the finitely many named positions that can occur in f.
The remainder of the positional environment defaults to zero. -/
def initialEnv (f : Formula) (ρ : Environment) : List Nat :=
  List.ofFn fun i : Fin (f.vars.sup id + 1) => ρ i.val

theorem initial_rel (f : Formula) (ρ : Environment) : Rel f.vars id [] (initialEnv f ρ) ρ := by
  intro x hx
  have hle : x ≤ f.vars.sup id := Finset.le_sup (f := id) hx
  have hlt : x < f.vars.sup id + 1 := by omega
  change (List.ofFn fun i : Fin (f.vars.sup id + 1) => ρ i.val).getD x 0 = ρ x
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hlt]
  rfl

/-- Every named compact formula and arbitrary assignment have a finite,
packed positional environment realizing exactly the same truth value. -/
theorem named_truth_in_positional (f : Formula) (ρ : Environment) :
    Truth4 (toFour f [] id)
      (PASoundness.M236Definitions.unpackEnv
        (PASoundness.M236Definitions.packEnv (initialEnv f ρ))) ↔ f.Realize ρ := by
  apply toFour_truth
  intro x hx
  simp only [index, id_eq]
  rw [PASoundness.M236Definitions.unpack_pack_agrees]
  exact initial_rel f ρ x hx

/-- The distinguished variable goes at position zero; every other named
parameter has its own disjoint position beginning at three. -/
def challengeSlot (b x : Nat) : Nat := if x = b then 0 else x + 3

def challengeEnv (f : Formula) (ρ : Environment) (A B : Nat) : List Nat :=
  [A, B] ++ initialEnv f ρ

/-- One fixed packed environment works for every challenge y. Its first two
entries supply the support and distinguished point independently. -/
theorem named_predicate_positional (f : Formula) (ρ : Environment) (b A B : Nat) :
    ∃ e, PASoundness.M236Game.lookup e 0 = A ∧ PASoundness.M236Game.lookup e 1 = B ∧ ∀ y,
      (Truth4 (toFour f [] (challengeSlot b)) (y :: unpackEnv e) ↔
        f.Realize (update ρ b y)) := by
  let values := challengeEnv f ρ A B
  let e := packEnv values
  have repr := pack_represented values
  refine ⟨e, ?_, ?_, ?_⟩
  · simpa [e, values, challengeEnv] using repr 0
  · simpa [e, values, challengeEnv] using repr 1
  · intro y
    apply toFour_truth
    intro x hx
    by_cases hxb : x = b
    · subst x
      simp [index, challengeSlot, update]
    · simp only [index, challengeSlot, hxb, if_false, update]
      have hidx : x + 3 = (x + 2) + 1 := by omega
      rw [hidx, List.getD_cons_succ]
      change (unpackEnv (packEnv values)).getD (x+2) 0 = ρ x
      rw [unpack_pack_agrees]
      change (initialEnv f ρ).getD x 0 = ρ x
      exact initial_rel f ρ x hx

/-- The positional family supplies the actual named predicate, uniformly in
the challenge, without assuming any finite-set comprehension theorem. -/
theorem pointed_named (h : PointedSupport4) (f : Formula) (ρ : Environment)
    (b A B : Nat) : ∃ code, ∀ y,
      (bit code y = true → f.Realize (update ρ b y)) ∧
      ((bit A y = true ∨ y = B) → f.Realize (update ρ b y) → bit code y = true) := by
  obtain ⟨e, he0, he1, he⟩ := named_predicate_positional f ρ b A B
  obtain ⟨code, hc⟩ := h (toFour f [] (challengeSlot b)) e
  refine ⟨code, fun y => ?_⟩
  rw [bit_eq_testBit]
  constructor
  · exact fun hb => (he y).mp ((hc y).1 hb)
  · intro hs hp
    apply (hc y).2
    · simpa [he0, he1, bit_eq_testBit] using hs
    · exact (he y).mpr hp

/-- The pointed game family entails the exact selector-eight formula, including
its collision guard. This is a semantic implication, not proof transport. -/
theorem pointed_axiom8 (h : PointedSupport4) (a b c u : Nat) (ρ : Environment) :
    (decode (PASoundness.CompactProof.axiomCode 8 a b c u)).Realize ρ := by
  classical
  open PASoundness.CompactSemantics PASoundness.CompactProof in
  by_cases hcollision : c = a ∨ c = b
  · simp [axiomCode, hcollision, Formula.Realize]
  have hca : c ≠ a := fun h => hcollision (Or.inl h)
  have hcb : c ≠ b := fun h => hcollision (Or.inr h)
  simp only [axiomCode, if_neg hcollision, realize_both, realize_exists, realize_all,
    realize_imp, realize_member, realize_equal]
  obtain ⟨z,hz⟩ := pointed_named h (decode c) ρ b (ρ a) (ρ b)
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
      apply (hz y).2
      · left
        by_cases hab : a = b
        · subst a
          simp only [update_same, bit_self_false] at hmem
          contradiction
        · simpa [update, hab, Ne.symm hca] using hmem
      · exact hφ
    · exact (hz y).1
  · intro hφ
    have hφ' := (realize_update_code c ρ z).mp hφ
    have hp : (decode c).Realize (update ρ b (ρ b)) := by
      simpa only [update_self] using hφ'
    have hm := (hz (ρ b)).2 (Or.inr rfl) hp
    simpa only [update_same, update_other ρ c b z (Ne.symm hcb)] using hm
  · intro heq x
    simpa [update, Ne.symm hca, Ne.symm hcb] using heq
  · intro hmem x
    simpa [update, Ne.symm hca, Ne.symm hcb] using hmem

/-- This concerns the selected mathematical source, not the physical table. -/
theorem source_accept_implies_axiom8
    (h : PASoundness.M236Observer.TraceAccept
      (PASoundness.Source.source PASoundness.M236Game.selectedValue))
    (a b c u : Nat) (ρ : Environment) :
    (decode (PASoundness.CompactProof.axiomCode 8 a b c u)).Realize ρ :=
  pointed_axiom8 (source_accept_iff_pointedSupport4.mp h) a b c u ρ

/-- The game family supplies the only nonlogical compact axiom needed by
the existing derivation semantics. The remaining axiom cases are proved
directly and do not use compact soundness or finite comprehension. -/
theorem pointed_compact_derivation_sound (h : PointedSupport4) {f : Nat}
    (d : PASoundness.CompactProof.KDerivation f) (ρ : Environment) :
    (decode f).Realize ρ := by
  open PASoundness.CompactSemantics PASoundness.CompactProof in
  induction d generalizing ρ with
  | truth => exact realize_zero ρ
  | «axiom» selector a b c u =>
    rcases selector with ⟨s, hs⟩
    have cases : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨
        s = 6 ∨ s = 7 ∨ s = 8 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [axiomCode] using axiom0_sound a b ρ
    · simpa only [axiomCode] using axiom1_sound a b c ρ
    · simpa only [axiomCode] using axiom2_sound a b c ρ
    · simpa only [axiomCode] using axiom3_sound a b c ρ
    · simpa only [axiomCode] using axiom4_sound a b c ρ
    · simpa only [axiomCode] using axiom5_sound a b ρ
    · simpa only [axiomCode] using axiom6_sound a b c ρ
    · simpa only [axiomCode] using axiom7_sound a b c u ρ
    · exact pointed_axiom8 h a b c u ρ
  | generalize x d ih =>
    apply (realize_all _ _ ρ).mpr
    exact fun value => ih (update ρ x value)
  | @mp a b da dab ia iab => exact (realize_imp a b ρ).mp (iab ρ) (ia ρ)

theorem source_accept_implies_compact_sound
    (h : PASoundness.M236Observer.TraceAccept
      (PASoundness.Source.source PASoundness.M236Game.selectedValue))
    {f : Nat} (d : PASoundness.CompactProof.KDerivation f) (ρ : Environment) :
    (decode f).Realize ρ :=
  pointed_compact_derivation_sound (source_accept_iff_pointedSupport4.mp h) d ρ

end PASoundness.M236Named
