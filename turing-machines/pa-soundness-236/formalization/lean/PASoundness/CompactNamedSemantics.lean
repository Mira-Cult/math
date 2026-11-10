import PASoundness.CompactNamed
import PASoundness.CompactSemantics

/-!
Direct standard semantics for the normalization IR. Alpha conversion,
vacuity and quantifier movement are proved from assignments and finite name
sets, independently of K derivation soundness or the HF comprehension axiom.
-/
namespace PASoundness.CompactNamed

open CompactMatrix (Environment update)
open CompactSemantics (update_same update_other update_self update_commute)

namespace Formula

def Realize (ρ : Environment) : Formula → Prop
  | .truth => True
  | .bottom => False
  | .imp a b => a.Realize ρ → b.Realize ρ
  | .member a b => CompactMatrix.bit (ρ a) (ρ b) = true
  | .equal a b => ρ a = ρ b
  | .all x a => ∀ v, a.Realize (update ρ x v)
  | .ex x a => ∃ v, a.Realize (update ρ x v)

/-- The auxiliary explicit bottom/existential nodes have exactly the meaning
of their unchanged compact numeric encodings, including the code-zero alias. -/
theorem encode_realize (f : Formula) (ρ : Environment) :
    (CompactMatrix.decode f.encode).Realize ρ ↔ f.Realize ρ := by
  induction f generalizing ρ with
  | truth => rw [encode,CompactSemantics.decode_zero]; rfl
  | bottom => simp [encode,Realize]
  | member a b => exact CompactSemantics.realize_member a b ρ
  | equal a b => exact CompactSemantics.realize_equal a b ρ
  | imp a b ia ib =>
    change (CompactMatrix.decode (CompactProof.imp a.encode b.encode)).Realize ρ ↔ _
    rw [CompactSemantics.realize_imp,ia,ib]
    rfl
  | all x a ih =>
    change (CompactMatrix.decode (CompactProof.allCode x a.encode)).Realize ρ ↔ _
    rw [CompactSemantics.realize_all]
    exact forall_congr' fun v => ih (update ρ x v)
  | ex x a ih =>
    change (CompactMatrix.decode (CompactProof.existsCode x a.encode)).Realize ρ ↔ _
    rw [CompactSemantics.realize_exists]
    exact exists_congr fun v => ih (update ρ x v)

theorem realize_agree (f : Formula) (ρ σ : Environment)
    (h : ∀ v ∈ f.names, ρ v = σ v) : f.Realize ρ ↔ f.Realize σ := by
  induction f generalizing ρ σ with
  | truth | bottom => rfl
  | member a b | equal a b =>
    have ha := h a (by simp [names])
    have hb := h b (by simp [names])
    simp only [Realize,ha,hb]
  | imp a b ia ib =>
    exact imp_congr (ia ρ σ (fun v hv => h v (Finset.mem_union_left _ hv)))
      (ib ρ σ (fun v hv => h v (Finset.mem_union_right _ hv)))
  | all x a ih =>
    apply forall_congr'
    intro value
    apply ih
    intro v hv
    by_cases hve : v = x
    · simp [update,hve]
    · simp only [update,if_neg hve]
      exact h v (Finset.mem_insert_of_mem hv)
  | ex x a ih =>
    apply exists_congr
    intro value
    apply ih
    intro v hv
    by_cases hve : v = x
    · simp [update,hve]
    · simp only [update,if_neg hve]
      exact h v (Finset.mem_insert_of_mem hv)

theorem realize_update_fresh (f : Formula) (ρ : Environment) (x value : Nat)
    (hx : x ∉ f.names) : f.Realize (update ρ x value) ↔ f.Realize ρ := by
  apply realize_agree
  intro v hv
  apply update_other
  intro he
  exact hx (he ▸ hv)

end Formula

private theorem rename_lookup (x y a : Nat) (ρ : Environment) :
    ρ (rename x y a) = update ρ x (ρ y) a := by
  by_cases h : a = x <;> simp [rename,update,h]

/-- Capture-safe syntactic replacement agrees with updating the replaced
variable to the value of the replacement name. -/
theorem replace_realize (x y : Nat) (f : Formula) (hx : x ∉ f.binders)
    (hy : y ∉ f.binders) (ρ : Environment) :
    (replace x y f).Realize ρ ↔ f.Realize (update ρ x (ρ y)) := by
  induction f generalizing ρ with
  | truth | bottom => rfl
  | member a b | equal a b =>
    simp only [replace,Formula.Realize,rename_lookup]
  | imp a b ia ib =>
    simp only [Formula.binders,Finset.mem_union,not_or] at hx hy
    exact imp_congr (ia hx.1 hy.1 ρ) (ib hx.2 hy.2 ρ)
  | all z a ih =>
    simp only [Formula.binders,Finset.mem_insert,not_or] at hx hy
    change (∀ v, (replace x y a).Realize (update ρ z v)) ↔ _
    apply forall_congr'
    intro v
    rw [ih hx.2 hy.2,update_other ρ z y v hy.1,
      update_commute ρ z x v (ρ y) (Ne.symm hx.1)]
  | ex z a ih =>
    simp only [Formula.binders,Finset.mem_insert,not_or] at hx hy
    change (∃ v, (replace x y a).Realize (update ρ z v)) ↔ _
    apply exists_congr
    intro v
    rw [ih hx.2 hy.2,update_other ρ z y v hy.1,
      update_commute ρ z x v (ρ y) (Ne.symm hx.1)]

private theorem replacement_at_bound_value (x y : Nat) (f : Formula)
    (hx : x ∉ f.binders) (hy : y ∉ f.names) (ρ : Environment) (v : Nat) :
    (replace x y f).Realize (update ρ y v) ↔ f.Realize (update ρ x v) := by
  rw [replace_realize x y f hx (fun h => hy (f.binders_subset_names h)),update_same]
  apply Formula.realize_agree
  intro z hz
  have hzy : z ≠ y := fun he => hy (he ▸ hz)
  by_cases hzx : z = x
  · simp [update,hzx]
  · simp [update,hzx,hzy]

theorem universalAlpha_semantics (x y : Nat) (f : Formula)
    (hx : x ∉ f.binders) (hy : y ∉ f.names) (ρ : Environment) :
    (Formula.all x f).Realize ρ ↔ (Formula.all y (replace x y f)).Realize ρ :=
  forall_congr' fun v => (replacement_at_bound_value x y f hx hy ρ v).symm

theorem existentialAlpha_semantics (x y : Nat) (f : Formula)
    (hx : x ∉ f.binders) (hy : y ∉ f.names) (ρ : Environment) :
    (Formula.ex x f).Realize ρ ↔ (Formula.ex y (replace x y f)).Realize ρ :=
  exists_congr fun v => (replacement_at_bound_value x y f hx hy ρ v).symm

theorem vacuousAll_semantics (x : Nat) (f : Formula) (hx : x ∉ f.names)
    (ρ : Environment) : f.Realize ρ ↔ (Formula.all x f).Realize ρ := by
  constructor
  · intro h v
    exact (f.realize_update_fresh ρ x v hx).mpr h
  · intro h
    exact (f.realize_update_fresh ρ x 0 hx).mp (h 0)

theorem vacuousExists_semantics (x : Nat) (f : Formula) (hx : x ∉ f.names)
    (ρ : Environment) : f.Realize ρ ↔ (Formula.ex x f).Realize ρ := by
  constructor
  · intro h
    exact ⟨0,(f.realize_update_fresh ρ x 0 hx).mpr h⟩
  · rintro ⟨v,h⟩
    exact (f.realize_update_fresh ρ x v hx).mp h

theorem implicationAllRight_semantics (x : Nat) (a b : Formula) (hx : x ∉ a.names)
    (ρ : Environment) : (Formula.imp a (.all x b)).Realize ρ ↔
      (Formula.all x (.imp a b)).Realize ρ := by
  constructor
  · intro h v ha
    exact h ((a.realize_update_fresh ρ x v hx).mp ha) v
  · intro h ha v
    exact h v ((a.realize_update_fresh ρ x v hx).mpr ha)

theorem implicationExistsLeft_semantics (x : Nat) (a b : Formula) (hx : x ∉ b.names)
    (ρ : Environment) : (Formula.imp (.ex x a) b).Realize ρ ↔
      (Formula.all x (.imp a b)).Realize ρ := by
  constructor
  · intro h v ha
    exact (b.realize_update_fresh ρ x v hx).mpr (h ⟨v,ha⟩)
  · intro h he
    obtain ⟨v,ha⟩ := he
    exact (b.realize_update_fresh ρ x v hx).mp (h v ha)

theorem implicationAllLeft_semantics (x : Nat) (a b : Formula) (hx : x ∉ b.names)
    (ρ : Environment) : (Formula.imp (.all x a) b).Realize ρ ↔
      (Formula.ex x (.imp a b)).Realize ρ := by
  classical
  constructor
  · intro h
    by_cases hb : b.Realize ρ
    · exact ⟨0,fun _ => (b.realize_update_fresh ρ x 0 hx).mpr hb⟩
    · have hn : ¬ ∀ v, a.Realize (update ρ x v) := fun ha => hb (h ha)
      obtain ⟨v,hv⟩ := not_forall.mp hn
      exact ⟨v,fun ha => False.elim (hv ha)⟩
  · rintro ⟨v,hv⟩ ha
    exact (b.realize_update_fresh ρ x v hx).mp (hv (ha v))

theorem implicationExistsRight_semantics (x : Nat) (a b : Formula) (hx : x ∉ a.names)
    (ρ : Environment) : (Formula.imp a (.ex x b)).Realize ρ ↔
      (Formula.ex x (.imp a b)).Realize ρ := by
  classical
  constructor
  · intro h
    by_cases ha : a.Realize ρ
    · obtain ⟨v,hv⟩ := h ha
      exact ⟨v,fun _ => hv⟩
    · exact ⟨0,fun hv => False.elim (ha ((a.realize_update_fresh ρ x 0 hx).mp hv))⟩
  · rintro ⟨v,hv⟩ ha
    exact ⟨v,hv ((a.realize_update_fresh ρ x v hx).mpr ha)⟩

end PASoundness.CompactNamed
