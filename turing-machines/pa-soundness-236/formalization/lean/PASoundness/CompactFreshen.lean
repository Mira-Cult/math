import PASoundness.CompactNamedSemantics
import Mathlib.Data.Finset.Max

/-!
Constructive standardization of arbitrary compact named formulas. Every binder
is allocated a new natural label, bottom-up, above all original names. The
result carries literal bidirectional K proofs and checked scope separation.
-/
namespace PASoundness.CompactNamed

open CompactProof CompactDerivations
attribute [local irreducible] imp Cantor.pair Cantor.triangle

structure ProofEquiv (a b : Formula) where
  forward : KDerivation (imp a.encode b.encode)
  backward : KDerivation (imp b.encode a.encode)
  semantic : ∀ ρ : CompactMatrix.Environment, a.Realize ρ ↔ b.Realize ρ

namespace ProofEquiv

def refl (a : Formula) : ProofEquiv a a :=
  ⟨CompactHilbertBasis.identity a.encode, CompactHilbertBasis.identity a.encode, fun _ => Iff.rfl⟩

def symm {a b : Formula} (h : ProofEquiv a b) : ProofEquiv b a :=
  ⟨h.backward, h.forward, fun ρ => (h.semantic ρ).symm⟩

def trans {a b c : Formula} (h : ProofEquiv a b) (h' : ProofEquiv b c) : ProofEquiv a c :=
  ⟨compose h.forward h'.forward, compose h'.backward h.backward,
    fun ρ => (h.semantic ρ).trans (h'.semantic ρ)⟩

def implication {a a' b b' : Formula} (ha : ProofEquiv a a') (hb : ProofEquiv b b') :
    ProofEquiv (.imp a b) (.imp a' b') :=
  ⟨implicationCongr ha.backward hb.forward, implicationCongr ha.forward hb.backward,
    fun ρ => imp_congr (ha.semantic ρ) (hb.semantic ρ)⟩

def universal (x : Nat) {a b : Formula} (h : ProofEquiv a b) :
    ProofEquiv (.all x a) (.all x b) := ⟨allCongr x h.forward, allCongr x h.backward,
    fun ρ => forall_congr' fun v => h.semantic (CompactMatrix.update ρ x v)⟩

def existential (x : Nat) {a b : Formula} (h : ProofEquiv a b) :
    ProofEquiv (.ex x a) (.ex x b) := ⟨existsCongr x h.forward, existsCongr x h.backward,
    fun ρ => exists_congr fun v => h.semantic (CompactMatrix.update ρ x v)⟩

def alphaAll (x y : Nat) (f : Formula) (hxy : x ≠ y)
    (hx : x ∉ f.binders) (hy : y ∉ f.names) :
    ProofEquiv (.all x f) (.all y (replace x y f)) :=
  let h := universalAlpha x y f hxy hx hy
  ⟨h.1,h.2,universalAlpha_semantics x y f hx hy⟩

def alphaExists (x y : Nat) (f : Formula) (hxy : x ≠ y)
    (hx : x ∉ f.binders) (hy : y ∉ f.names) :
    ProofEquiv (.ex x f) (.ex y (replace x y f)) :=
  let h := existentialAlpha x y f hxy hx hy
  ⟨h.1,h.2,existentialAlpha_semantics x y f hx hy⟩

end ProofEquiv

theorem rename_mem (x y a : Nat) : rename x y a = y ∨ rename x y a = a := by
  by_cases h : a = x <;> simp [rename, h]

theorem replace_names_subset (x y : Nat) (f : Formula) :
    (replace x y f).names ⊆ insert y f.names := by
  induction f with
  | truth | bottom => simp [replace, Formula.names]
  | member a b | equal a b =>
    intro z hz
    simp only [replace, Formula.names, Finset.mem_insert, Finset.mem_singleton] at hz ⊢
    rcases hz with rfl | rfl
    · rcases rename_mem x y a with h | h <;> simp [h]
    · rcases rename_mem x y b with h | h <;> simp [h]
  | imp a b ia ib =>
    intro z hz
    simp only [replace, Formula.names, Finset.mem_union] at hz
    rcases hz with ha | hb
    · exact (Finset.insert_subset_insert y (Finset.subset_union_left)).trans
        (Finset.Subset.refl _) (ia ha)
    · exact (Finset.insert_subset_insert y (Finset.subset_union_right)).trans
        (Finset.Subset.refl _) (ib hb)
  | all z a ih | ex z a ih =>
    intro v hv
    simp only [replace, Formula.names, Finset.mem_insert] at hv ⊢
    rcases hv with rfl | hv
    · exact Or.inr (Or.inl rfl)
    · rcases Finset.mem_insert.mp (ih hv) with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)

theorem rename_outside (x y v a : Nat) (hx : v ≠ x) (hy : v ≠ y) :
    v = rename x y a ↔ v = a := by
  by_cases h : a = x <;> simp [rename, h, hx, hy]

theorem replace_names_outside (x y v : Nat) (f : Formula)
    (hx : v ≠ x) (hy : v ≠ y) : v ∈ (replace x y f).names ↔ v ∈ f.names := by
  induction f <;> simp_all [replace, Formula.names, rename_outside x y v _ hx hy]

/-- Scope separation allows quantifier movement without capturing a name in
another branch. Repeated input names are allowed before `freshen`. -/
def Separated : Formula → Prop
  | .truth | .bottom | .member _ _ | .equal _ _ => True
  | .imp a b => Separated a ∧ Separated b ∧
      (∀ x ∈ a.binders, x ∉ b.names) ∧ (∀ x ∈ b.binders, x ∉ a.names)
  | .all x a | .ex x a => Separated a ∧ x ∉ a.binders

theorem replace_separated (x y : Nat) (f : Formula) (h : Separated f)
    (hx : x ∉ f.binders) (hy : y ∉ f.binders) : Separated (replace x y f) := by
  induction f with
  | truth | bottom | member | equal => trivial
  | imp a b ia ib =>
    rcases h with ⟨ha,hb,hab,hba⟩
    simp only [Formula.binders, Finset.mem_union, not_or] at hx hy
    refine ⟨ia ha hx.1 hy.1, ib hb hx.2 hy.2, ?_, ?_⟩
    · intro v hv hmem
      rw [replace_binders] at hv
      exact hab v hv ((replace_names_outside x y v b
        (fun he => hx.1 (he ▸ hv)) (fun he => hy.1 (he ▸ hv))).mp hmem)
    · intro v hv hmem
      rw [replace_binders] at hv
      exact hba v hv ((replace_names_outside x y v a
        (fun he => hx.2 (he ▸ hv)) (fun he => hy.2 (he ▸ hv))).mp hmem)
  | all z a ih | ex z a ih =>
    rcases h with ⟨ha,hza⟩
    simp only [Formula.binders, Finset.mem_insert, not_or] at hx hy
    exact ⟨ih ha hx.2 hy.2, by simpa only [replace_binders] using hza⟩

structure Freshened (f : Formula) (start : Nat) where
  formula : Formula
  next : Nat
  equivalent : ProofEquiv f formula
  next_ge : start ≤ next
  names_lt : ∀ v ∈ formula.names, v < next
  old_names : ∀ v ∈ formula.names, v < start → v ∈ f.names
  binders_ge : ∀ v ∈ formula.binders, start ≤ v
  separated : Separated formula

private def unchanged (f : Formula) (start : Nat)
    (hn : ∀ v ∈ f.names, v < start) (hb : f.binders = ∅) (hs : Separated f) :
    Freshened f start :=
  ⟨f,start,.refl f,le_refl _,hn,fun _ h _ => h,
    fun v h => False.elim (by simpa [hb] using h), hs⟩

private def joinImp (a b : Formula) (start : Nat)
    (ha : Freshened a start) (hb : Freshened b ha.next)
    (hnb : ∀ v ∈ b.names, v < start) : Freshened (.imp a b) start := by
  refine ⟨.imp ha.formula hb.formula, hb.next,
    .implication ha.equivalent hb.equivalent, ha.next_ge.trans hb.next_ge,
    ?_, ?_, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (ha.names_lt v hv).trans_le hb.next_ge
    · exact hb.names_lt v hv
  · intro v hv hvs
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Finset.mem_union_left _ (ha.old_names v hv hvs)
    · exact Finset.mem_union_right _ (hb.old_names v hv (hvs.trans_le ha.next_ge))
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact ha.binders_ge v hv
    · exact ha.next_ge.trans (hb.binders_ge v hv)
  · refine ⟨ha.separated,hb.separated,?_,?_⟩
    · intro v hva hvb
      have hvlt := ha.names_lt v (ha.formula.binders_subset_names hva)
      have hvb' := hb.old_names v hvb hvlt
      have := ha.binders_ge v hva
      have := hnb v hvb'
      omega
    · intro v hvb hva
      have := hb.binders_ge v hvb
      have := ha.names_lt v hva
      omega

private def joinBinder (isEx : Bool) (x : Nat) (f : Formula) (start : Nat)
    (h : Freshened f start) (hx : x < start) :
    Freshened (if isEx then .ex x f else .all x f) start := by
  have hnxt := h.next_ge
  have hxb : x ∉ h.formula.binders := by
    intro hm
    have := h.binders_ge x hm
    omega
  have hyn : h.next ∉ h.formula.names := by
    intro hm
    have := h.names_lt h.next hm
    omega
  have hxy : x ≠ h.next := by have := h.next_ge; omega
  let renamed := replace x h.next h.formula
  have he : ProofEquiv (if isEx then .ex x f else .all x f)
      (if isEx then .ex h.next renamed else .all h.next renamed) := by
    cases isEx
    · exact (ProofEquiv.universal x h.equivalent).trans (.alphaAll x h.next h.formula hxy hxb hyn)
    · exact (ProofEquiv.existential x h.equivalent).trans (.alphaExists x h.next h.formula hxy hxb hyn)
  have hnames : (if isEx then Formula.ex h.next renamed else Formula.all h.next renamed).names =
      insert h.next renamed.names := by cases isEx <;> rfl
  have hbinders : (if isEx then Formula.ex h.next renamed else Formula.all h.next renamed).binders =
      insert h.next h.formula.binders := by
    cases isEx <;> simp [Formula.binders, renamed, replace_binders]
  refine ⟨if isEx then .ex h.next renamed else .all h.next renamed,
    h.next+1, he, by omega, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [hnames] at hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · omega
    · rcases Finset.mem_insert.mp (replace_names_subset x h.next h.formula hv) with rfl | hv
      · omega
      · exact (h.names_lt v hv).trans (Nat.lt_succ_self _)
  · intro v hv hvs
    rw [hnames] at hv
    have hvn : v ≠ h.next := by have := h.next_ge; omega
    have hv' := (Finset.mem_insert.mp hv).resolve_left hvn
    have hv'' := (Finset.mem_insert.mp (replace_names_subset x h.next h.formula hv')).resolve_left hvn
    have old := h.old_names v hv'' hvs
    cases isEx <;> exact Finset.mem_insert_of_mem old
  · intro v hv
    rw [hbinders] at hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact h.next_ge
    · exact h.binders_ge v hv
  · have hs := replace_separated x h.next h.formula h.separated hxb
      (fun hm => hyn (h.formula.binders_subset_names hm))
    have hb : h.next ∉ renamed.binders := by
      simpa only [renamed, replace_binders] using
        (show h.next ∉ h.formula.binders from fun hm => hyn (h.formula.binders_subset_names hm))
    cases isEx <;> exact ⟨hs,hb⟩

/-- Executable freshening works for arbitrary finite formulas, including
shadowed or repeated binder labels in the original input. -/
def freshen (f : Formula) (start : Nat) (hn : ∀ v ∈ f.names, v < start) :
    Freshened f start :=
  match f with
  | .truth => unchanged .truth start hn rfl trivial
  | .bottom => unchanged .bottom start hn rfl trivial
  | .member a b => unchanged (.member a b) start hn rfl trivial
  | .equal a b => unchanged (.equal a b) start hn rfl trivial
  | .imp a b =>
      let ha := freshen a start (fun v hv => hn v (Finset.mem_union_left _ hv))
      let hb := freshen b ha.next
        (fun v hv => (hn v (Finset.mem_union_right _ hv)).trans_le ha.next_ge)
      joinImp a b start ha hb (fun v hv => hn v (Finset.mem_union_right _ hv))
  | .all x a => joinBinder false x a start
      (freshen a start (fun v hv => hn v (Finset.mem_insert_of_mem hv)))
      (hn x (Finset.mem_insert_self ..))
  | .ex x a => joinBinder true x a start
      (freshen a start (fun v hv => hn v (Finset.mem_insert_of_mem hv)))
      (hn x (Finset.mem_insert_self ..))

end PASoundness.CompactNamed
