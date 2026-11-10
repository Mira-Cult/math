import PASoundness.PAtoCompactFreeNames
import PASoundness.CompactFreshen

/-! Capture-safe K vacuity from syntactic free-name absence. -/
namespace PASoundness.PAtoCompactFreeVacuity

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactFormulaTranslation

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- A free name distinct from the replacement target was already free. -/
theorem replace_free_other (x y z : Nat) (f : Formula) (hzy : z ≠ y) :
    z ∈ (replace x y f).free → z ∈ f.free := by
  induction f with
  | truth | bottom => simp [replace, Formula.free]
  | member a b | equal a b =>
      simp only [replace, Formula.free, Finset.mem_insert, Finset.mem_singleton]
      intro h
      rcases h with h | h
      · left
        by_cases ha : a = x
        · subst a
          simp [rename] at h
          exact False.elim (hzy h)
        · simpa [rename, ha] using h
      · right
        by_cases hb : b = x
        · subst b
          simp [rename] at h
          exact False.elim (hzy h)
        · simpa [rename, hb] using h
  | imp a b ia ib =>
      simp only [replace, Formula.free, Finset.mem_union]
      rintro (h | h)
      · exact Or.inl (ia h)
      · exact Or.inr (ib h)
  | all w a ih | ex w a ih =>
      simp only [replace, Formula.free, Finset.mem_erase]
      rintro ⟨hne, h⟩
      exact ⟨hne, ih h⟩

/-- Replacing a name by a distinct name removes every free occurrence of the
old name, including under shadowing binders. -/
theorem replace_no_free (x y : Nat) (hxy : x ≠ y) (f : Formula) :
    x ∉ (replace x y f).free := by
  induction f with
  | truth | bottom => simp [replace, Formula.free]
  | member a b | equal a b =>
      by_cases ha : a = x <;> by_cases hb : b = x <;>
        simp [replace, Formula.free, rename, ha, hb, hxy] <;> aesop
  | imp a b ia ib => simp [replace, Formula.free, ia, ib]
  | all w a ih | ex w a ih => simp [replace, Formula.free, ih]

/-- The existing capture-safe freshener never adds a free name. -/
theorem freshen_free_subset (f : Formula) : ∀ (start : Nat)
    (hn : ∀ v ∈ f.names, v < start), (freshen f start hn).formula.free ⊆ f.free := by
  induction f with
  | truth | bottom | member | equal =>
      intro start hn
      exact Finset.Subset.refl _
  | imp a b ia ib =>
      intro start hn
      let hna : ∀ v ∈ a.names, v < start := fun v hv => hn v (Finset.mem_union_left _ hv)
      let fa := freshen a start hna
      let hnb : ∀ v ∈ b.names, v < fa.next :=
        fun v hv => (hn v (Finset.mem_union_right _ hv)).trans_le fa.next_ge
      let fb := freshen b fa.next hnb
      change (Formula.imp fa.formula fb.formula).free ⊆ (Formula.imp a b).free
      exact Finset.union_subset_union (ia start hna) (ib fa.next hnb)
  | all x a ia | ex x a ia =>
      intro start hn
      let hna : ∀ v ∈ a.names, v < start := fun v hv => hn v (Finset.mem_insert_of_mem hv)
      let fa := freshen a start hna
      have hx : x < start := hn x (Finset.mem_insert_self ..)
      have hxy : x ≠ fa.next := by have := fa.next_ge; omega
      change (Formula.all fa.next (replace x fa.next fa.formula)).free ⊆ (Formula.all x a).free
      intro z hz
      simp only [Formula.free, Finset.mem_erase] at hz ⊢
      refine ⟨?_, ?_⟩
      · intro he
        subst z
        exact replace_no_free x fa.next hxy fa.formula hz.2
      · exact ia start hna (replace_free_other x fa.next z fa.formula hz.1 hz.2)

/-- K proves vacuous universal generalization whenever the named formula
has no free occurrence of the selected name. Bound occurrences are first
freshened, with an explicit finite K proof equivalence. -/
def free_vacuity (x : Nat) (f : Formula) (hx : x ∉ f.free) :
    KDerivation (imp f.encode (allCode x f.encode)) := by
  let start := max (f.names.sup id + 1) (x + 1)
  have hn : ∀ v ∈ f.names, v < start := by
    intro v hv
    have h := Finset.le_sup (f := id) hv
    change v ≤ f.names.sup id at h
    have hm : f.names.sup id + 1 ≤ start := Nat.le_max_left _ _
    omega
  let g := freshen f start hn
  have hfree : x ∉ g.formula.free := by
    intro h
    exact hx (freshen_free_subset f start hn h)
  have hbound : x ∉ g.formula.binders := by
    intro h
    have hg := g.binders_ge x h
    have hm : x + 1 ≤ start := Nat.le_max_right _ _
    omega
  have hnames : x ∉ g.formula.names := by
    rw [Formula.names_eq_free_union_binders]
    simp [hfree, hbound]
  exact compose g.equivalent.forward
    (compose (g.formula.vacuity x hnames) (allCongr x g.equivalent.backward))

theorem free_vacuity_certificate (x : Nat) (f : Formula) (hx : x ∉ f.free) :
    theoremCode (certificate (free_vacuity x f hx)) = imp f.encode (allCode x f.encode) :=
  certificate_correct _

/-- A translated open PA formula has no free compact names outside the
source formula's free variables. -/
theorem formula_free_subset (φ : Peano.Formula) : (formula φ).free ⊆ φ.freeVarFinset := by
  have h := scopedFormula_free_subset φ Fin.elim0
  simpa [formula] using h

/-- K vacuity for the concrete PA translation, without a requirement that the
source variable avoid bound names generated internally by the translation. -/
def translated_vacuity (φ : Peano.Formula) (x : Nat) (hx : x ∉ φ.freeVarFinset) :
    KDerivation (imp (code φ) (allCode x (code φ))) :=
  free_vacuity x (formula φ) (fun h => hx (formula_free_subset φ h))

/-- The source vacuous logical leaf is derived from translated vacuity and
the same generalization bridge needed by the proof compiler. -/
def translated_vacuous_leaf (φ : Peano.Formula) (x : Nat) (hx : x ∉ φ.freeVarFinset)
    (hgen : KDerivation (imp (allCode x (code φ)) (code (FOL.allAt x φ)))) :
    KDerivation (code (φ.imp (FOL.allAt x φ))) := by
  rw [code_imp]
  exact compose (translated_vacuity φ x hx) hgen

theorem translated_vacuous_leaf_certificate (φ : Peano.Formula) (x : Nat)
    (hx : x ∉ φ.freeVarFinset)
    (hgen : KDerivation (imp (allCode x (code φ)) (code (FOL.allAt x φ)))) :
    theoremCode (certificate (translated_vacuous_leaf φ x hx hgen)) =
      code (φ.imp (FOL.allAt x φ)) := certificate_correct _

end PASoundness.PAtoCompactFreeVacuity

#print axioms PASoundness.PAtoCompactFreeVacuity.replace_free_other
#print axioms PASoundness.PAtoCompactFreeVacuity.replace_no_free
#print axioms PASoundness.PAtoCompactFreeVacuity.freshen_free_subset
#print axioms PASoundness.PAtoCompactFreeVacuity.free_vacuity
#print axioms PASoundness.PAtoCompactFreeVacuity.free_vacuity_certificate
#print axioms PASoundness.PAtoCompactFreeVacuity.formula_free_subset
#print axioms PASoundness.PAtoCompactFreeVacuity.translated_vacuity
#print axioms PASoundness.PAtoCompactFreeVacuity.translated_vacuous_leaf
#print axioms PASoundness.PAtoCompactFreeVacuity.translated_vacuous_leaf_certificate
