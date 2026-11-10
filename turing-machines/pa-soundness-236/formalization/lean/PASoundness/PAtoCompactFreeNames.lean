import PASoundness.PAtoCompactTermTranslation
import PASoundness.PAtoCompactEqualityGraphTruth

/-! Syntactic free-name bounds for the concrete relational term translation.
These results are not K proof transformations or semantic soundness claims. -/
namespace PASoundness.PAtoCompactFreeNames

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactEqualityGraphTruth

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Renaming can capture a free occurrence when the map is not injective,
but it cannot create a free name outside the image of the original free
names. -/
theorem mapNames_free_subset (f : Nat → Nat) (a : Formula) :
    (mapNames f a).free ⊆ a.free.image f := by
  induction a with
  | truth | bottom | member | equal => simp [mapNames, Formula.free]
  | imp a b ia ib =>
      simpa [mapNames, Formula.free, Finset.image_union] using
        Finset.union_subset_union ia ib
  | all x a ih | ex x a ih =>
      intro z hz
      simp only [mapNames, Formula.free, Finset.mem_erase] at hz
      obtain ⟨w, hw, he⟩ := Finset.mem_image.mp (ih hz.2)
      apply Finset.mem_image.mpr
      refine ⟨w, Finset.mem_erase.mpr ⟨?_, hw⟩, he⟩
      intro e
      subst w
      exact hz.1 he.symm

/-- The free names of a generated conjunction are the union of those of its
two arguments. -/
theorem andF_free (a b : Formula) : (andF a b).free = a.free ∪ b.free := by
  simp [andF, CompactNamed.Formula.not, Formula.free]

theorem domainAt_free (base x : Nat) : (domainAt base x).free ⊆ {x} := by
  unfold domainAt
  refine (mapNames_free_subset _ _).trans ?_
  apply Finset.image_subset_iff.mpr
  intro a ha
  have h := templates_free_names.1 ha
  have : a = 0 := by simpa using h
  subst a
  simp [oneMap]

theorem equivAt_free (base x y : Nat) : (equivAt base x y).free ⊆ {x,y} := by
  unfold equivAt
  refine (mapNames_free_subset _ _).trans ?_
  apply Finset.image_subset_iff.mpr
  intro a ha
  have h := templates_free_names.2.1 ha
  have : a = 0 ∨ a = 1 := by simpa using h
  rcases this with rfl | rfl <;> simp [twoMap]

theorem zeroAt_free (base x : Nat) : (zeroAt base x).free ⊆ {x} := by
  unfold zeroAt
  refine (mapNames_free_subset _ _).trans ?_
  apply Finset.image_subset_iff.mpr
  intro a ha
  have h := templates_free_names.2.2.1 ha
  have : a = 0 := by simpa using h
  subst a
  simp [oneMap]

theorem succAt_free (base x y : Nat) : (succAt base x y).free ⊆ {x,y} := by
  unfold succAt
  refine (mapNames_free_subset _ _).trans ?_
  apply Finset.image_subset_iff.mpr
  intro a ha
  have h := templates_free_names.2.2.2.1 ha
  have : a = 0 ∨ a = 1 := by simpa using h
  rcases this with rfl | rfl <;> simp [twoMap]

theorem addAt_free (base x y z : Nat) : (addAt base x y z).free ⊆ {x,y,z} := by
  unfold addAt
  refine (mapNames_free_subset _ _).trans ?_
  apply Finset.image_subset_iff.mpr
  intro a ha
  have h := templates_free_names.2.2.2.2.1 ha
  have : a = 30 ∨ a = 31 ∨ a = 32 := by simpa using h
  rcases this with rfl | rfl | rfl <;> simp [threeMap]

theorem mulAt_free (base x y z : Nat) : (mulAt base x y z).free ⊆ {x,y,z} := by
  unfold mulAt
  refine (mapNames_free_subset _ _).trans ?_
  apply Finset.image_subset_iff.mpr
  intro a ha
  have h := templates_free_names.2.2.2.2.2 ha
  have : a = 0 ∨ a = 1 ∨ a = 2 := by simpa using h
  rcases this with rfl | rfl | rfl <;> simp [threeMap]

/-- The only free names in a generated term graph are its output and the
images of source variables actually occurring in the term. -/
theorem termGraph_free_subset {α : Type} [DecidableEq α] (varName : α → Nat)
    (t : Peano.language.Term α) : ∀ out base,
    (termGraph varName t out base).free ⊆ t.varFinset.image varName ∪ {out} := by
  induction t with
  | var a =>
      intro out base z hz
      simp only [termGraph, andF_free, Finset.mem_union] at hz
      rcases hz with hd | he
      · have h := domainAt_free base out hd
        exact Finset.mem_union_right _ h
      · have h := equivAt_free base (varName a) out he
        simpa [FirstOrder.Language.Term.varFinset] using h
  | @func l f ts ih =>
      have hchild (i : Fin l) : (ts i).varFinset.image varName ⊆
          (FirstOrder.Language.Term.func f ts).varFinset.image varName := by
        intro z hz
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
        apply Finset.mem_image.mpr
        refine ⟨a, ?_, rfl⟩
        simp only [FirstOrder.Language.Term.varFinset, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        exact ⟨i, ha⟩
      cases f with
      | zero =>
          intro out base z hz
          simp only [termGraph, andF_free, Finset.mem_union] at hz
          rcases hz with hd | he
          · have h := domainAt_free base out hd
            exact Finset.mem_union_right _ h
          · have h := zeroAt_free base out he
            exact Finset.mem_union_right _ h
      | succ =>
          intro out base z hz
          simp only [termGraph, andF_free, Formula.free, Finset.mem_union,
            Finset.mem_erase] at hz
          rcases hz with hd | ⟨hne, hc | hr⟩
          · exact Finset.mem_union_right _ (domainAt_free base out hd)
          · rcases Finset.mem_union.mp (ih 0 base (base + 64) hc) with h | h
            · exact Finset.mem_union_left _ (hchild 0 h)
            · exact False.elim (hne (Finset.mem_singleton.mp h))
          · have h := succAt_free base base out hr
            simp only [Finset.mem_insert, Finset.mem_singleton] at h
            rcases h with h | h
            · exact False.elim (hne h)
            · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr h)
      | add =>
          intro out base z hz
          simp only [termGraph, andF_free, Formula.free, Finset.mem_union,
            Finset.mem_erase] at hz
          rcases hz with hd | ⟨hn0, hn1, hc | hc | hr⟩
          · exact Finset.mem_union_right _ (domainAt_free base out hd)
          · rcases Finset.mem_union.mp (ih 0 base (base + 64) hc) with h | h
            · exact Finset.mem_union_left _ (hchild 0 h)
            · exact False.elim (hn0 (Finset.mem_singleton.mp h))
          · rcases Finset.mem_union.mp (ih 1 (base + 1) (base + 64 + termCost (ts 0)) hc) with h | h
            · exact Finset.mem_union_left _ (hchild 1 h)
            · exact False.elim (hn1 (Finset.mem_singleton.mp h))
          · have h := addAt_free base base (base + 1) out hr
            simp only [Finset.mem_insert, Finset.mem_singleton] at h
            rcases h with h | h | h
            · exact False.elim (hn0 h)
            · exact False.elim (hn1 h)
            · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr h)
      | mul =>
          intro out base z hz
          simp only [termGraph, andF_free, Formula.free, Finset.mem_union,
            Finset.mem_erase] at hz
          rcases hz with hd | ⟨hn0, hn1, hc | hc | hr⟩
          · exact Finset.mem_union_right _ (domainAt_free base out hd)
          · rcases Finset.mem_union.mp (ih 0 base (base + 64) hc) with h | h
            · exact Finset.mem_union_left _ (hchild 0 h)
            · exact False.elim (hn0 (Finset.mem_singleton.mp h))
          · rcases Finset.mem_union.mp (ih 1 (base + 1) (base + 64 + termCost (ts 0)) hc) with h | h
            · exact Finset.mem_union_left _ (hchild 1 h)
            · exact False.elim (hn1 (Finset.mem_singleton.mp h))
          · have h := mulAt_free base base (base + 1) out hr
            simp only [Finset.mem_insert, Finset.mem_singleton] at h
            rcases h with h | h | h
            · exact False.elim (hn0 h)
            · exact False.elim (hn1 h)
            · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr h)

/-- Source term variables map only to the formula's free names or to the
currently active bound-name image. -/
theorem term_image_subset {n : Nat} (t : Peano.language.Term (Nat ⊕ Fin n))
    (φ : Peano.language.BoundedFormula Nat n) (bound : Fin n → Nat)
    (hleft : t.varFinsetLeft ⊆ φ.freeVarFinset) :
    t.varFinset.image (Sum.elim id bound) ⊆ φ.freeVarFinset ∪ Finset.univ.image bound := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
  cases a with
  | inl x =>
      exact Finset.mem_union_left _ (hleft (inl_mem_left t x ha))
  | inr i =>
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- The generated scoped formula has no free names beyond source free
variables and the names assigned to active bound levels. -/
theorem scopedFormula_free_subset {n : Nat} (φ : Peano.language.BoundedFormula Nat n) :
    ∀ bound : Fin n → Nat,
      (scopedFormula n φ bound).free ⊆ φ.freeVarFinset ∪ Finset.univ.image bound := by
  induction φ with
  | falsum =>
      intro bound z hz
      simp [scopedFormula, Formula.free] at hz
  | @equal n t u =>
      intro bound z hz
      let source : Peano.language.BoundedFormula Nat n := .equal t u
      let base := scopeBase source bound
      change z ∈ (CompactNamed.Formula.ex base (.ex (base + 1)
        (andF (termGraph (Sum.elim id bound) t base (base + 2))
          (andF (termGraph (Sum.elim id bound) u (base + 1) (base + 2 + termCost t))
            (equivAt (base + 2 + termCost t + termCost u) base (base + 1)))))).free at hz
      simp only [Formula.free, Finset.mem_erase, andF_free, Finset.mem_union] at hz
      rcases hz with ⟨hn0, hn1, ht | hu | he⟩
      · rcases Finset.mem_union.mp (termGraph_free_subset (Sum.elim id bound) t base (base + 2) ht) with h | h
        · exact term_image_subset t source bound (by intro y hy; exact Finset.mem_union_left _ hy) h
        · exact False.elim (hn0 (Finset.mem_singleton.mp h))
      · rcases Finset.mem_union.mp (termGraph_free_subset (Sum.elim id bound) u (base + 1) (base + 2 + termCost t) hu) with h | h
        · exact term_image_subset u source bound (by intro y hy; exact Finset.mem_union_right _ hy) h
        · exact False.elim (hn1 (Finset.mem_singleton.mp h))
      · have h := equivAt_free (base + 2 + termCost t + termCost u) base (base + 1) he
        simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h
        · exact False.elim (hn0 h)
        · exact False.elim (hn1 h)
  | rel r ts => exact nomatch r
  | imp a b iha ihb =>
      intro bound z hz
      simp only [scopedFormula, Formula.free, Finset.mem_union] at hz
      rcases hz with ha | hb
      · rcases Finset.mem_union.mp (iha bound ha) with h | h
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
        · exact Finset.mem_union_right _ h
      · rcases Finset.mem_union.mp (ihb bound hb) with h | h
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
        · exact Finset.mem_union_right _ h
  | @all n body ih =>
      intro bound z hz
      let source : Peano.language.BoundedFormula Nat n := .all body
      let x := scopeBase source bound
      change z ∈ (CompactNamed.Formula.all x (.imp (domainAt (x + 1) x)
        (scopedFormula (n + 1) body (Fin.snoc bound x)))).free at hz
      simp only [Formula.free, Finset.mem_erase, Finset.mem_union] at hz
      rcases hz with ⟨hne, hd | hb⟩
      · have h := domainAt_free (x + 1) x hd
        exact False.elim (hne (Finset.mem_singleton.mp h))
      · rcases Finset.mem_union.mp (ih (Fin.snoc bound x) hb) with hf | hv
        · exact Finset.mem_union_left _ hf
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
          have he : (Fin.snoc bound x : Fin (n + 1) → Nat) i = x ∨
              ∃ j : Fin n, (Fin.snoc bound x : Fin (n + 1) → Nat) i = bound j := by
            refine Fin.lastCases ?_ (fun j => ?_) i
            · left; simp
            · right; exact ⟨j, by simp⟩
          rcases he with he | ⟨j, he⟩
          · exact False.elim (hne (hi.symm.trans he))
          · exact Finset.mem_union_right _
              (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, he.symm.trans hi⟩)

end PASoundness.PAtoCompactFreeNames

#print axioms PASoundness.PAtoCompactFreeNames.mapNames_free_subset
#print axioms PASoundness.PAtoCompactFreeNames.termGraph_free_subset
#print axioms PASoundness.PAtoCompactFreeNames.scopedFormula_free_subset
