import PASoundness.PAtoCompactTermGraphFullTruth
import PASoundness.PAtoCompactFormulaTranslation

/-! Standard-HF truth of the equality case of the generated PA formula
translation. The input assignment and freshness hypotheses are explicit;
this does not prove K witness existence or full formula truth. -/
namespace PASoundness.PAtoCompactEqualityGraphTruth

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermRenamingSemantics PASoundness.PAtoCompactTermGraphTruth
open PASoundness.PAtoCompactTermGraphFullTruth PASoundness.HFCoding
open PASoundness.PAtoCompactFormulaTranslation
open PASoundness.CompactMatrix (Environment update)

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Two generated term graphs and their isomorphism test realize arithmetic
equality. The source variable names used by either term lie below both
existential witness labels. -/
theorem equality_graph_truth {α : Type} [DecidableEq α] (varName : α → Nat)
    (t u : Peano.language.Term α) (base : Nat) (ρ : Environment) (v : α → Nat)
    (htnames : ∀ a ∈ t.varFinset, varName a < base)
    (hunames : ∀ a ∈ u.varFinset, varName a < base)
    (htvalues : ∀ a ∈ t.varFinset, ρ (varName a) = (ordinal (v a)).code)
    (huvalues : ∀ a ∈ u.varFinset, ρ (varName a) = (ordinal (v a)).code) :
    (CompactNamed.Formula.ex base (.ex (base + 1)
      (andF (termGraph varName t base (base + 2))
        (andF (termGraph varName u (base + 1) (base + 2 + termCost t))
          (equivAt (base + 2 + termCost t + termCost u) base (base + 1)))))).Realize ρ ↔
      t.realize v = u.realize v := by
  have ht (a b : Nat) :
      (termGraph varName t base (base + 2)).Realize
        (update (update ρ base a) (base + 1) b) ↔ a = (ordinal (t.realize v)).code := by
    have h := graph_truth varName t base (base + 2)
      (update (update ρ base a) (base + 1) b) v (by omega) htnames (by
        intro x hx
        have h0 : varName x ≠ base := by have := htnames x hx; omega
        have h1 : varName x ≠ base + 1 := by have := htnames x hx; omega
        simpa [update, h0, h1] using htvalues x hx)
    simpa [update] using h
  have hu (a b : Nat) :
      (termGraph varName u (base + 1) (base + 2 + termCost t)).Realize
        (update (update ρ base a) (base + 1) b) ↔ b = (ordinal (u.realize v)).code := by
    have h := graph_truth varName u (base + 1) (base + 2 + termCost t)
      (update (update ρ base a) (base + 1) b) v (by omega) (by
        intro x hx
        have := hunames x hx
        omega) (by
        intro x hx
        have h0 : varName x ≠ base := by have := hunames x hx; omega
        have h1 : varName x ≠ base + 1 := by have := hunames x hx; omega
        simpa [update, h0, h1] using huvalues x hx)
    simpa [update] using h
  simp only [CompactNamed.Formula.Realize]
  constructor
  · rintro ⟨a, b, h⟩
    have hleft := ((andF_realize _ _ _).mp h).1
    have hright := ((andF_realize _ _ _).mp ((andF_realize _ _ _).mp h).2).1
    have hrel := ((andF_realize _ _ _).mp ((andF_realize _ _ _).mp h).2).2
    have ha := (ht a b).mp hleft
    have hb := (hu a b).mp hright
    subst a
    subst b
    exact (equivAt_ordinal (base + 2 + termCost t + termCost u) base (base + 1)
      (t.realize v) (u.realize v) (by omega) (by omega) (by omega) _
      (by simp [update]) (by simp [update])).mp hrel
  · intro h
    refine ⟨(ordinal (t.realize v)).code, (ordinal (u.realize v)).code, ?_⟩
    apply (andF_realize _ _ _).mpr
    refine ⟨(ht _ _).mpr rfl, ?_⟩
    apply (andF_realize _ _ _).mpr
    refine ⟨(hu _ _).mpr rfl, ?_⟩
    exact (equivAt_ordinal (base + 2 + termCost t + termCost u) base (base + 1)
      (t.realize v) (u.realize v) (by omega) (by omega) (by omega) _
      (by simp [update]) (by simp [update])).mpr h

/-- A free variable occurring in a sum-labelled term occurs in the term's
left-variable set. -/
theorem inl_mem_left {n : Nat} (t : Peano.language.Term (Nat ⊕ Fin n))
    (x : Nat) (h : Sum.inl x ∈ t.varFinset) : x ∈ t.varFinsetLeft := by
  induction t with
  | var a =>
      cases a with
      | inl y => simpa [FirstOrder.Language.Term.varFinset, FirstOrder.Language.Term.varFinsetLeft] using h
      | inr i => simp [FirstOrder.Language.Term.varFinset] at h
  | @func l f ts ih =>
      simp only [FirstOrder.Language.Term.varFinset, Finset.mem_biUnion,
        Finset.mem_univ, true_and] at h
      obtain ⟨i, hi⟩ := h
      simp only [FirstOrder.Language.Term.varFinsetLeft, Finset.mem_biUnion,
        Finset.mem_univ, true_and]
      exact ⟨i, ih i hi⟩

/-- The actual translated bounded equality is true exactly when the source
equality is true, provided the free and active bound assignments are coded
consistently. No injectivity of the bound-name map is assumed. -/
theorem scoped_equal_truth {n : Nat} (t u : Peano.language.Term (Nat ⊕ Fin n))
    (bound : Fin n → Nat) (ρ : Environment) (v : Nat → Nat) (xs : Fin n → Nat)
    (hfree : ∀ x ∈ (FirstOrder.Language.BoundedFormula.equal t u).freeVarFinset,
      ρ x = (ordinal (v x)).code)
    (hbound : ∀ i, ρ (bound i) = (ordinal (xs i)).code) :
    (scopedFormula n (.equal t u) bound).Realize ρ ↔
      (FirstOrder.Language.BoundedFormula.equal t u).Realize v xs := by
  let source : Peano.language.BoundedFormula Nat n := .equal t u
  let base := scopeBase source bound
  have hn (a : Nat ⊕ Fin n) (h : a ∈ t.varFinset ∨ a ∈ u.varFinset) :
      Sum.elim id bound a < base := by
    cases a with
    | inl x =>
        have hx : x ∈ source.freeVarFinset := by
          change x ∈ t.varFinsetLeft ∪ u.varFinsetLeft
          rcases h with h | h
          · exact Finset.mem_union_left _ (inl_mem_left t x h)
          · exact Finset.mem_union_right _ (inl_mem_left u x h)
        exact free_lt_scopeBase source bound x hx
    | inr i => exact bound_lt_scopeBase source bound i
  have hv (a : Nat ⊕ Fin n) (h : a ∈ t.varFinset ∨ a ∈ u.varFinset) :
      ρ (Sum.elim id bound a) = (ordinal (Sum.elim v xs a)).code := by
    cases a with
    | inl x =>
        have hx : x ∈ source.freeVarFinset := by
          change x ∈ t.varFinsetLeft ∪ u.varFinsetLeft
          rcases h with h | h
          · exact Finset.mem_union_left _ (inl_mem_left t x h)
          · exact Finset.mem_union_right _ (inl_mem_left u x h)
        exact hfree x hx
    | inr i => exact hbound i
  change (CompactNamed.Formula.ex base (.ex (base + 1)
      (andF (termGraph (Sum.elim id bound) t base (base + 2))
        (andF (termGraph (Sum.elim id bound) u (base + 1) (base + 2 + termCost t))
          (equivAt (base + 2 + termCost t + termCost u) base (base + 1)))))).Realize ρ ↔
    t.realize (Sum.elim v xs) = u.realize (Sum.elim v xs)
  exact equality_graph_truth (Sum.elim id bound) t u base ρ (Sum.elim v xs)
    (fun a ha => hn a (.inl ha)) (fun a ha => hn a (.inr ha))
    (fun a ha => hv a (.inl ha)) (fun a ha => hv a (.inr ha))

end PASoundness.PAtoCompactEqualityGraphTruth

#print axioms PASoundness.PAtoCompactEqualityGraphTruth.equality_graph_truth
#print axioms PASoundness.PAtoCompactEqualityGraphTruth.scoped_equal_truth
