import PASoundness.PAtoCompactEqualityGraphTruth

/-! Standard-HF truth of the concrete scoped PA formula translation. This
is a semantic correspondence, not a K proof of translated PA axioms. -/
namespace PASoundness.PAtoCompactFormulaFullTruth

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermGraphTruth PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactEqualityGraphTruth PASoundness.HFCoding
open PASoundness.CompactMatrix (Environment update)

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Truth of each bounded source formula agrees with its generated compact
formula when all used free names and active bound names carry their ordinal
codes. The hypotheses permit name collisions only when their assigned values
are consistent. -/
theorem scoped_truth {n : Nat} (φ : Peano.language.BoundedFormula Nat n) :
    ∀ (bound : Fin n → Nat) (ρ : Environment) (v : Nat → Nat) (xs : Fin n → Nat),
      (∀ x ∈ φ.freeVarFinset, ρ x = (ordinal (v x)).code) →
      (∀ i, ρ (bound i) = (ordinal (xs i)).code) →
      ((scopedFormula n φ bound).Realize ρ ↔ φ.Realize v xs) := by
  induction φ with
  | falsum =>
      intro bound ρ v xs hfree hbound
      rfl
  | equal t u =>
      intro bound ρ v xs hfree hbound
      exact scoped_equal_truth t u bound ρ v xs hfree hbound
  | rel r ts =>
      exact nomatch r
  | imp a b iha ihb =>
      intro bound ρ v xs hfree hbound
      have ha : ∀ x ∈ a.freeVarFinset, ρ x = (ordinal (v x)).code := by
        intro x hx
        apply hfree x
        exact Finset.mem_union_left _ hx
      have hb : ∀ x ∈ b.freeVarFinset, ρ x = (ordinal (v x)).code := by
        intro x hx
        apply hfree x
        exact Finset.mem_union_right _ hx
      change ((scopedFormula _ a bound).Realize ρ → (scopedFormula _ b bound).Realize ρ) ↔
        (a.Realize v xs → b.Realize v xs)
      constructor
      · intro h hs
        exact (ihb bound ρ v xs hb hbound).mp (h ((iha bound ρ v xs ha hbound).mpr hs))
      · intro h hs
        exact (ihb bound ρ v xs hb hbound).mpr (h ((iha bound ρ v xs ha hbound).mp hs))
  | @all n body ih =>
      intro bound ρ v xs hfree hbound
      let source : Peano.language.BoundedFormula Nat n := .all body
      let x := scopeBase source bound
      have bodyAt (j : Nat) :
          (scopedFormula (n + 1) body (Fin.snoc bound x)).Realize
            (update ρ x (ordinal j).code) ↔ body.Realize v (Fin.snoc xs j) := by
        apply ih (Fin.snoc bound x) (update ρ x (ordinal j).code) v (Fin.snoc xs j)
        · intro y hy
          have hlt : y < x := free_lt_scopeBase source bound y hy
          have hne : y ≠ x := Nat.ne_of_lt hlt
          simpa [update, hne] using hfree y hy
        · intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simp [update]
          · simp only [Fin.snoc_castSucc]
            have hne : bound j ≠ x := Nat.ne_of_lt (bound_lt_scopeBase source bound j)
            simpa [update, hne] using hbound j
      change (∀ w, (domainAt (x + 1) x).Realize (update ρ x w) →
        (scopedFormula (n + 1) body (Fin.snoc bound x)).Realize (update ρ x w)) ↔
          ∀ j, body.Realize v (Fin.snoc xs j)
      constructor
      · intro h j
        apply (bodyAt j).mp
        apply h
        apply (domainAt_iff (x + 1) x (by omega) _).mpr
        exact ⟨j, by simp [update]⟩
      · intro h w hw
        obtain ⟨j, hj⟩ := (domainAt_iff (x + 1) x (by omega) _).mp hw
        have hw' : w = (ordinal j).code := by simpa [update] using hj
        subst w
        exact (bodyAt j).mpr (h j)

/-- Every PA formula has the same truth value as its concrete translation on
the ordinal-coded standard assignment. -/
theorem formula_truth (φ : Peano.Formula) (v : Nat → Nat) :
    (PASoundness.CompactMatrix.decode (code φ)).Realize
      (PASoundness.PAtoCompactOpenScope.ordinalAssignment v) ↔ φ.Realize v := by
  rw [show code φ = (formula φ).encode by rfl, Formula.encode_realize]
  exact scoped_truth φ Fin.elim0 (PASoundness.PAtoCompactOpenScope.ordinalAssignment v)
    v Fin.elim0 (by intro x hx; rfl) (by intro i; exact Fin.elim0 i)

end PASoundness.PAtoCompactFormulaFullTruth

#print axioms PASoundness.PAtoCompactFormulaFullTruth.scoped_truth
#print axioms PASoundness.PAtoCompactFormulaFullTruth.formula_truth
