import PASoundness.HierarchyCounterexample
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.ModelTheory.Complexity

/-!
# Finite specialization for the polynomial control model

This module proves that truth of every existential quantifier-free sentence
in the explicit Nat[X] control model transfers to standard Nat. Both positive
and negative atomic truth values stabilize, so Boolean combinations, including
negation, are covered. The observer formulas do not acquire a polynomial or
eventual-order primitive from this semantic model argument.
-/

namespace PASoundness.HierarchyCounterexample

open FirstOrder FirstOrder.Language Filter

theorem real_eventually_positive (p : Polynomial ℝ) (hp : 0 < p.leadingCoeff) :
    ∀ᶠ x : ℝ in atTop, 0 < p.eval x := by
  by_cases hd : p.degree ≤ 0
  · have hC := Polynomial.eq_C_of_degree_le_zero hd
    have hc : 0 < p.coeff 0 := by
      simpa only [Polynomial.leadingCoeff,
        Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr hd] using hp
    exact .of_forall (fun x => by rw [hC, Polynomial.eval_C]; exact hc)
  · exact (p.tendsto_atTop_of_leadingCoeff_nonneg (lt_of_not_ge hd) hp.le).eventually_gt_atTop 0

theorem real_eventually_negative (p : Polynomial ℝ) (hp : p.leadingCoeff < 0) :
    ∀ᶠ x : ℝ in atTop, p.eval x < 0 := by
  have h := real_eventually_positive (-p) (by simpa using hp)
  simpa using h

theorem eventuallyLt_iff (p q : Polynomial Nat) :
    EventuallyLt p q ↔ ∀ᶠ m : Nat in atTop, p.eval m < q.eval m :=
  eventually_atTop.symm

/-- The natural-polynomial order eventually chooses one of the three ordinary
comparison outcomes. Equality is polynomial equality, not pointwise equality
at an unspecified evaluation argument. -/
theorem polynomial_trichotomy (p q : Polynomial Nat) :
    p = q ∨ EventuallyLt p q ∨ EventuallyLt q p := by
  classical
  let f : Nat →+* ℝ := Nat.castRingHom ℝ
  let d : Polynomial ℝ := q.map f - p.map f
  have heval (r : Polynomial Nat) (m : Nat) :
      (r.map f).eval (m : ℝ) = ((r.eval m : Nat) : ℝ) :=
    Polynomial.eval_map_apply f m
  by_cases hd : d = 0
  · left
    have hm : q.map f = p.map f := sub_eq_zero.mp hd
    exact (Polynomial.map_injective f Nat.cast_injective hm).symm
  · have hc : d.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hd
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · right; right
      apply (eventuallyLt_iff q p).mpr
      have h : ∀ᶠ m : Nat in atTop, d.eval (m : ℝ) < 0 :=
        tendsto_natCast_atTop_atTop.eventually (real_eventually_negative d hneg)
      filter_upwards [h] with m hm
      have hm' : ((q.eval m : Nat) : ℝ) < ((p.eval m : Nat) : ℝ) := by
        simpa only [d, Polynomial.eval_sub, heval, sub_neg] using hm
      exact Nat.cast_lt.mp hm'
    · right; left
      apply (eventuallyLt_iff p q).mpr
      have h : ∀ᶠ m : Nat in atTop, 0 < d.eval (m : ℝ) :=
        tendsto_natCast_atTop_atTop.eventually (real_eventually_positive d hpos)
      filter_upwards [h] with m hm
      have hm' : ((p.eval m : Nat) : ℝ) < ((q.eval m : Nat) : ℝ) := by
        simpa only [d, Polynomial.eval_sub, heval, sub_pos] using hm
      exact Nat.cast_lt.mp hm'

/-- Every equality atom has its full truth value preserved after one finite
specialization threshold. -/
theorem eventually_equal_iff (p q : Polynomial Nat) :
    ∀ᶠ m : Nat in atTop, (p = q ↔ p.eval m = q.eval m) := by
  rcases polynomial_trichotomy p q with rfl | hpq | hqp
  · exact .of_forall (fun _ => ⟨fun _ => rfl, fun _ => rfl⟩)
  · have hne : p ≠ q := by
      intro heq
      obtain ⟨b,hb⟩ := hpq
      exact (Nat.lt_irrefl _) (heq ▸ hb b le_rfl)
    filter_upwards [(eventuallyLt_iff p q).mp hpq] with m hm
    simp only [hne, Nat.ne_of_lt hm]
  · have hne : p ≠ q := by
      intro heq
      obtain ⟨b,hb⟩ := hqp
      exact (Nat.lt_irrefl _) (heq ▸ hb b le_rfl)
    filter_upwards [(eventuallyLt_iff q p).mp hqp] with m hm
    simp only [hne, Nat.ne_of_gt hm]

/-- Negated order atoms also stabilize; negation is not discarded when
specializing a quantifier-free formula. -/
theorem eventually_less_iff (p q : Polynomial Nat) :
    ∀ᶠ m : Nat in atTop, (EventuallyLt p q ↔ p.eval m < q.eval m) := by
  by_cases h : EventuallyLt p q
  · filter_upwards [(eventuallyLt_iff p q).mp h] with m hm
    exact ⟨fun _ => hm, fun _ => h⟩
  · rcases polynomial_trichotomy p q with rfl | hpq | hqp
    · exact .of_forall (fun m => by simp only [h, lt_self_iff_false])
    · exact (h hpq).elim
    · filter_upwards [(eventuallyLt_iff q p).mp hqp] with m hm
      exact ⟨fun h' => (h h').elim, fun hn => (Nat.lt_asymm hm hn).elim⟩

/-- Substituting a natural number for X commutes with realization of each
arithmetic term, including multiplication and arbitrarily nested terms. -/
theorem realize_term_specialize {α : Type*} (t : language.Term α)
    (v : α → Polynomial Nat) (m : Nat) :
    (t.realize v).eval m = t.realize (fun i => (v i).eval m) := by
  induction t with
  | var i => rfl
  | @func n f ts ih =>
    cases f with
    | zero => simp [FirstOrder.Language.Term.realize]
    | succ => simp [FirstOrder.Language.Term.realize, ih, Nat.succ_eq_add_one]
    | add => simp [FirstOrder.Language.Term.realize, ih]
    | mul =>
      change ((ts 0).realize v * (ts 1).realize v).eval m =
        (ts 0).realize (fun i => (v i).eval m) * (ts 1).realize (fun i => (v i).eval m)
      simp only [Polynomial.eval_mul, ih]

theorem realize_term_specialize_sum {α : Type*} {n : Nat}
    (t : language.Term (α ⊕ Fin n)) (v : α → Polynomial Nat)
    (xs : Fin n → Polynomial Nat) (m : Nat) :
    (t.realize (Sum.elim v xs)).eval m =
      t.realize (Sum.elim (fun i => (v i).eval m) (fun i => (xs i).eval m)) := by
  rw [realize_term_specialize]
  congr 1
  funext i
  cases i <;> rfl

theorem eventually_realize_atomic {α : Type*} {n : Nat}
    {φ : language.BoundedFormula α n} (h : φ.IsAtomic)
    (v : α → Polynomial Nat) (xs : Fin n → Polynomial Nat) :
    ∀ᶠ m : Nat in atTop, φ.Realize v xs ↔
      φ.Realize (fun i => (v i).eval m) (fun i => (xs i).eval m) := by
  cases h with
  | equal t u =>
    have h := eventually_equal_iff (t.realize (Sum.elim v xs)) (u.realize (Sum.elim v xs))
    simpa only [BoundedFormula.realize_bdEqual, ← realize_term_specialize_sum] using h
  | rel r ts =>
    cases r with
    | lt =>
      have h := eventually_less_iff ((ts 0).realize (Sum.elim v xs))
        ((ts 1).realize (Sum.elim v xs))
      simpa only [Relations.boundedFormula, BoundedFormula.Realize, polynomial_rel_lt, nat_rel_lt,
        ← realize_term_specialize_sum] using h

/-- A single threshold preserves all atoms and Boolean connectives of the
given finite formula simultaneously. It depends on the formula and its finite
tuple of polynomial values; no uniform bound over all formulas is asserted. -/
theorem eventually_realize_qf {α : Type*} {n : Nat}
    {φ : language.BoundedFormula α n} (h : φ.IsQF)
    (v : α → Polynomial Nat) (xs : Fin n → Polynomial Nat) :
    ∀ᶠ m : Nat in atTop, φ.Realize v xs ↔
      φ.Realize (fun i => (v i).eval m) (fun i => (xs i).eval m) := by
  induction h with
  | falsum => exact .of_forall (fun _ => Iff.rfl)
  | of_isAtomic h => exact eventually_realize_atomic h v xs
  | imp hφ hψ ihφ ihψ =>
    filter_upwards [ihφ, ihψ] with m hmφ hmψ
    exact imp_congr hmφ hmψ

/-- Mathlib's canonical `IsExistential` permits any finite prefix of
existential quantifiers over an `IsQF` matrix, including a prefix of length
zero. Polynomial witnesses are specialized together at the same index. -/
theorem eventually_realize_existential {α : Type*} {n : Nat}
    {φ : language.BoundedFormula α n} (h : φ.IsExistential)
    (v : α → Polynomial Nat) (xs : Fin n → Polynomial Nat)
    (hφ : φ.Realize v xs) :
    ∀ᶠ m : Nat in atTop,
      φ.Realize (fun i => (v i).eval m) (fun i => (xs i).eval m) := by
  induction h generalizing v with
  | of_isQF hq =>
    exact (eventually_realize_qf hq v xs).mono (fun _ hm => hm.mp hφ)
  | @ex n φ h ih =>
    obtain ⟨p,hp⟩ := BoundedFormula.realize_ex.mp hφ
    have hh := ih v (Fin.snoc xs p) hp
    filter_upwards [hh] with m hm
    apply BoundedFormula.realize_ex.mpr
    refine ⟨p.eval m, ?_⟩
    simpa only [← Function.comp_def, Fin.comp_snoc] using hm

/-- Closed existential quantifier-free truth in this particular polynomial
structure transfers to standard Nat. This is a preservation theorem about
two explicitly defined structures, not an arithmetic truth predicate. -/
theorem existential_truth_specializes {φ : Sentence} (h : φ.IsExistential)
    (hφ : (Polynomial Nat) ⊨ φ) : Nat ⊨ φ := by
  simp only [FirstOrder.Language.Sentence.Realize,
    FirstOrder.Language.Formula.Realize] at hφ ⊢
  have hφ' : BoundedFormula.Realize φ
      (Empty.elim : Empty → Polynomial Nat) (Fin.elim0 : Fin 0 → Polynomial Nat) := by
    convert hφ using 1
  have hh := eventually_realize_existential h Empty.elim Fin.elim0 hφ'
  obtain ⟨m,hm⟩ := hh.exists
  convert hm using 1

/-- The recovered bare singleton theory has no false existential
quantifier-free consequence in standard Nat. This uses generic first-order
proof soundness in the polynomial model, independently of PA soundness. -/
theorem existential_qf_sound {φ : Sentence} (hφ : φ.IsExistential)
    (hproof : FOL.Proves theory φ) : Nat ⊨ φ := by
  apply existential_truth_specializes hφ
  apply FOL.theory_sound (M := Polynomial Nat) (T := theory) (φ := φ)
    (fun ψ hψ => by cases hψ; exact sentence_true_polynomial)
  exact hproof

/-- A closed scoped counterexample to identifying all existential-qf
channels with the bounded-matrix Sigma_1 class: the same consistent bare
theory is sound on every canonical existential-qf sentence and proves the
explicit standard-false existential bounded sentence. -/
theorem qf_bounded_separation :
    (¬ FOL.Proves theory (⊥ : Sentence)) ∧
    (∀ φ : Sentence, φ.IsExistential → FOL.Proves theory φ → Nat ⊨ φ) ∧
    ∃ φ : Sentence, ExistsBounded φ ∧ FOL.Proves theory φ ∧ ¬ Nat ⊨ φ :=
  ⟨consistent, fun _ => existential_qf_sound,
    sentence, sentence_existsBounded, proves_sentence, sentence_false_nat⟩

end PASoundness.HierarchyCounterexample
