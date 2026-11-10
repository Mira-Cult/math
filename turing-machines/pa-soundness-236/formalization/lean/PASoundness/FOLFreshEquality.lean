import PASoundness.FOLQuantifierDerivations
/-! Finite equality proofs with a freshly chosen substitution variable. -/
namespace PASoundness.FOL
open FirstOrder FirstOrder.Language
variable {L : Language} {A : Formula L → Prop}

theorem term_subst_fixed (t : Term L) (σ : Nat → Term L)
    (h : ∀ x, x ∈ t.varFinset → σ x = .var x) : t.subst σ = t := by
  induction t with
  | var x => exact h x (by simp [FirstOrder.Language.Term.varFinset])
  | func f ts ih =>
    simp only [FirstOrder.Language.Term.subst]
    congr 1
    funext i
    apply ih i
    intro x hx
    apply h x
    simp only [FirstOrder.Language.Term.varFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, hx⟩

theorem term_subst_fresh (t : Term L) (x : Nat) (u : Term L)
    (hx : x ∉ t.varFinset) :
    t.subst (fun y => if y = x then u else .var y) = t := by
  apply term_subst_fixed
  intro y hy
  have hne : y ≠ x := by intro h; subst y; exact hx hy
  simp [hne]

theorem fresh_for_term (t : Term L) : ∃ x, x ∉ t.varFinset := by
  let x := t.varFinset.sup id + 1
  refine ⟨x, ?_⟩
  intro hx
  have hle : x ≤ t.varFinset.sup id := Finset.le_sup (f := id) hx
  dsimp [x] at hle
  omega

/-- A genuine first-order derivation of equality transitivity for arbitrary
terms. The auxiliary variable is chosen fresh from the first term. -/
theorem equality_transitivity (a b c : Term L) :
    Derivation A ((b.equal c).imp ((a.equal b).imp (a.equal c))) := by
  obtain ⟨x, hx⟩ := fresh_for_term a
  have h := Derivation.logical (Axiom := A)
    (LogicalAxiom.eqSubst (a.equal (.var x)) x b c)
  have hb : substAt (a.equal (.var x)) x b = a.equal b := by
    simp only [substAt, FOL.equality_subst, FirstOrder.Language.Term.subst, ↓reduceIte]
    rw [term_subst_fresh a x b hx]
  have hc : substAt (a.equal (.var x)) x c = a.equal c := by
    simp only [substAt, FOL.equality_subst, FirstOrder.Language.Term.subst, ↓reduceIte]
    rw [term_subst_fresh a x c hx]
  rw [hb, hc] at h
  exact h

/-- A genuine first-order derivation of equality symmetry. -/
theorem equality_symmetry (a b : Term L) : Derivation A ((a.equal b).imp (b.equal a)) := by
  obtain ⟨x, hx⟩ := fresh_for_term a
  have h := Derivation.logical (Axiom := A)
    (LogicalAxiom.eqSubst ((.var x : Term L).equal a) x a b)
  have ha : substAt ((.var x : Term L).equal a) x a = a.equal a := by
    simp only [substAt, FOL.equality_subst, FirstOrder.Language.Term.subst, ↓reduceIte]
    rw [term_subst_fresh a x a hx]
  have hb : substAt ((.var x : Term L).equal a) x b = b.equal a := by
    simp only [substAt, FOL.equality_subst, FirstOrder.Language.Term.subst, ↓reduceIte]
    rw [term_subst_fresh a x b hx]
  rw [ha, hb] at h
  apply Context.closeEmpty
  apply Context.deduction
  exact .mp (.mp (.closed h) (Context.head [] (a.equal b))) (.closed (.logical (.eqRefl a)))

namespace Derivation

/-- Equality symmetry as a rule on ordinary derivations. -/
theorem eqSymm {a b : Term L} (h : Derivation A (a.equal b)) : Derivation A (b.equal a) :=
  .mp (equality_symmetry a b) h

/-- Equality transitivity as a rule on ordinary derivations. -/
theorem eqTrans {a b c : Term L} (hab : Derivation A (a.equal b))
    (hbc : Derivation A (b.equal c)) : Derivation A (a.equal c) :=
  .mp (.mp (equality_transitivity a b c) hbc) hab
end Derivation

namespace Context

/-- Equality symmetry within any finite temporary proof context. -/
theorem eqSymm {Γ : List (Formula L)} {a b : Term L}
    (h : Context A Γ (a.equal b)) : Context A Γ (b.equal a) :=
  .mp (.closed (equality_symmetry a b)) h

/-- Equality transitivity within any finite temporary proof context. -/
theorem eqTrans {Γ : List (Formula L)} {a b c : Term L}
    (hab : Context A Γ (a.equal b)) (hbc : Context A Γ (b.equal c)) :
    Context A Γ (a.equal c) :=
  .mp (.mp (.closed (equality_transitivity a b c)) hbc) hab
end Context
end PASoundness.FOL
