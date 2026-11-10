import PASoundness.Peano
import PASoundness.PAtoCompactCandidateQuantifiers

/-! Capture-safe semantic opening of one PA de Bruijn scope. This file gives
one quantifier step under an explicit body interpretation; it does not define
a complete translation or construct any object-level K derivation. -/
namespace PASoundness.PAtoCompactOpenScope

open FirstOrder FirstOrder.Language
open PASoundness.CompactMatrix PASoundness.CompactSemantics PASoundness.CompactProof
open PASoundness.HFCoding PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactCandidateQuantifiers

/-- Open the sole in-scope bound position as the named variable `x`. -/
def openOne (φ : Peano.language.BoundedFormula Nat 1) (x : Nat) : Peano.Formula :=
  φ.toFormula.relabel (Sum.elim id (fun _ => x))

/-- Bounded formulas ignore assignments away from their syntactic free names. -/
theorem bounded_realize_agree {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (v w : Nat → Nat) (xs : Fin n → Nat)
    (h : ∀ x ∈ φ.freeVarFinset, v x = w x) :
    φ.Realize v xs ↔ φ.Realize w xs := by
  have hv := BoundedFormula.realize_restrictFreeVar
    (φ := φ) (f := fun x => (x : Nat)) (v := v) (xs := xs) v (by intro x; rfl)
  have hw := BoundedFormula.realize_restrictFreeVar
    (φ := φ) (f := fun x => (x : Nat)) (v := v) (xs := xs) w
    (by intro x; exact h x x.property)
  exact hv.symm.trans hw

/-- Opening is capture-safe provided the chosen name is absent from the
original scope's free variables. Existing inner bound variables are handled by
mathlib's locally nameless `toFormula`, not by raw replacement. -/
theorem openOne_truth (φ : Peano.language.BoundedFormula Nat 1) (x : Nat)
    (fresh : x ∉ φ.freeVarFinset) (v : Nat → Nat) (a : Nat) :
    (openOne φ x).Realize (Function.update v x a) ↔
      φ.Realize v (Fin.snoc default a) := by
  rw [openOne, Formula.realize_relabel, BoundedFormula.realize_toFormula]
  have hnames : ((Function.update v x a ∘ Sum.elim id (fun _ : Fin 1 => x)) ∘ Sum.inl) =
      Function.update v x a := rfl
  rw [hnames]
  have hbound : ((Function.update v x a ∘ Sum.elim id (fun _ : Fin 1 => x)) ∘ Sum.inr) =
      Fin.snoc (default : Fin 0 → Nat) a := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    simp [Fin.snoc_zero]
  rw [hbound]
  apply bounded_realize_agree
  intro y hy
  have hne : y ≠ x := by intro h; subst y; exact fresh hy
  simp [hne]

/-- Named rebinding of the opened body has the original universal meaning. -/
theorem openOne_all_truth (φ : Peano.language.BoundedFormula Nat 1) (x : Nat)
    (fresh : x ∉ φ.freeVarFinset) (v : Nat → Nat) :
    (FOL.allAt x (openOne φ x)).Realize v ↔ FirstOrder.Language.Formula.Realize φ.all v := by
  rw [FOL.realize_allAt]
  change (∀ a, (openOne φ x).Realize (Function.update v x a)) ↔
    ∀ a, φ.Realize v (Fin.snoc default a)
  exact forall_congr' (fun a => openOne_truth φ x fresh v a)

/-- Ordinal-code a standard arithmetic assignment. -/
def ordinalAssignment (v : Nat → Nat) : Environment := fun x => (ordinal (v x)).code

/-- A translated opened body gives a translated literal scoped universal.
Both freshness conditions and the complete body truth assumption remain explicit. -/
theorem guarded_scope_all_truth (φ : Peano.language.BoundedFormula Nat 1)
    (x b p q u k a m r body : Nat)
    (scopeFresh : x ∉ φ.freeVarFinset)
    (candidateFresh : [x,b,p,q,u,k,a,m,r].Nodup)
    (bodyTruth : ∀ v : Nat → Nat,
      (decode body).Realize (ordinalAssignment v) ↔ (openOne φ x).Realize v)
    (v : Nat → Nat) :
    (decode (allCode x (imp
      (both (oneLevelTransitiveCode x b p q)
        (both (greatestSubsetsCode x u k m r) (leastSubsetsCode x u k a m r))) body))).Realize
      (ordinalAssignment v) ↔ FirstOrder.Language.Formula.Realize φ.all v := by
  rw [realize_all]
  simp only [realize_imp]
  rw [candidate_forall x b p q u k a m r (ordinalAssignment v) candidateFresh
    (fun z => (decode body).Realize (update (ordinalAssignment v) x z))]
  rw [← openOne_all_truth φ x scopeFresh v, FOL.realize_allAt]
  apply forall_congr'
  intro n
  have hu : update (ordinalAssignment v) x (ordinal n).code =
      ordinalAssignment (Function.update v x n) := by
    funext y
    by_cases h : y = x <;> simp [update, ordinalAssignment, h]
  rw [hu]
  exact bodyTruth _

end PASoundness.PAtoCompactOpenScope

#print axioms PASoundness.PAtoCompactOpenScope.guarded_scope_all_truth
