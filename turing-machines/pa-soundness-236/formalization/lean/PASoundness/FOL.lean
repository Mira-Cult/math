import Mathlib.ModelTheory.Semantics

/-!
# A syntactic first-order calculus over mathlib syntax

Terms and formulas are mathlib's canonical first-order objects. Bound variables
use its locally nameless de Bruijn levels. Free variables are natural numbers.
`allAt` binds one named free variable; `substAt` substitutes a term for it without
capture. `Derivation` is an inductive Hilbert calculus, not semantic entailment.
The word `BoundedFormula` in mathlib names a scope index, not the arithmetic
bounded-quantifier class Delta_0.
-/

namespace PASoundness.FOL

open FirstOrder FirstOrder.Language

universe u

variable {L : Language}

abbrev Formula (L : Language) := L.Formula Nat
abbrev Term (L : Language) := L.Term Nat

/-- Bind every free occurrence of `x`; existing bound variables are shifted by
mathlib's capture-avoiding relabelling operation. -/
def allAt (x : Nat) (φ : Formula L) : Formula L :=
  (BoundedFormula.relabel (fun y =>
    if y = x then Sum.inr (0 : Fin 1) else Sum.inl y) φ).all

/-- Capture-avoiding substitution at a named free variable. -/
def substAt (φ : Formula L) (x : Nat) (t : Term L) : Formula L :=
  φ.subst (fun y => if y = x then t else .var y)

/-- The canonical embedding of sentences into formulas with named free variables. -/
def openSentence (φ : L.Sentence) : Formula L := φ.relabel Empty.elim

section Semantics

variable {M : Type u} [L.Structure M]

theorem realize_rename (φ : Formula L) (r : Nat → Nat) (v : Nat → M) :
    (φ.relabel r).Realize v ↔ φ.Realize (v ∘ r) :=
  FirstOrder.Language.Formula.realize_relabel

theorem realize_subst (φ : Formula L) (σ : Nat → Term L) (v : Nat → M) :
    FirstOrder.Language.Formula.Realize (φ.subst σ) v ↔
      φ.Realize (fun x => (σ x).realize v) :=
  BoundedFormula.realize_subst

@[simp] theorem realize_substAt (φ : Formula L) (x : Nat) (t : Term L)
    (v : Nat → M) :
    (substAt φ x t).Realize v ↔ φ.Realize (Function.update v x (t.realize v)) := by
  rw [substAt, realize_subst]
  have h : (fun y => (if y = x then t else (.var y : Term L)).realize v) =
      Function.update v x (t.realize v) := by
    funext y
    by_cases h : y = x
    · simp [h]
    · simp [h]
  rw [h]

@[simp] theorem realize_allAt (φ : Formula L) (x : Nat) (v : Nat → M) :
    (allAt x φ).Realize v ↔ ∀ a : M, φ.Realize (Function.update v x a) := by
  simp only [allAt, FirstOrder.Language.Formula.Realize,
    BoundedFormula.realize_all, BoundedFormula.realize_relabel]
  apply forall_congr'
  intro a
  have h : (Sum.elim v ((Fin.snoc default a) ∘ Fin.castAdd 0) ∘
      (fun y : Nat => if y = x then Sum.inr (0 : Fin 1) else Sum.inl y)) =
      Function.update v x a := by
    funext y
    by_cases h : y = x
    · simp [h, Fin.snoc_zero]
    · simp [h]
  rw [h]
  have hz : (Fin.snoc (default : Fin 0 → M) a ∘ Fin.natAdd 1) = default :=
    funext fun i => Fin.elim0 i
  rw [hz]

/-- A formula depends only on its explicitly computed finite set of free variables. -/
theorem realize_agree (φ : Formula L) (v w : Nat → M)
    (h : ∀ x ∈ φ.freeVarFinset, v x = w x) : φ.Realize v ↔ φ.Realize w := by
  have hv := BoundedFormula.realize_restrictFreeVar
    (φ := φ) (f := fun x => (x : Nat)) (v := v) (xs := default) v (by intro x; rfl)
  have hw := BoundedFormula.realize_restrictFreeVar
    (φ := φ) (f := fun x => (x : Nat)) (v := v) (xs := default) w
    (by intro x; exact h x x.property)
  exact hv.symm.trans hw

/-- The syntactic eigenvariable side condition implies assignment independence. -/
theorem realize_update_of_not_free (φ : Formula L) (x : Nat)
    (hx : x ∉ φ.freeVarFinset) (v : Nat → M) (a : M) :
    φ.Realize (Function.update v x a) ↔ φ.Realize v := by
  apply realize_agree
  intro y hy
  have h : y ≠ x := by intro e; subst y; exact hx hy
  simp [h]

@[simp] theorem realize_openSentence (φ : L.Sentence) (v : Nat → M) :
    (openSentence φ).Realize v ↔ M ⊨ φ := by
  rw [openSentence, FirstOrder.Language.Formula.realize_relabel]
  have h : (v ∘ Empty.elim : Empty → M) = default := funext fun x => Empty.elim x
  rw [h]
  rfl

end Semantics

/-- Finite syntactic logical axiom schemas. No constructor has a truth premise. -/
inductive LogicalAxiom : Formula L → Prop
  | k (φ ψ : Formula L) : LogicalAxiom (φ.imp (ψ.imp φ))
  | s (φ ψ χ : Formula L) :
      LogicalAxiom ((φ.imp (ψ.imp χ)).imp ((φ.imp ψ).imp (φ.imp χ)))
  | classical (φ : Formula L) : LogicalAxiom (φ.not.not.imp φ)
  | allElim (φ : Formula L) (x : Nat) (t : Term L) :
      LogicalAxiom ((allAt x φ).imp (substAt φ x t))
  | allImp (φ ψ : Formula L) (x : Nat) :
      LogicalAxiom ((allAt x (φ.imp ψ)).imp ((allAt x φ).imp (allAt x ψ)))
  | vacuous (φ : Formula L) (x : Nat) (hx : x ∉ φ.freeVarFinset) :
      LogicalAxiom (φ.imp (allAt x φ))
  | eqRefl (t : Term L) : LogicalAxiom (t.equal t)
  | eqSubst (φ : Formula L) (x : Nat) (t u : Term L) :
      LogicalAxiom ((t.equal u).imp ((substAt φ x t).imp (substAt φ x u)))

/-- Finite syntactic derivation trees. Axioms are universally interpreted open
formulas; thus generalization has no extra assumption-context side condition. -/
inductive Derivation (Axiom : Formula L → Prop) : Formula L → Prop
  | axiom {φ} : Axiom φ → Derivation Axiom φ
  | logical {φ} : LogicalAxiom φ → Derivation Axiom φ
  | mp {φ ψ} : Derivation Axiom (φ.imp ψ) → Derivation Axiom φ → Derivation Axiom ψ
  | generalize {φ} (x : Nat) : Derivation Axiom φ → Derivation Axiom (allAt x φ)

section Soundness

variable {M : Type u} [L.Structure M]

theorem logical_sound {φ : Formula L} (h : LogicalAxiom φ) (v : Nat → M) :
    φ.Realize v := by
  induction h with
  | k φ ψ => exact fun hφ _ => hφ
  | s φ ψ χ => exact fun h₁ h₂ hφ => h₁ hφ (h₂ hφ)
  | classical φ => exact Classical.not_not.mp
  | allElim φ x t =>
      intro h
      exact (realize_substAt φ x t v).mpr ((realize_allAt φ x v).mp h (t.realize v))
  | allImp φ ψ x =>
      intro h₁ h₂
      apply (realize_allAt ψ x v).mpr
      intro a
      exact ((realize_allAt (φ.imp ψ) x v).mp h₁ a)
        ((realize_allAt φ x v).mp h₂ a)
  | vacuous φ x hx =>
      intro h
      apply (realize_allAt φ x v).mpr
      intro a
      exact (realize_update_of_not_free φ x hx v a).mpr h
  | eqRefl t => exact (FirstOrder.Language.Formula.realize_equal).mpr rfl
  | eqSubst φ x t u =>
      intro htu ht
      have e : t.realize v = u.realize v :=
        FirstOrder.Language.Formula.realize_equal.mp htu
      apply (realize_substAt φ x u v).mpr
      rw [← e]
      exact (realize_substAt φ x t v).mp ht

/-- Soundness is proved by induction on syntactic derivations and has no
theory-soundness assumption beyond the stated truth of individual axiom instances. -/
theorem derivation_sound {Axiom : Formula L → Prop}
    (hAxiom : ∀ φ, Axiom φ → ∀ v : Nat → M, φ.Realize v)
    {φ : Formula L} (h : Derivation Axiom φ) : ∀ v : Nat → M, φ.Realize v := by
  induction h with
  | «axiom» h => exact hAxiom _ h
  | logical h => exact logical_sound h
  | mp _ _ ih₁ ih₂ => exact fun v => ih₁ v (ih₂ v)
  | generalize x _ ih =>
      intro v
      exact (realize_allAt _ x v).mpr (fun a => ih (Function.update v x a))

end Soundness

/-- A sentence theory supplies exactly the canonical open embeddings of its
sentences as nonlogical axioms. -/
def SentenceAxiom (T : L.Sentence → Prop) (ψ : Formula L) : Prop :=
  ∃ φ, T φ ∧ openSentence φ = ψ

def Proves (T : L.Sentence → Prop) (φ : L.Sentence) : Prop :=
  Derivation (SentenceAxiom T) (openSentence φ)

theorem sentence_axiom {T : L.Sentence → Prop} {φ : L.Sentence} (h : T φ) :
    Proves T φ :=
  Derivation.axiom ⟨φ, h, rfl⟩

theorem theory_sound {M : Type u} [L.Structure M] [Inhabited M]
    {T : L.Sentence → Prop} (hT : ∀ φ, T φ → M ⊨ φ)
    {φ : L.Sentence} (h : Proves T φ) : M ⊨ φ := by
  have hA : ∀ ψ, SentenceAxiom T ψ → ∀ v : Nat → M, ψ.Realize v := by
    rintro ψ ⟨χ, hχ, rfl⟩ v
    exact (realize_openSentence χ v).mpr (hT χ hχ)
  exact (realize_openSentence φ (fun _ => default)).mp
    (derivation_sound hA h (fun _ => default))

theorem theory_consistent {M : Type u} [L.Structure M] [Inhabited M]
    {T : L.Sentence → Prop} (hT : ∀ φ, T φ → M ⊨ φ) :
    ¬Proves T (⊥ : L.Sentence) := by
  intro h
  exact theory_sound hT h

end PASoundness.FOL
