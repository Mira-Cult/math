import PASoundness.Peano
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff

/-!
# The bounded sentence and polynomial witness from the observer counterexample

This formalizes the actual closed sentence

  exists x, 0 < x and forall y <= x, x != y+y and x != y+y+1,

its explicit bounded-matrix syntax, its falsity in standard Nat, and its
truth in Nat[X] with eventual order. Consequently its bare singleton theory
is consistent and proves a standard-false existential bounded sentence.

The companion `PolynomialSpecialization` module proves that all existential
quantifier-free consequences of this singleton theory are standardly true.
Its finite-specialization proof closes the recovered separation for those
explicit syntactic sentence classes. No global impossibility claim about
observers is made.
-/

namespace PASoundness.HierarchyCounterexample

open FirstOrder FirstOrder.Language

inductive RelationSymbol : Nat → Type
  | lt : RelationSymbol 2
  deriving DecidableEq

def language : Language where
  Functions := Peano.FunctionSymbol
  Relations := RelationSymbol

abbrev Term (n : Nat) := language.Term (Empty ⊕ Fin n)
abbrev Formula (n : Nat) := language.BoundedFormula Empty n
abbrev Sentence := language.Sentence

def zero {n : Nat} : Term n := .func .zero Fin.elim0
def succ {n : Nat} (t : Term n) : Term n := .func .succ ![t]
def add {n : Nat} (t u : Term n) : Term n := .func .add ![t,u]
def lt {n : Nat} (t u : Term n) : Formula n := .rel .lt ![t,u]
def le {n : Nat} (t u : Term n) : Formula n := lt t u ⊔ t.bdEqual u

def lift {n : Nat} (t : Term n) : Term (n+1) :=
  t.relabel (Sum.map id Fin.castSucc)

/-- The bound term is in the *old* scope. The newly bound variable cannot
occur in its own bound, by the types of the term and the scope lift. -/
def boundedAll {n : Nat} (bound : Term n) (body : Formula (n+1)) : Formula n :=
  .all ((le (.var (.inr (Fin.last n))) (lift bound)).imp body)

/-- A transparent syntactic bounded-arithmetic fragment. It contains only
atoms, Boolean connectives, and syntactically bounded universal quantifiers. -/
inductive BoundedArithmetic : {n : Nat} → Formula n → Prop
  | equal {n} (t u : Term n) : BoundedArithmetic (.equal t u)
  | less {n} (t u : Term n) : BoundedArithmetic (lt t u)
  | falsum {n} : BoundedArithmetic (.falsum : Formula n)
  | neg {n} {φ : Formula n} : BoundedArithmetic φ → BoundedArithmetic φ.not
  | conj {n} {φ ψ : Formula n} : BoundedArithmetic φ → BoundedArithmetic ψ →
      BoundedArithmetic (φ ⊓ ψ)
  | disj {n} {φ ψ : Formula n} : BoundedArithmetic φ → BoundedArithmetic ψ →
      BoundedArithmetic (φ ⊔ ψ)
  | imp {n} {φ ψ : Formula n} : BoundedArithmetic φ → BoundedArithmetic ψ →
      BoundedArithmetic (φ.imp ψ)
  | boundedAll {n} (bound : Term n) {body : Formula (n+1)} :
      BoundedArithmetic body → BoundedArithmetic (boundedAll bound body)

def matrix : Formula 1 :=
  (lt zero (.var (.inr 0))) ⊓
    boundedAll (.var (.inr 0))
      (((.var (.inr 0) : Term 2).bdEqual (add (.var (.inr 1)) (.var (.inr 1)))).not ⊓
        ((.var (.inr 0) : Term 2).bdEqual
          (succ (add (.var (.inr 1)) (.var (.inr 1))))).not)

def sentence : Sentence := matrix.ex

theorem matrix_bounded : BoundedArithmetic matrix :=
  .conj (.less _ _) (.boundedAll _ (.conj (.neg (.equal _ _)) (.neg (.equal _ _))))

/-- A single existential quantifier over this bounded syntax, a concrete
syntactic Sigma_1 subclass. This is not the legacy observer's singleton rank. -/
def ExistsBounded (φ : Sentence) : Prop :=
  ∃ body : Formula 1, BoundedArithmetic body ∧ φ = body.ex

theorem sentence_existsBounded : ExistsBounded sentence := ⟨matrix, matrix_bounded, rfl⟩

instance natStructure : language.Structure Nat where
  funMap := fun {_n} f v => match f with
    | .zero => 0
    | .succ => Nat.succ (v 0)
    | .add => v 0 + v 1
    | .mul => v 0 * v 1
  RelMap := fun {_n} r v => match r with
    | .lt => v 0 < v 1

@[simp] theorem nat_fun_zero (v : Fin 0 → Nat) :
    Structure.funMap (L := language) Peano.FunctionSymbol.zero v = 0 := rfl
@[simp] theorem nat_fun_succ (v : Fin 1 → Nat) :
    Structure.funMap (L := language) Peano.FunctionSymbol.succ v = Nat.succ (v 0) := rfl
@[simp] theorem nat_fun_add (v : Fin 2 → Nat) :
    Structure.funMap (L := language) Peano.FunctionSymbol.add v = v 0 + v 1 := rfl
@[simp] theorem nat_rel_lt (v : Fin 2 → Nat) :
    Structure.RelMap (L := language) RelationSymbol.lt v ↔ v 0 < v 1 := Iff.rfl

theorem sentence_nat_iff : Nat ⊨ sentence ↔
    ∃ x : Nat, 0 < x ∧ ∀ y : Nat, (y < x ∨ y = x) →
      x ≠ y+y ∧ x ≠ Nat.succ (y+y) := by
  classical
  simp [sentence, matrix, boundedAll, le, lt, zero, succ, add, lift,
    FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize,
    BoundedFormula.Realize, FirstOrder.Language.Term.realize, Fin.snoc]

theorem sentence_false_nat : ¬ Nat ⊨ sentence := by
  rw [sentence_nat_iff]
  rintro ⟨x, _, h⟩
  have hle := Nat.div_le_self x 2
  have hbound : x/2 < x ∨ x/2 = x := by omega
  obtain ⟨heven, hodd⟩ := h (x/2) hbound
  have hm := Nat.mod_lt x (by decide : 0 < 2)
  have hd := Nat.mod_add_div x 2
  omega

/-- Eventual polynomial order is a semantic relation of the control model,
not a primitive available to the soundness observer. -/
def EventuallyLt (p q : Polynomial Nat) : Prop :=
  ∃ bound : Nat, ∀ m : Nat, bound ≤ m → p.eval m < q.eval m

noncomputable instance polynomialStructure : language.Structure (Polynomial Nat) where
  funMap := fun {_n} f v => match f with
    | .zero => 0
    | .succ => v 0 + 1
    | .add => v 0 + v 1
    | .mul => v 0 * v 1
  RelMap := fun {_n} r v => match r with
    | .lt => EventuallyLt (v 0) (v 1)

@[simp] theorem polynomial_fun_zero (v : Fin 0 → Polynomial Nat) :
    Structure.funMap (L := language) Peano.FunctionSymbol.zero v = 0 := rfl
@[simp] theorem polynomial_fun_succ (v : Fin 1 → Polynomial Nat) :
    Structure.funMap (L := language) Peano.FunctionSymbol.succ v = v 0 + 1 := rfl
@[simp] theorem polynomial_fun_add (v : Fin 2 → Polynomial Nat) :
    Structure.funMap (L := language) Peano.FunctionSymbol.add v = v 0 + v 1 := rfl
@[simp] theorem polynomial_rel_lt (v : Fin 2 → Polynomial Nat) :
    Structure.RelMap (L := language) RelationSymbol.lt v ↔ EventuallyLt (v 0) (v 1) := Iff.rfl

theorem sentence_polynomial_iff : (Polynomial Nat) ⊨ sentence ↔
    ∃ x : Polynomial Nat, EventuallyLt 0 x ∧
      ∀ y : Polynomial Nat, (EventuallyLt y x ∨ y = x) →
        x ≠ y+y ∧ x ≠ y+y+1 := by
  classical
  simp [sentence, matrix, boundedAll, le, lt, zero, succ, add, lift,
    FirstOrder.Language.Sentence.Realize, FirstOrder.Language.Formula.Realize,
    BoundedFormula.Realize, FirstOrder.Language.Term.realize, Fin.snoc]

theorem zero_eventually_lt_X : EventuallyLt 0 Polynomial.X := by
  refine ⟨1, ?_⟩
  intro m hm
  simp only [Polynomial.eval_zero, Polynomial.eval_X]
  omega

/-- The X coefficient is one; the X coefficient of twice any natural
polynomial is even. The conclusion holds without a bounded-order premise. -/
theorem X_ne_double (p : Polynomial Nat) : Polynomial.X ≠ p+p := by
  intro h
  have hc := congrArg (fun q : Polynomial Nat => q.coeff 1) h
  simp at hc
  omega

theorem X_ne_double_add_one (p : Polynomial Nat) : Polynomial.X ≠ p+p+1 := by
  intro h
  have hc := congrArg (fun q : Polynomial Nat => q.coeff 1) h
  simp [Polynomial.coeff_one] at hc
  omega

/-- A concrete model and witness for the exact recovered sentence. -/
theorem sentence_true_polynomial : (Polynomial Nat) ⊨ sentence := by
  apply sentence_polynomial_iff.mpr
  exact ⟨Polynomial.X, zero_eventually_lt_X,
    fun p _ => ⟨X_ne_double p, X_ne_double_add_one p⟩⟩

def theory : Sentence → Prop := fun φ => φ = sentence

theorem consistent : ¬ FOL.Proves theory (⊥ : Sentence) := by
  apply FOL.theory_consistent (M := Polynomial Nat)
  intro φ hφ
  cases hφ
  exact sentence_true_polynomial

theorem proves_sentence : FOL.Proves theory sentence := FOL.sentence_axiom rfl

/-- The completed bounded scope: a consistent bare first-order theory with
a proved standard-false existential bounded sentence. No qf-preservation
conclusion is part of this theorem. -/
theorem consistent_bounded_unsound :
    (¬ FOL.Proves theory (⊥ : Sentence)) ∧
    ∃ φ : Sentence, ExistsBounded φ ∧ FOL.Proves theory φ ∧ ¬ Nat ⊨ φ :=
  ⟨consistent, sentence, sentence_existsBounded, proves_sentence, sentence_false_nat⟩

end PASoundness.HierarchyCounterexample
