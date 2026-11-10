import PASoundness.FOL

/-!
# First-order Peano arithmetic and its standard model

This is PA in the signature `0, S, +, *`, with logical equality. The nonlogical
axioms are the usual six arithmetic axiom schemas and the full first-order
induction schema. All free variables other than the induction variable are
parameters. Provability is the syntactic Hilbert derivation relation from FOL.
The standard-model theorem is proved in Lean's metatheory, not internally in PA.
-/

namespace PASoundness.Peano

open FirstOrder FirstOrder.Language

inductive FunctionSymbol : Nat → Type
  | zero : FunctionSymbol 0
  | succ : FunctionSymbol 1
  | add : FunctionSymbol 2
  | mul : FunctionSymbol 2
  deriving DecidableEq

def language : Language where
  Functions := FunctionSymbol
  Relations := fun _ => Empty

abbrev Term := language.Term Nat
abbrev Formula := language.Formula Nat
abbrev Sentence := language.Sentence

def zero : Term := .func FunctionSymbol.zero Fin.elim0
def succ (t : Term) : Term := .func FunctionSymbol.succ ![t]
def add (t u : Term) : Term := .func FunctionSymbol.add ![t, u]
def mul (t u : Term) : Term := .func FunctionSymbol.mul ![t, u]

instance natStructure : language.Structure Nat where
  funMap := fun {_n} f v => match f with
    | .zero => 0
    | .succ => Nat.succ (v 0)
    | .add => v 0 + v 1
    | .mul => v 0 * v 1
  RelMap := fun {_} r => Empty.elim r

@[simp] theorem realize_zero (v : Nat → Nat) : zero.realize v = 0 := rfl
@[simp] theorem realize_succ (t : Term) (v : Nat → Nat) :
    (succ t).realize v = Nat.succ (t.realize v) := rfl
@[simp] theorem realize_add (t u : Term) (v : Nat → Nat) :
    (add t u).realize v = t.realize v + u.realize v := rfl
@[simp] theorem realize_mul (t u : Term) (v : Nat → Nat) :
    (mul t u).realize v = t.realize v * u.realize v := rfl

/-- The induction instance for an arbitrary first-order formula. Parameters
remain free, and hence are universally interpreted in the proof calculus. -/
def inductionAxiom (φ : Formula) (x : Nat) : Formula :=
  (FOL.substAt φ x zero).imp
    ((FOL.allAt x (φ.imp (FOL.substAt φ x (succ (.var x))))).imp (FOL.allAt x φ))

/-- Genuine syntactic PA nonlogical axioms, not a predicate defined by truth. -/
inductive Axiom : Formula → Prop
  | succ_ne_zero (t : Term) : Axiom ((succ t).equal zero).not
  | succ_injective (t u : Term) : Axiom (((succ t).equal (succ u)).imp (t.equal u))
  | add_zero (t : Term) : Axiom ((add t zero).equal t)
  | add_succ (t u : Term) : Axiom ((add t (succ u)).equal (succ (add t u)))
  | mul_zero (t : Term) : Axiom ((mul t zero).equal zero)
  | mul_succ (t u : Term) : Axiom ((mul t (succ u)).equal (add (mul t u) t))
  | induction (φ : Formula) (x : Nat) : Axiom (inductionAxiom φ x)

theorem inductionAxiom_true (φ : Formula) (x : Nat) (v : Nat → Nat) :
    (inductionAxiom φ x).Realize v := by
  intro hzero hsucc
  apply (FOL.realize_allAt φ x v).mpr
  intro n
  induction n with
  | zero =>
      exact (FOL.realize_substAt φ x zero v).mp hzero
  | succ n ih =>
      have hstep := (FOL.realize_allAt
        (φ.imp (FOL.substAt φ x (succ (.var x)))) x v).mp hsucc n
      have hn := (FOL.realize_substAt φ x (succ (.var x))
        (Function.update v x n)).mp (hstep ih)
      simpa using hn

/-- Every PA axiom is true in the standard natural numbers, including every
induction instance with arbitrary parameters. -/
theorem axiom_true {φ : Formula} (h : Axiom φ) (v : Nat → Nat) : φ.Realize v := by
  cases h with
  | succ_ne_zero t =>
      simp only [FirstOrder.Language.Formula.realize_not,
        FirstOrder.Language.Formula.realize_equal, realize_succ, realize_zero]
      exact Nat.succ_ne_zero _
  | succ_injective t u =>
      simp only [FirstOrder.Language.Formula.realize_imp,
        FirstOrder.Language.Formula.realize_equal, realize_succ]
      exact Nat.succ.inj
  | add_zero t =>
      simp only [FirstOrder.Language.Formula.realize_equal, realize_add, realize_zero,
        Nat.add_zero]
  | add_succ t u =>
      simp only [FirstOrder.Language.Formula.realize_equal, realize_add, realize_succ,
        Nat.add_succ]
  | mul_zero t =>
      simp only [FirstOrder.Language.Formula.realize_equal, realize_mul, realize_zero,
        Nat.mul_zero]
  | mul_succ t u =>
      simp only [FirstOrder.Language.Formula.realize_equal, realize_mul, realize_succ,
        realize_add, Nat.mul_succ]
  | induction φ x => exact inductionAxiom_true φ x v

abbrev FormulaProves (φ : Formula) : Prop := FOL.Derivation Axiom φ

/-- PA syntactically proves the sentence, using the explicit nonlogical axioms
and the explicit first-order Hilbert calculus. -/
def Proves (φ : Sentence) : Prop := FormulaProves (FOL.openSentence φ)

theorem formula_soundness {φ : Formula} (h : FormulaProves φ) (v : Nat → Nat) :
    φ.Realize v :=
  FOL.derivation_sound (fun _ ha w => axiom_true ha w) h v

/-- Closed standard-model soundness of genuine first-order Peano arithmetic.
This theorem assumes no soundness or consistency proposition about PA. -/
theorem soundness (φ : Sentence) (h : Proves φ) : Nat ⊨ φ :=
  (FOL.realize_openSentence φ (fun _ => 0)).mp (formula_soundness h (fun _ => 0))

theorem consistent : ¬Proves (⊥ : Sentence) := by
  intro h
  exact soundness _ h

end PASoundness.Peano
