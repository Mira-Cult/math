import PASoundness.Peano
import Mathlib.Tactic.FinCases

/-! Syntactic reversal of multiplication operands in PA terms and formulas.
This module proves an involution on syntax only. It does not construct a PA or
compact-calculus proof translation, or claim multiplication commutativity. -/

namespace PASoundness.PAtoCompactMulReversalSyntax

open FirstOrder FirstOrder.Language

/-- Recursively reverse the operands of every multiplication symbol, leaving
all variables and other function symbols in place. -/
def reverseTerm {α : Type} : Peano.language.Term α → Peano.language.Term α
  | .var x => .var x
  | .func .zero _ => .func .zero Fin.elim0
  | .func .succ ts => .func .succ (fun i => reverseTerm (ts i))
  | .func .add ts => .func .add (fun i => reverseTerm (ts i))
  | .func .mul ts => .func .mul (fun i => reverseTerm (ts i.rev))

@[simp] theorem reverseTerm_var {α : Type} (x : α) :
    reverseTerm (.var x : Peano.language.Term α) = .var x := rfl

@[simp] theorem reverseTerm_zero : reverseTerm Peano.zero = Peano.zero := rfl

@[simp] theorem reverseTerm_succ (t : Peano.Term) :
    reverseTerm (Peano.succ t) = Peano.succ (reverseTerm t) := by
  change Term.func Peano.FunctionSymbol.succ (fun i => reverseTerm (![t] i)) = _
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem reverseTerm_add (t u : Peano.Term) :
    reverseTerm (Peano.add t u) = Peano.add (reverseTerm t) (reverseTerm u) := by
  change Term.func Peano.FunctionSymbol.add (fun i => reverseTerm (![t, u] i)) = _
  congr 1
  funext i
  fin_cases i <;> rfl

@[simp] theorem reverseTerm_mul (t u : Peano.Term) :
    reverseTerm (Peano.mul t u) = Peano.mul (reverseTerm u) (reverseTerm t) := by
  change Term.func Peano.FunctionSymbol.mul (fun i => reverseTerm (![t, u] i.rev)) = _
  congr 1
  funext i
  fin_cases i <;> rfl

/-- The reversal works uniformly for free and bound variable types. -/
@[simp] theorem reverseTerm_involutive {α : Type} (t : Peano.language.Term α) :
    reverseTerm (reverseTerm t) = t := by
  induction t with
  | var x => rfl
  | @func n symbol ts ih =>
      cases symbol with
      | zero =>
          change Term.func Peano.FunctionSymbol.zero Fin.elim0 = Term.func Peano.FunctionSymbol.zero ts
          congr 1
          funext i
          exact Fin.elim0 i
      | succ =>
          change Term.func Peano.FunctionSymbol.succ (fun i => reverseTerm (reverseTerm (ts i))) = Term.func Peano.FunctionSymbol.succ ts
          congr 1
          funext i
          exact ih i
      | add =>
          change Term.func Peano.FunctionSymbol.add (fun i => reverseTerm (reverseTerm (ts i))) = Term.func Peano.FunctionSymbol.add ts
          congr 1
          funext i
          exact ih i
      | mul =>
          change Term.func Peano.FunctionSymbol.mul (fun i => reverseTerm (reverseTerm (ts i.rev.rev))) = Term.func Peano.FunctionSymbol.mul ts
          congr 1
          funext i
          simpa only [Fin.rev_rev] using ih i

/-- Reverse terms at each equality leaf of a locally nameless formula. The
quantifier scope and its de Bruijn indices are unchanged. -/
def reverseBounded {α : Type} : (n : Nat) →
    Peano.language.BoundedFormula α n → Peano.language.BoundedFormula α n
  | _, .falsum => .falsum
  | _, .equal t u => .equal (reverseTerm t) (reverseTerm u)
  | _, .rel r _ => nomatch r
  | n, .imp φ ψ => .imp (reverseBounded n φ) (reverseBounded n ψ)
  | n, .all φ => .all (reverseBounded (n+1) φ)

@[simp] theorem reverseBounded_falsum {α : Type} {n : Nat} :
    reverseBounded n (.falsum : Peano.language.BoundedFormula α n) = .falsum := rfl

@[simp] theorem reverseBounded_equal {α : Type} {n : Nat}
    (t u : Peano.language.Term (α ⊕ Fin n)) :
    reverseBounded n (.equal t u) = .equal (reverseTerm t) (reverseTerm u) := rfl

@[simp] theorem reverseBounded_imp {α : Type} {n : Nat}
    (φ ψ : Peano.language.BoundedFormula α n) :
    reverseBounded n (.imp φ ψ) = .imp (reverseBounded n φ) (reverseBounded n ψ) := rfl

@[simp] theorem reverseBounded_all {α : Type} {n : Nat}
    (φ : Peano.language.BoundedFormula α (n+1)) :
    reverseBounded n (.all φ) = .all (reverseBounded (n+1) φ) := rfl

/-- Reversing twice returns exactly the original PA syntax. -/
@[simp] theorem reverseBounded_involutive {α : Type} {n : Nat}
    (φ : Peano.language.BoundedFormula α n) :
    reverseBounded n (reverseBounded n φ) = φ := by
  induction φ with
  | falsum => rfl
  | equal t u => simp only [reverseBounded_equal, reverseTerm_involutive]
  | rel r ts => exact nomatch r
  | imp φ ψ ihφ ihψ => simp only [reverseBounded_imp, ihφ, ihψ]
  | all φ ih => simp only [reverseBounded_all, ih]

end PASoundness.PAtoCompactMulReversalSyntax

#print axioms PASoundness.PAtoCompactMulReversalSyntax.reverseTerm
#print axioms PASoundness.PAtoCompactMulReversalSyntax.reverseTerm_involutive
#print axioms PASoundness.PAtoCompactMulReversalSyntax.reverseBounded
#print axioms PASoundness.PAtoCompactMulReversalSyntax.reverseBounded_involutive
