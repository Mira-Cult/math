import PASoundness.PeanoBetaCRTAlignment

/-! Transport of PA derivations through a finite free-name swap.
The transformation uses actual generalization and universal elimination;
it is independent of the intended AX8 instantiation. -/
namespace PASoundness.PeanoFreeNameSwap
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic

/-- Swap free variable names `x` and `y`; bound variables are untouched by
the capture-safe formula substitution. -/
def swapName (x y : Nat) (n : Nat) : Peano.Term :=
  if n = x then .var y else if n = y then .var x else .var n

private def substName (src dst : Nat) (n : Nat) : Peano.Term :=
  if n = src then .var dst else .var n

private theorem specialize (φ : Peano.Formula) (src dst : Nat)
    (h : FormulaProves φ) : FormulaProves (φ.subst (substName src dst)) := by
  exact .mp (.logical (.allElim φ src (.var dst))) (.generalize src h)

/-- Three single-name substitutions implement the swap on a formula when the
intermediate name is absent from its original free-variable set. -/
private theorem swap_syntax (φ : Peano.Formula) (x y z : Nat)
    (hxz : x ≠ z) (hyz : y ≠ z) (hf : z ∉ φ.freeVarFinset) :
    ((φ.subst (substName x z)).subst (substName y x)).subst (substName z y) =
      φ.subst (swapName x y) := by
  simp only [SyntaxTransport.formula_subst_comp]
  apply SyntaxTransport.formula_subst_agree
  intro n hn
  have hnz : n ≠ z := by intro h; subst n; exact hf hn
  by_cases hnx : n = x
  · subst n
    simp [substName, swapName, FirstOrder.Language.Term.subst, Ne.symm hyz]
  by_cases hny : n = y
  · subst n
    simp [substName, swapName, FirstOrder.Language.Term.subst, hnx, hxz]
  simp [substName, swapName, FirstOrder.Language.Term.subst, hnx, hny, hnz]

/-- A finite name swap transforms any explicit PA derivation into an actual
PA derivation of the capture-safe swapped formula. No semantic soundness or
unrestricted substitution-closure of PA axioms is assumed. -/
theorem swap_proves (φ : Peano.Formula) (x y : Nat) (h : FormulaProves φ) :
    FormulaProves (φ.subst (swapName x y)) := by
  let z := max (max x y) (φ.freeVarFinset.sup id) + 1
  have hxz : x ≠ z := by dsimp [z]; omega
  have hyz : y ≠ z := by dsimp [z]; omega
  have hf : z ∉ φ.freeVarFinset := by
    intro hz
    have hs : z ≤ φ.freeVarFinset.sup id := Finset.le_sup (f := id) hz
    dsimp [z] at hs
    omega
  have h1 := specialize φ x z h
  have h2 := specialize _ y x h1
  have h3 := specialize _ z y h2
  rw [swap_syntax φ x y z hxz hyz hf] at h3
  exact h3

end PASoundness.PeanoFreeNameSwap

#print axioms PASoundness.PeanoFreeNameSwap.swap_proves
