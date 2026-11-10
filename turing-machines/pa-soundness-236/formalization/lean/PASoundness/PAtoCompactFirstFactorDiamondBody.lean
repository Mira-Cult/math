import PASoundness.PAtoCompactFirstFactorDiamondAdapter
import PASoundness.PAtoCompactFirstFactorSharedGraphPoint

/-! An explicit first-factor arithmetic diamond, projected into both actual
term graphs and then into the guarded PA formula. The guarded existence of the
whole package remains an explicit K proof input. -/
namespace PASoundness.PAtoCompactFirstFactorDiamondBody

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactTermZeroGuarded
open PASoundness.PAtoCompactFirstFactorSharedGraphPoint PASoundness.PAtoCompactFirstFactorDiamondAdapter

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Nine conjuncts retain the same witnesses across both arithmetic paths. -/
def diamond (t u : Peano.Term) (q : Nat) : Nat :=
  let e := q+100
  let x := q+1
  let y := q+2
  let p := q+3
  let sx := q+4
  both (domainAt e sx).encode (both (domainAt e p).encode
    (both (domainAt e q).encode (both (termGraph id t x e).encode
      (both (termGraph id u y e).encode (both (succAt e x sx).encode
        (both (mulAt e x y p).encode (both (addAt e p y q).encode
          (mulAt e sx y q).encode)))))))

/-- The displayed diamond yields both actual term graphs at its same output.
This implication does not assert that any diamond witnesses exist. -/
noncomputable def graphs_of_diamond (t u : Peano.Term) :
    let left := Peano.mul (Peano.succ t) u
    let right := Peano.add (Peano.mul t u) u
    let A := left.equal right
    let q := guardBase A
    KDerivation (imp (diamond t u q) (andF (termGraph id left q (q+100))
      (termGraph id right q (q+100))).encode) := by
  let left := Peano.mul (Peano.succ t) u
  let right := Peano.add (Peano.mul t u) u
  let A := left.equal right
  let q := guardBase A
  let e := q+100
  let x := q+1
  let y := q+2
  let p := q+3
  let sx := q+4
  have ht : ∀ a ∈ t.varFinset, id a < e := by
    intro a ha
    have hf : a ∈ A.freeVarFinset := by
      simp [A, left, right, Peano.mul, Peano.add, Peano.succ, eq_free, Term.varFinset, ha]
    have hh : a ≤ A.freeVarFinset.sup id := Finset.le_sup (f := id) hf
    dsimp [e, q, guardBase]
    omega
  have hu : ∀ a ∈ u.varFinset, id a < e := by
    intro a ha
    have hf : a ∈ A.freeVarFinset := by
      simp [A, left, right, Peano.mul, Peano.add, Peano.succ, eq_free, Term.varFinset, ha]
    have hh : a ≤ A.freeVarFinset.sup id := Finset.le_sup (f := id) hf
    dsimp [e, q, guardBase]
    omega
  have hpoint := shared_graphs id t u e x y sx p q
    (by dsimp [e,x]; omega) (by dsimp [e,y]; omega) (by dsimp [e,sx]; omega)
    (by dsimp [e,p]; omega) (by dsimp [e]; omega) ht hu
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [diamond t u q]
  have h := Context.head [] (diamond t u q)
  have hSX := Context.conjunctionLeft h
  have h₁ := Context.conjunctionRight h
  have hP := Context.conjunctionLeft h₁
  have h₂ := Context.conjunctionRight h₁
  have hQ := Context.conjunctionLeft h₂
  have h₃ := Context.conjunctionRight h₂
  have hT := Context.conjunctionLeft h₃
  have h₄ := Context.conjunctionRight h₃
  have hU := Context.conjunctionLeft h₄
  have h₅ := Context.conjunctionRight h₄
  have hS := Context.conjunctionLeft h₅
  have h₆ := Context.conjunctionRight h₅
  have hOld := Context.conjunctionLeft h₆
  have h₇ := Context.conjunctionRight h₆
  have hAdd := Context.conjunctionLeft h₇
  have hNew := Context.conjunctionRight h₇
  have hresult := Context.mp hNew (Context.mp hAdd (Context.mp hOld (Context.mp hS
    (Context.mp hU (Context.mp hT (Context.mp hQ (Context.mp hP
      (Context.mp hSX (.closed hpoint)))))))))
  change Context Γ (andF (termGraph id left q e) (termGraph id right q e)).encode
  simpa only [left, right, Peano.mul, Peano.add, Peano.succ, binaryTerm,
    Bool.false_eq_true, ↓reduceIte] using hresult

/-- The guarded first-factor successor formula follows from the explicit
finite K proof that the displayed shared diamond has witnesses. This theorem
does not construct that package. -/
noncomputable def guarded_first_successor_of_diamond (t u : Peano.Term)
    (package : let A := (Peano.mul (Peano.succ t) u).equal (Peano.add (Peano.mul t u) u)
      let q := guardBase A
      KDerivation (imp (guardFormula A).encode
        (existsCode (q+1) (existsCode (q+2) (existsCode (q+3)
          (existsCode (q+4) (existsCode q (diamond t u q)))))))) :
    KDerivation (guardedCode ((Peano.mul (Peano.succ t) u).equal (Peano.add (Peano.mul t u) u))) := by
  exact guarded_first_successor t u _ (graphs_of_diamond t u) package

end PASoundness.PAtoCompactFirstFactorDiamondBody

#print axioms PASoundness.PAtoCompactFirstFactorDiamondBody.diamond
#print axioms PASoundness.PAtoCompactFirstFactorDiamondBody.graphs_of_diamond
#print axioms PASoundness.PAtoCompactFirstFactorDiamondBody.guarded_first_successor_of_diamond
