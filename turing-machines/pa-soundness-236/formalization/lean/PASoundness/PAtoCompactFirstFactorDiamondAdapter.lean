import PASoundness.PAtoCompactGuardedEqualityDiamondAdapter
import PASoundness.PAtoCompactAllTermTransport

/-! A supplied first-factor arithmetic diamond proves the actual guarded PA
formula only when the caller also supplies its pointwise shared graph proof.
Neither input is constructed here. -/
namespace PASoundness.PAtoCompactFirstFactorDiamondAdapter

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactAllTermTransport
open PASoundness.PAtoCompactGuardedEqualityDiamondAdapter

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- From a supplied diamond package and a supplied implication to both
shared-output graphs at base q+100, derive the guarded first-factor formula.
The proof uses finite K graph-base conversions and no graph functionality. -/
noncomputable def guarded_first_successor (t u : Peano.Term) (body : Nat)
    (point : let left := Peano.mul (Peano.succ t) u
      let right := Peano.add (Peano.mul t u) u
      let A := left.equal right
      let q := guardBase A
      KDerivation (imp body (andF (termGraph id left q (q+100))
        (termGraph id right q (q+100))).encode))
    (package : let A := (Peano.mul (Peano.succ t) u).equal (Peano.add (Peano.mul t u) u)
      let q := guardBase A
      KDerivation (imp (guardFormula A).encode
        (existsCode (q+1) (existsCode (q+2) (existsCode (q+3)
          (existsCode (q+4) (existsCode q body))))))) :
    KDerivation (guardedCode ((Peano.mul (Peano.succ t) u).equal (Peano.add (Peano.mul t u) u))) := by
  let left := Peano.mul (Peano.succ t) u
  let right := Peano.add (Peano.mul t u) u
  let A := left.equal right
  let q := guardBase A
  let e := q+100
  have hscope : q = scopeBase A Fin.elim0 := by simp [q, guardBase, scopeBase]
  have hl : ∀ a ∈ left.varFinset, a < q := by
    intro a ha
    have hf : a ∈ A.freeVarFinset := by
      simp only [A, eq_free, Finset.mem_union]
      exact Or.inl ha
    have hh := free_lt_scopeBase A Fin.elim0 a hf
    omega
  have hr : ∀ a ∈ right.varFinset, a < q := by
    intro a ha
    have hf : a ∈ A.freeVarFinset := by
      simp only [A, eq_free, Finset.mem_union]
      exact Or.inr ha
    have hh := free_lt_scopeBase A Fin.elim0 a hf
    omega
  have hL := (termGraph_base_transport id left e (q+2) q (by dsimp [e]; omega)
    (by omega) (by intro a ha; have := hl a ha; simp only [id_eq]; dsimp [e]; omega)
    (by intro a ha; have := hl a ha; simp only [id_eq]; omega)).1
  have hR := (termGraph_base_transport id right e (q+2+termCost left) q
    (by dsimp [e]; omega) (by omega)
    (by intro a ha; have := hr a ha; simp only [id_eq]; dsimp [e]; omega)
    (by intro a ha; have := hr a ha; simp only [id_eq]; omega)).1
  have hpoint : KDerivation (imp body (andF (termGraph id left q (q+2))
      (termGraph id right q (q+2+termCost left))).encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    let Γ := [body]
    have hb : Context Γ body := .head _ _
    have hsource : Context Γ (both (termGraph id left q e).encode
        (termGraph id right q e).encode) := by
      have h := Context.mp hb (.closed point)
      simpa [A, q, e, left, right, andF, CompactNamed.Formula.not, Formula.encode, both, neg] using h
    have hleft := Context.mp (Context.conjunctionLeft hsource) (.closed hL)
    have hright := Context.mp (Context.conjunctionRight hsource) (.closed hR)
    have h := Context.conjunctionIntro hleft hright
    simpa [andF, CompactNamed.Formula.not, Formula.encode, both, neg] using h
  exact guarded_of_diamond left right body hpoint package

end PASoundness.PAtoCompactFirstFactorDiamondAdapter

#print axioms PASoundness.PAtoCompactFirstFactorDiamondAdapter.guarded_first_successor
