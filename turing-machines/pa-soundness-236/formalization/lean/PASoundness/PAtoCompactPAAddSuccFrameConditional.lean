import PASoundness.PAtoCompactMulZeroAxiomFrameShared
import PASoundness.PAtoCompactGuardedBridge

/-! A finite-K equality-frame adapter for the PA addition-successor axiom.
The common output witness remains an explicit proof-data input. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddSuccFrameConditional

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactMulZeroAxiomFrameShared

/-- A shared-value proof for the two actual term graphs supplies the literal
guarded PA addition-successor axiom. This adapter does not assert that such a
witness exists. -/
noncomputable def add_succ_of_shared (t u : Peano.Term)
    (shared : let left := Peano.add t (Peano.succ u)
      let right := Peano.succ (Peano.add t u)
      let A := left.equal right
      let b := guardBase A
      KDerivation (imp (guardFormula A).encode
        (existsCode b (andF (termGraph id left b (b+2))
          (termGraph id right b (b+2+termCost left))).encode))) :
    KDerivation (guardedCode ((Peano.add t (Peano.succ u)).equal
      (Peano.succ (Peano.add t u)))) := by
  let left := Peano.add t (Peano.succ u)
  let right := Peano.succ (Peano.add t u)
  let A := left.equal right
  let b := guardBase A
  have hscope : b = scopeBase A Fin.elim0 := by simp [b, guardBase, scopeBase]
  have hl : ∀ a ∈ left.varFinset, a < b := by
    intro a ha
    have hfree : a ∈ A.freeVarFinset := by
      simp only [A, eq_free, Finset.mem_union]
      exact Or.inl ha
    have hh := free_lt_scopeBase A Fin.elim0 a hfree
    omega
  have hr : ∀ a ∈ right.varFinset, a < b := by
    intro a ha
    have hfree : a ∈ A.freeVarFinset := by
      simp only [A, eq_free, Finset.mem_union]
      exact Or.inr ha
    have hh := free_lt_scopeBase A Fin.elim0 a hfree
    omega
  have hframe := shared_graphs_to_frame left right b hl hr
  have h := compose shared hframe
  unfold guardedCode code
  rw [original_shape]
  change KDerivation (imp (guardFormula A).encode
    (equalityFrame id left right (scopeBase A Fin.elim0)).encode)
  rw [← hscope]
  exact h

theorem add_succ_of_shared_certificate (t u : Peano.Term)
    (shared : let left := Peano.add t (Peano.succ u)
      let right := Peano.succ (Peano.add t u)
      let A := left.equal right
      let b := guardBase A
      KDerivation (imp (guardFormula A).encode
        (existsCode b (andF (termGraph id left b (b+2))
          (termGraph id right b (b+2+termCost left))).encode))) :
    theoremCode (certificate (add_succ_of_shared t u shared)) =
      guardedCode ((Peano.add t (Peano.succ u)).equal
        (Peano.succ (Peano.add t u))) := certificate_correct _

end PASoundness.PAtoCompactPAAddSuccFrameConditional

#print axioms PASoundness.PAtoCompactPAAddSuccFrameConditional.add_succ_of_shared
#print axioms PASoundness.PAtoCompactPAAddSuccFrameConditional.add_succ_of_shared_certificate
