import PASoundness.PAtoCompactMulZeroAxiomFrameShared
import PASoundness.PAtoCompactGuardedDirectBridge

/-! A shared term-graph witness yields the guarded PA addition-zero axiom.
The existence of such a witness remains an explicit finite K proof input. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddZeroFrameBridge

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactMulZeroAxiomFrameShared

/-- A jointly existing output of `t + 0` and `t` proves their actual guarded
PA equality. This does not assert existence of a common output. -/
noncomputable def add_zero_of_shared (t : Peano.Term)
    (joint : let a := Peano.add t Peano.zero
      let A := a.equal t
      let b := guardBase A
      KDerivation (imp (guardFormula A).encode
        (existsCode b (andF (termGraph id a b (b+2))
          (termGraph id t b (b+2+termCost a))).encode))) :
    KDerivation (guardedCode ((Peano.add t Peano.zero).equal t)) := by
  let a := Peano.add t Peano.zero
  let A := a.equal t
  let b := guardBase A
  have hscope : b = scopeBase A Fin.elim0 := by simp [b, guardBase, scopeBase]
  have ha : ∀ z ∈ a.varFinset, z < b := by
    intro z hz
    have hf : z ∈ A.freeVarFinset := by
      simp only [A, eq_free, Finset.mem_union]
      exact Or.inl hz
    have hh := free_lt_scopeBase A Fin.elim0 z hf
    omega
  have ht : ∀ z ∈ t.varFinset, z < b := by
    intro z hz
    have hf : z ∈ A.freeVarFinset := by
      simp only [A, eq_free, Finset.mem_union]
      exact Or.inr hz
    have hh := free_lt_scopeBase A Fin.elim0 z hf
    omega
  have hframe := shared_graphs_to_frame a t b ha ht
  have h := compose joint hframe
  unfold guardedCode code
  rw [original_shape]
  change KDerivation (imp (guardFormula A).encode
    (equalityFrame id a t (scopeBase A Fin.elim0)).encode)
  rw [← hscope]
  exact h

theorem add_zero_of_shared_certificate (t : Peano.Term)
    (joint : let a := Peano.add t Peano.zero
      let A := a.equal t
      let b := guardBase A
      KDerivation (imp (guardFormula A).encode
        (existsCode b (andF (termGraph id a b (b+2))
          (termGraph id t b (b+2+termCost a))).encode))) :
    theoremCode (certificate (add_zero_of_shared t joint)) =
      guardedCode ((Peano.add t Peano.zero).equal t) := certificate_correct _

end PASoundness.PAtoCompactPAAddZeroFrameBridge
#print axioms PASoundness.PAtoCompactPAAddZeroFrameBridge.add_zero_of_shared
#print axioms PASoundness.PAtoCompactPAAddZeroFrameBridge.add_zero_of_shared_certificate
