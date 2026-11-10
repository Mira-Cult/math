import PASoundness.PAtoCompactPAAddSuccNecessaryTLift
import PASoundness.PAtoCompactPAAddSuccNecessaryUTransport
import PASoundness.PAtoCompactUnaryGuardedCanonical

/-! The actual guarded PA addition-successor axiom entails existence of the
first argument's exact graph witness. This is finite K proof transformation,
not a semantic soundness argument. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddSuccNecessaryT
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactPAAddSuccNecessaryTLift PASoundness.PAtoCompactPAAddSuccNecessaryUTransport

/-- The actual equality frame entails precisely the first child graph
existence required by the constructive addition-successor axiom handler. -/
noncomputable def frame_to_t_graph (t u : Peano.Term) (q : Nat)
    (ht : ∀ a ∈ t.varFinset, a < q) (hu : ∀ a ∈ u.varFinset, a < q) :
    KDerivation (imp (equalityFrame id (Peano.add t (Peano.succ u))
      (Peano.succ (Peano.add t u)) q).encode
      (existsCode (q+1) (termGraph id t (q+1) (q+100)).encode)) := by
  have hn := frame_to_t_native t u q ht hu
  have htransport := existential_graph_transport id t (q+66) (q+100) (q+2) (q+1)
    (by omega) (by omega) (by omega)
    (by intro a ha; have := ht a ha; simp only [id_eq]; omega)
    (by intro a ha; have := ht a ha; simp only [id_eq]; omega)
    (by intro a ha; have := ht a ha; simp only [id_eq]; omega)
    (by intro a ha; have := ht a ha; simp only [id_eq]; omega)
  exact compose hn htransport

/-- A K proof of the guarded PA addition-successor axiom yields the precise
first-child graph-existence proof required by `add_succ_of_child_existence`. -/
noncomputable def guarded_t_of_add_succ (t u : Peano.Term)
    (h : KDerivation (guardedCode ((Peano.add t (Peano.succ u)).equal
      (Peano.succ (Peano.add t u))))) :
    let A := (Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))
    let q := guardBase A
    KDerivation (imp (guardFormula A).encode
      (existsCode (q+1) (termGraph id t (q+1) (q+100)).encode)) := by
  let L := Peano.add t (Peano.succ u)
  let R := Peano.succ (Peano.add t u)
  let A := L.equal R
  let q := guardBase A
  have hscope : q = scopeBase A Fin.elim0 := by simp [q, guardBase, scopeBase]
  have hfree : ∀ a ∈ A.freeVarFinset, a < q := by
    intro a ha
    have hh : a ≤ A.freeVarFinset.sup id := Finset.le_sup (f := id) ha
    dsimp [q, guardBase]
    omega
  have ht : ∀ a ∈ t.varFinset, a < q := by
    intro a ha
    apply hfree
    simp [A, L, R, Peano.add, Peano.succ, eq_free, Term.varFinset, ha]
  have hu : ∀ a ∈ u.varFinset, a < q := by
    intro a ha
    apply hfree
    simp [A, L, R, Peano.add, Peano.succ, eq_free, Term.varFinset, ha]
  have hg : KDerivation (imp (guardFormula A).encode (equalityFrame id L R q).encode) := by
    have hh := h
    unfold guardedCode code at hh
    rw [original_shape] at hh
    rw [← hscope] at hh
    exact hh
  exact compose hg (frame_to_t_graph t u q ht hu)

theorem guarded_t_of_add_succ_certificate (t u : Peano.Term)
    (h : KDerivation (guardedCode ((Peano.add t (Peano.succ u)).equal
      (Peano.succ (Peano.add t u))))) :
    let A := (Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))
    let q := guardBase A
    theoremCode (certificate (guarded_t_of_add_succ t u h)) =
      imp (guardFormula A).encode
        (existsCode (q+1) (termGraph id t (q+1) (q+100)).encode) := certificate_correct _
end PASoundness.PAtoCompactPAAddSuccNecessaryT
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryT.frame_to_t_graph
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryT.guarded_t_of_add_succ
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryT.guarded_t_of_add_succ_certificate
