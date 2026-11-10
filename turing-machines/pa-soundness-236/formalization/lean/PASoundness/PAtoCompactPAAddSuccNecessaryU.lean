import PASoundness.PAtoCompactPAAddZeroNecessityFrame
import PASoundness.PAtoCompactPAAddSuccNecessaryUExtract
import PASoundness.PAtoCompactPAAddSuccNecessaryUTransport
import PASoundness.PAtoCompactVacuousEqualityAlignment
import PASoundness.PAtoCompactUnaryGuardedCanonical

/-! The guarded PA addition-successor axiom supplies the graph of its second
argument. This is a finite-K proof-data projection, not a semantic argument. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPAAddSuccNecessaryU
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactPAAddZeroNecessityFrame PASoundness.PAtoCompactPAAddSuccNecessaryUExtract
open PASoundness.PAtoCompactPAAddSuccNecessaryUTransport
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private theorem exists_graph_not_free (t : Peano.Term) (n out b : Nat)
    (hno : n ≠ out) (hn : ∀ a ∈ t.varFinset, a ≠ n) :
    n ∉ (Formula.ex out (termGraph id t out b)).free := by
  intro h
  simp only [Formula.free, Finset.mem_erase] at h
  have hs := termGraph_free_subset id t out b h.2
  rcases Finset.mem_union.mp hs with hv | ho
  · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hv
    simp only [id_eq] at he
    exact (hn a ha) he
  · exact hno (Finset.mem_singleton.mp ho)

/-- Eliminate a graph witness which is absent from the target existential. -/
private def forget_witness (P : Nat) (F : Formula) (n : Nat)
    (hfree : n ∉ F.free) (h : KDerivation (imp P F.encode)) :
    KDerivation (imp (existsCode n P) F.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.existsElim (free_vacuity n F hfree)
    (.closed (.generalize n h)) (Context.head [] _)

/-- The actual equality frame for `t+S(u)=S(t+u)` entails the precise right
child graph-existence premise used by the constructive axiom proof. -/
noncomputable def frame_to_u_graph (t u : Peano.Term) (q : Nat)
    (ht : ∀ a ∈ t.varFinset, a < q) (hu : ∀ a ∈ u.varFinset, a < q) :
    KDerivation (imp (equalityFrame id (Peano.add t (Peano.succ u))
      (Peano.succ (Peano.add t u)) q).encode
      (existsCode (q+2) (termGraph id u (q+2) (q+100)).encode)) := by
  let L := Peano.add t (Peano.succ u)
  let T := Peano.add t u
  let R := Peano.succ T
  let p := q+2+termCost L
  let B := p+64
  let C := B+64+termCost t
  let F := Formula.ex p (termGraph id T p (p+64))
  let U := Formula.ex (B+1) (termGraph id u (B+1) C)
  have hTnames : ∀ a ∈ T.varFinset, a < q := by
    intro a ha
    simp [T, Peano.add, Term.varFinset] at ha
    rcases ha with ha | ha
    · exact ht a ha
    · exact hu a ha
  have hRnames : ∀ a ∈ R.varFinset, id a < q := by
    intro a ha
    have haT : a ∈ T.varFinset := by simpa [R, Peano.succ, Term.varFinset] using ha
    simpa using hTnames a haT
  have hf := equality_frame_right_graph id L R q hRnames
  have hs : KDerivation (imp (termGraph id R (q+1) p).encode F.encode) := by
    simpa [R, Peano.succ, F, Formula.encode] using successor_child id T (q+1) p
  have hfreeF : q+1 ∉ F.free := by
    apply exists_graph_not_free T (q+1) p (p+64) (by dsimp [p]; omega)
    intro a ha
    have hh := hTnames a ha
    omega
  have hfirst := forget_witness (termGraph id R (q+1) p).encode F (q+1) hfreeF hs
  have ha : KDerivation (imp (termGraph id T p B).encode U.encode) := by
    have hright := addition_right_child id t u p B (by
      intro a ha
      have hh := hu a ha
      simp only [id_eq]
      dsimp [B, p]
      omega)
    simpa [T, Peano.add, U, C, B, Formula.encode] using hright
  have hfreeU : p ∉ U.free := by
    apply exists_graph_not_free u p (B+1) C (by dsimp [B]; omega)
    intro a ha
    have hh := hu a ha
    dsimp [p]
    omega
  have hsecond := forget_witness (termGraph id T p B).encode U p hfreeU ha
  have htransport := existential_graph_transport id u C (q+100) (B+1) (q+2)
    (by dsimp [C, B]; omega) (by dsimp [C, B, p]; omega) (by omega)
    (by intro a ha; have := hu a ha; simp only [id_eq]; dsimp [C, B, p]; omega)
    (by intro a ha; have := hu a ha; simp only [id_eq]; omega)
    (by intro a ha; have := hu a ha; simp only [id_eq]; dsimp [B, p]; omega)
    (by intro a ha; have := hu a ha; simp only [id_eq]; omega)
  exact compose (compose (compose hf hfirst) hsecond) htransport

/-- A proof of the guarded addition-successor axiom yields the exact guarded
second-child graph-existence proof required by `add_succ_of_child_existence`. -/
noncomputable def guarded_u_of_add_succ (t u : Peano.Term)
    (h : KDerivation (guardedCode ((Peano.add t (Peano.succ u)).equal
      (Peano.succ (Peano.add t u))))) :
    let A := (Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))
    let q := guardBase A
    KDerivation (imp (guardFormula A).encode
      (existsCode (q+2) (termGraph id u (q+2) (q+100)).encode)) := by
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
  exact compose hg (frame_to_u_graph t u q ht hu)

theorem guarded_u_of_add_succ_certificate (t u : Peano.Term)
    (h : KDerivation (guardedCode ((Peano.add t (Peano.succ u)).equal
      (Peano.succ (Peano.add t u))))) :
    let A := (Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))
    let q := guardBase A
    theoremCode (certificate (guarded_u_of_add_succ t u h)) =
      imp (guardFormula A).encode
        (existsCode (q+2) (termGraph id u (q+2) (q+100)).encode) := certificate_correct _
end PASoundness.PAtoCompactPAAddSuccNecessaryU
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryU.frame_to_u_graph
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryU.guarded_u_of_add_succ
#print axioms PASoundness.PAtoCompactPAAddSuccNecessaryU.guarded_u_of_add_succ_certificate
