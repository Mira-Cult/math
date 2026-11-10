import PASoundness.PAtoCompactPAAddSuccDiamondExistence
import PASoundness.PAtoCompactPAAddSuccDiamondBridge
import PASoundness.PAtoCompactAddUnaryTotalityClosed
import PASoundness.PAtoCompactGuardedVacuity

/-! Construct the actual guarded addition-successor axiom from child graph
existence, and discharge those premises for the addition/unary term fragment.
This is finite K proof data; graph functionality and semantic soundness are not
used. -/
namespace PASoundness.PAtoCompactPAAddSuccDiamondExistenceClosed
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactUnaryGuardedCanonical PASoundness.PAtoCompactGuardedVacuity
open PASoundness.PAtoCompactAddUnaryTotalityInduction PASoundness.PAtoCompactAddUnaryGuardedTotality
open PASoundness.PAtoCompactAddUnaryTotalityClosed
open PASoundness.PAtoCompactPAAddSuccDiamondExistenceVacuity
open PASoundness.PAtoCompactPAAddSuccDiamondExistence
open PASoundness.PAtoCompactPAAddSuccDiamondBridge
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Construct the guarded PA axiom when K proofs of both child graphs are
provided at the exact fresh labels; arbitrary PA child terms are permitted. -/
noncomputable def add_succ_of_child_existence (t u : Peano.Term)
    (childT : let A := (Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))
      let q := guardBase A
      KDerivation (imp (guardFormula A).encode
        (existsCode (q+1) (termGraph id t (q+1) (q+100)).encode)))
    (childU : let A := (Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))
      let q := guardBase A
      KDerivation (imp (guardFormula A).encode
        (existsCode (q+2) (termGraph id u (q+2) (q+100)).encode))) :
    KDerivation (guardedCode ((Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u)))) := by
  let A := (Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))
  let q := guardBase A
  have hfree : ∀ a ∈ A.freeVarFinset, a < q := by
    intro a ha
    have hh : a ≤ A.freeVarFinset.sup id := Finset.le_sup (f := id) ha
    dsimp [q, guardBase]
    omega
  have ht : ∀ a ∈ t.varFinset, a < q := by
    intro a ha
    apply hfree
    simp [A, Peano.add, Peano.succ, eq_free, Term.varFinset, ha]
  have hu : ∀ a ∈ u.varFinset, a < q := by
    intro a ha
    apply hfree
    simp [A, Peano.add, Peano.succ, eq_free, Term.varFinset, ha]
  have hg : ∀ a ∈ (guardFormula A).free, a < q := by
    intro a ha
    exact hfree a (guardFormula_free_subset A ha)
  have hd := diamond_of_children t u (guardFormula A) q ht hu hg childT childU
  apply add_succ_of_diamond t u
  simpa [requiredDiamond, closedDiamond_encode, A, q] using hd

/-- The actual guarded PA addition-successor axiom when both argument terms
are built from variables, zero, successor, and addition. -/
noncomputable def add_succ (t u : Peano.Term) (ht : AddUnaryTerm t) (hu : AddUnaryTerm u) :
    KDerivation (guardedCode ((Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u)))) := by
  let A := (Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))
  let q := guardBase A
  have hfree : ∀ a ∈ A.freeVarFinset, a < q := by
    intro a ha
    have hh : a ≤ A.freeVarFinset.sup id := Finset.le_sup (f := id) ha
    dsimp [q, guardBase]
    omega
  have hcoverT : ∀ a ∈ t.varFinset, id a ∈ A.freeVarFinset := by
    intro a ha
    simp [A, Peano.add, Peano.succ, eq_free, Term.varFinset, ha]
  have hcoverU : ∀ a ∈ u.varFinset, id a ∈ A.freeVarFinset := by
    intro a ha
    simp [A, Peano.add, Peano.succ, eq_free, Term.varFinset, ha]
  have hT := PAtoCompactAddUnaryGuardedTotality.guarded_total id A ht additionExistence
    (q+100) (q+1) (by omega) (by intro a ha; have := hfree a ha; omega) hcoverT
  have hU := PAtoCompactAddUnaryGuardedTotality.guarded_total id A hu additionExistence
    (q+100) (q+2) (by omega) (by intro a ha; have := hfree a ha; omega) hcoverU
  exact add_succ_of_child_existence t u hT hU

theorem add_succ_certificate (t u : Peano.Term) (ht : AddUnaryTerm t) (hu : AddUnaryTerm u) :
    theoremCode (certificate (add_succ t u ht hu)) =
      guardedCode ((Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))) :=
  certificate_correct _
end PASoundness.PAtoCompactPAAddSuccDiamondExistenceClosed
#print axioms PASoundness.PAtoCompactPAAddSuccDiamondExistenceClosed.add_succ_of_child_existence
#print axioms PASoundness.PAtoCompactPAAddSuccDiamondExistenceClosed.add_succ
#print axioms PASoundness.PAtoCompactPAAddSuccDiamondExistenceClosed.add_succ_certificate
