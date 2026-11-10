import PASoundness.PAtoCompactPAAddSuccDiamondExistenceClosed
import PASoundness.PAtoCompactAllTermsTotalityClosed

/-! The actual guarded PA addition-successor axiom for arbitrary PA terms,
using finite K graph-existence proofs for both argument terms. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PASoundness.PAtoCompactPAAddSuccAllTerms

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactVacuousEqualityAlignment

/-- Construct the literal guarded PA axiom `t + S(u) = S(t + u)` for
arbitrary PA terms, with no supplied K proof or term-fragment evidence. -/
noncomputable def add_succ (t u : Peano.Term) :
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
  have hT := PASoundness.PAtoCompactAllTermsTotalityClosed.guarded_total id A t
    (q+100) (q+1) (by omega) (by intro a ha; have := hfree a ha; omega) hcoverT
  have hU := PASoundness.PAtoCompactAllTermsTotalityClosed.guarded_total id A u
    (q+100) (q+2) (by omega) (by intro a ha; have := hfree a ha; omega) hcoverU
  exact PASoundness.PAtoCompactPAAddSuccDiamondExistenceClosed.add_succ_of_child_existence t u hT hU

theorem add_succ_certificate (t u : Peano.Term) :
    theoremCode (certificate (add_succ t u)) =
      guardedCode ((Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))) :=
  certificate_correct _

end PASoundness.PAtoCompactPAAddSuccAllTerms

#print axioms PASoundness.PAtoCompactPAAddSuccAllTerms.add_succ
#print axioms PASoundness.PAtoCompactPAAddSuccAllTerms.add_succ_certificate
