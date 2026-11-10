import PASoundness.PAtoCompactPAAddSuccDiamondExistenceClosed
import PASoundness.PAtoCompactPAAddSuccNecessaryT
import PASoundness.PAtoCompactPAAddSuccNecessaryU

/-! Constructive proof-data equivalence for the actual guarded PA addition-
successor axiom. Both directions use finite K proof transformations; no PA/K
semantic soundness is assumed. The child graph obligations retain the exact
axiom guard, witness names and allocator needed by the constructive handler. -/
namespace PASoundness.PAtoCompactPAAddSuccGraphEquivalence
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactPAAddSuccDiamondExistenceClosed
open PASoundness.PAtoCompactPAAddSuccNecessaryT PASoundness.PAtoCompactPAAddSuccNecessaryU

/-- The exact first-child guarded graph code for the addition-successor axiom. -/
def firstChildCode (t u : Peano.Term) : Nat :=
  let A := (Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))
  let q := guardBase A
  imp (guardFormula A).encode
    (existsCode (q+1) (termGraph id t (q+1) (q+100)).encode)

/-- The exact second-child guarded graph code for the addition-successor axiom. -/
def secondChildCode (t u : Peano.Term) : Nat :=
  let A := (Peano.add t (Peano.succ u)).equal (Peano.succ (Peano.add t u))
  let q := guardBase A
  imp (guardFormula A).encode
    (existsCode (q+2) (termGraph id u (q+2) (q+100)).encode)

/-- An actual finite K proof of the guarded axiom exists exactly when finite
K proofs of the two specified guarded child graph-existence codes exist. This
holds for arbitrary PA terms, including those containing multiplication. It
does not assert that either side is inhabited. -/
theorem add_succ_proof_iff_child_graph_proofs (t u : Peano.Term) :
    Nonempty (KDerivation (guardedCode ((Peano.add t (Peano.succ u)).equal
      (Peano.succ (Peano.add t u))))) ↔
    Nonempty (KDerivation (firstChildCode t u)) ∧
      Nonempty (KDerivation (secondChildCode t u)) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨⟨guarded_t_of_add_succ t u h⟩, ⟨guarded_u_of_add_succ t u h⟩⟩
  · rintro ⟨⟨ht⟩, ⟨hu⟩⟩
    exact ⟨add_succ_of_child_existence t u ht hu⟩

end PASoundness.PAtoCompactPAAddSuccGraphEquivalence
#print axioms PASoundness.PAtoCompactPAAddSuccGraphEquivalence.add_succ_proof_iff_child_graph_proofs
