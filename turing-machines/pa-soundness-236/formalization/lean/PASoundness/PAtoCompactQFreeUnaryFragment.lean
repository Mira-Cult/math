import PASoundness.PAtoCompactQFreeUnaryAtomLeaf
import PASoundness.PAtoCompactTermSubstQFree

/-! Bidirectional finite-K unary substitution for a restricted quantifier-free
fragment. Its atoms are x=s with x absent from s, or arbitrary equalities in
which x is absent from both terms. The retained hypothesis contains the PA
guard and the unary term graph. No general formula substitution is claimed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQFreeUnaryFragment
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactVacuousQuantifierFree PASoundness.PAtoCompactTermSubstQFree
open PASoundness.PAtoCompactGuardedLogicalCongruence PASoundness.PAtoCompactQFreeUnaryAtomLeaf
open PASoundness.PAtoCompactAllElimTermEqualityGeneral

/-- Structural evidence for the exact fragment, including vacuous equalities. -/
inductive Fragment (x : Nat) : Peano.Formula → Type
  | falsum : Fragment x .falsum
  | leftVar (s : Peano.Term) (fresh : x ∉ s.varFinset) :
      Fragment x ((.var x : Peano.Term).equal s)
  | vacuous (s u : Peano.Term) (hs : x ∉ s.varFinset) (hu : x ∉ u.varFinset) :
      Fragment x (s.equal u)
  | imp {φ ψ : Peano.Formula} : Fragment x φ → Fragment x ψ → Fragment x (φ.imp ψ)

noncomputable def fragmentQFree {x : Nat} {φ : Peano.Formula} (h : Fragment x φ) : QuantifierFree φ := by
  induction h with
  | falsum => exact .falsum
  | leftVar s _ => exact .equal (.var x) s
  | vacuous s u _ _ => exact .equal s u
  | imp _ _ ihφ ihψ => exact .imp ihφ ihψ

/-- A vacuous equality has literally equal source substitutions. -/
theorem vacuous_atom_subst (x : Nat) (s u t : Peano.Term)
    (hs : x ∉ s.varFinset) (hu : x ∉ u.varFinset) :
    FOL.substAt (s.equal u) x t = s.equal u := by
  simp only [FOL.substAt, FOL.equality_subst]
  rw [term_subst_of_fresh s t x hs, term_subst_of_fresh u t x hu]

/-- Construct exactly the finite K leaf alignments needed by the selected
fragment. The guard may be any PA formula whose free variables cover t. -/
noncomputable def fragmentLeaves
    (A : Peano.Formula) (x : Nat) (t : Peano.Term) (ht : UnaryTerm t) (q d : Nat)
    (hb : guardBase A ≤ d) (hq : q < d)
    (hcover : ∀ a ∈ t.varFinset, a ∈ A.freeVarFinset)
    {φ : Peano.Formula} (h : Fragment x φ) :
    LeafAlignment (andF (guardFormula A) (termGraph id t q d)) x q t (fragmentQFree h) := by
  induction h with
  | falsum => exact .falsum
  | leftVar s fresh =>
      exact .equal (.var x) s (unary_atom_both A x t s ht q d fresh hb hq hcover)
  | vacuous s u hs hu =>
      apply LeafAlignment.equal s u
      rw [vacuous_atom_subst x s u (.var q) hs hu, vacuous_atom_subst x s u t hs hu]
      constructor <;> apply Context.closeEmpty <;> apply Context.deduction <;> exact .closed (identity _)
  | imp hφ hψ ihφ ihψ => exact .imp ihφ ihψ

/-- Every formula in this fragment has both K substitution directions while
retaining the same PA guard and graph. No equality/leaf proof is an input. -/
noncomputable def fragment_substitution
    (A : Peano.Formula) (x : Nat) (t : Peano.Term) (ht : UnaryTerm t) (q d : Nat)
    (hb : guardBase A ≤ d) (hq : q < d)
    (hcover : ∀ a ∈ t.varFinset, a ∈ A.freeVarFinset)
    {φ : Peano.Formula} (h : Fragment x φ) :
    GuardedBoth (andF (guardFormula A) (termGraph id t q d))
      (formula (FOL.substAt φ x (.var q))) (formula (FOL.substAt φ x t)) :=
  qfree_substitution_local _ x q t φ (fragmentQFree h)
    (fragmentLeaves A x t ht q d hb hq hcover h)

theorem fragment_substitution_backward_certificate
    (A : Peano.Formula) (x : Nat) (t : Peano.Term) (ht : UnaryTerm t) (q d : Nat)
    (hb : guardBase A ≤ d) (hq : q < d)
    (hcover : ∀ a ∈ t.varFinset, a ∈ A.freeVarFinset)
    {φ : Peano.Formula} (h : Fragment x φ) :
    theoremCode (certificate (fragment_substitution A x t ht q d hb hq hcover h).2) =
      imp (andF (guardFormula A) (termGraph id t q d)).encode
        (imp (code (FOL.substAt φ x t)) (code (FOL.substAt φ x (.var q)))) := certificate_correct _
end PASoundness.PAtoCompactQFreeUnaryFragment

#print axioms PASoundness.PAtoCompactQFreeUnaryFragment.fragmentQFree
#print axioms PASoundness.PAtoCompactQFreeUnaryFragment.vacuous_atom_subst
#print axioms PASoundness.PAtoCompactQFreeUnaryFragment.fragmentLeaves
#print axioms PASoundness.PAtoCompactQFreeUnaryFragment.fragment_substitution
#print axioms PASoundness.PAtoCompactQFreeUnaryFragment.fragment_substitution_backward_certificate
