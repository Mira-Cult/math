import PASoundness.PAtoCompactVacuousQuantifierFree
import PASoundness.PAtoCompactTermSubstSuccessorInduction
import PASoundness.PAtoCompactGuardedLogicalCongruence
import PASoundness.FOLQuantifierDerivations

/-! Convert guarded alignment of two equality frames at a common allocation
base into alignment of the actual translated PA equality substitutions. The
common-frame K proofs are explicit inputs; no semantic soundness is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccessorEqualityFormulaBridge
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactScopedEqualityReplace PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactVacuousQuantifierFree PASoundness.PAtoCompactGuardedLogicalCongruence
open PASoundness.PAtoCompactTermSubstSuccessorInduction

/-- Source-level equality substitution is the equality of the two substituted
terms, including the case where q or variables of u already occur in the atom. -/
theorem variable_atom_subst (s r : Peano.Term) (x q : Nat) :
    FOL.substAt (s.equal r) x (.var q) =
      (s.subst (variableSubst x q)).equal (r.subst (variableSubst x q)) := by
  simp only [FOL.substAt, FOL.equality_subst]
  congr 2

theorem successor_atom_subst (s r u : Peano.Term) (x : Nat) :
    FOL.substAt (s.equal r) x (succTerm u) =
      (s.subst (successorSubst x u)).equal (r.subst (successorSubst x u)) := by
  simp only [FOL.substAt, FOL.equality_subst]
  congr 2

/-- Rebase the two concrete translated equality nodes to and from the common
frame. Both graph and comparison-witness directions remain explicit inputs;
the hypotheses bound every source variable below the common allocator. -/
noncomputable def atom_of_common_frame (H : Formula) (s r u : Peano.Term) (x q b : Nat)
    (hsv : ∀ a ∈ (s.subst (variableSubst x q)).varFinset, a < b)
    (hrv : ∀ a ∈ (r.subst (variableSubst x q)).varFinset, a < b)
    (hss : ∀ a ∈ (s.subst (successorSubst x u)).varFinset, a < b)
    (hrs : ∀ a ∈ (r.subst (successorSubst x u)).varFinset, a < b)
    (frames : GuardedBoth H
      (equalityFrame id (s.subst (variableSubst x q)) (r.subst (variableSubst x q)) b)
      (equalityFrame id (s.subst (successorSubst x u)) (r.subst (successorSubst x u)) b)) :
    GuardedBoth H (formula (FOL.substAt (s.equal r) x (.var q)))
      (formula (FOL.substAt (s.equal r) x (succTerm u))) := by
  rw [variable_atom_subst, successor_atom_subst, original_shape, original_shape]
  let sv := s.subst (variableSubst x q)
  let rv := r.subst (variableSubst x q)
  let ss := s.subst (successorSubst x u)
  let rs := r.subst (successorSubst x u)
  let bv := scopeBase (sv.equal rv) Fin.elim0
  let bs := scopeBase (ss.equal rs) Fin.elim0
  have source := equalityFrame_base_transport id sv rv bv b
    (by intro a ha; exact names_lt_original_base sv rv a (Finset.mem_union_left _ ha))
    (by intro a ha; exact names_lt_original_base sv rv a (Finset.mem_union_right _ ha))
    (by simpa only [id_eq] using hsv)
    (by simpa only [id_eq] using hrv)
  have target := equalityFrame_base_transport id ss rs bs b
    (by intro a ha; exact names_lt_original_base ss rs a (Finset.mem_union_left _ ha))
    (by intro a ha; exact names_lt_original_base ss rs a (Finset.mem_union_right _ ha))
    (by simpa only [id_eq] using hss)
    (by simpa only [id_eq] using hrs)
  constructor
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(equalityFrame id sv rv bv).encode,H.encode]
    have h0 : Context Γ (equalityFrame id sv rv bv).encode := Context.head _ _
    have hH : Context Γ H.encode := .hypothesis (by simp [Γ])
    have h1 : Context Γ (equalityFrame id sv rv b).encode := .mp h0 (.closed source.1)
    have h2 : Context Γ (equalityFrame id ss rs b).encode := .mp h1 (.mp hH (.closed frames.1))
    exact .mp h2 (.closed target.2)
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [(equalityFrame id ss rs bs).encode,H.encode]
    have h0 : Context Γ (equalityFrame id ss rs bs).encode := Context.head _ _
    have hH : Context Γ H.encode := .hypothesis (by simp [Γ])
    have h1 : Context Γ (equalityFrame id ss rs b).encode := .mp h0 (.closed target.1)
    have h2 : Context Γ (equalityFrame id sv rv b).encode := .mp h1 (.mp hH (.closed frames.2))
    exact .mp h2 (.closed source.2)

end PASoundness.PAtoCompactSuccessorEqualityFormulaBridge

#print axioms PASoundness.PAtoCompactSuccessorEqualityFormulaBridge.variable_atom_subst
#print axioms PASoundness.PAtoCompactSuccessorEqualityFormulaBridge.successor_atom_subst
#print axioms PASoundness.PAtoCompactSuccessorEqualityFormulaBridge.atom_of_common_frame
