import PASoundness.PAtoCompactSuccessorEqualityFormulaBridge
import PASoundness.PAtoCompactSuccessorEqualityFrameCommonBase
import PASoundness.PAtoCompactTermSubstQFree

/-! Actual finite-K substitution of a successor term in arbitrary equality
atoms and, consequently, every quantifier-free PA formula. The retained
hypothesis includes the successor graph; candidate proofs for its child
variables are explicit. No semantic soundness is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccessorEqualityComplete
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactTermSubstSuccessorInduction
open PASoundness.PAtoCompactGuardedLogicalCongruence PASoundness.PAtoCompactTermSubstQFree
open PASoundness.PAtoCompactVacuousQuantifierFree
open PASoundness.PAtoCompactSuccessorEqualityFormulaBridge PASoundness.PAtoCompactSuccessorEqualityFrameCommonBase

/-- A common allocator strictly above the retained free names and every name
in the four substituted equality operands. -/
def commonBase (g : Formula) (u s r : Peano.Term) (x q d : Nat) : Nat :=
  (((retained g u q d).free ∪ (s.subst (variableSubst x q)).varFinset ∪
      (r.subst (variableSubst x q)).varFinset ∪ (s.subst (successorSubst x u)).varFinset ∪
      (r.subst (successorSubst x u)).varFinset).sup id) + 1

/-- Finite K implications in both directions for arbitrary equality operands.
The successor graph is retained as an object-level antecedent; it is not
assumed total. The child-variable candidate inputs are finite K proofs. -/
noncomputable def equality_alignment
    (g : Formula) (u : Peano.Term) (hu : UnaryTerm u) (x q d : Nat)
    (hqd : q < d) (hud : ∀ a ∈ u.varFinset, a < d)
    (hdom : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (s r : Peano.Term) :
    GuardedBoth (retained g u q d)
      (formula (FOL.substAt (s.equal r) x (.var q)))
      (formula (FOL.substAt (s.equal r) x (succTerm u))) := by
  let b := commonBase g u s r x q d
  have hb : ∀ a ∈ (retained g u q d).free ∪ (s.subst (variableSubst x q)).varFinset ∪
      (r.subst (variableSubst x q)).varFinset ∪ (s.subst (successorSubst x u)).varFinset ∪
      (r.subst (successorSubst x u)).varFinset, a < b := by
    intro a ha
    have hle := Finset.le_sup (f := id) ha
    change a < _ + 1
    exact Nat.lt_succ_of_le (by simpa only [id_eq] using hle)
  have hH : ∀ a ∈ (retained g u q d).free, a < b := by
    intro a ha
    apply hb
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ha)))
  have hsv : ∀ a ∈ (s.subst (variableSubst x q)).varFinset, a < b := by
    intro a ha
    apply hb
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ha)))
  have hrv : ∀ a ∈ (r.subst (variableSubst x q)).varFinset, a < b := by
    intro a ha
    apply hb
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ha))
  have hss : ∀ a ∈ (s.subst (successorSubst x u)).varFinset, a < b := by
    intro a ha
    apply hb
    exact Finset.mem_union_left _ (Finset.mem_union_right _ ha)
  have hrs : ∀ a ∈ (r.subst (successorSubst x u)).varFinset, a < b := by
    intro a ha
    apply hb
    exact Finset.mem_union_right _ ha
  have hf := equality_frame_alignment g u hu x q d hqd hud hdom s r b hH hsv hss hrv hrs
  exact atom_of_common_frame (retained g u q d) s r u x q b hsv hrv hss hrs hf

/-- Both K directions for every quantifier-free PA formula, obtained from the
arbitrary equality leaf family under one fixed retained graph and guard. -/
noncomputable def qfree_alignment
    (g : Formula) (u : Peano.Term) (hu : UnaryTerm u) (x q d : Nat)
    (hqd : q < d) (hud : ∀ a ∈ u.varFinset, a < d)
    (hdom : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (φ : Peano.Formula) (hf : QuantifierFree φ) :
    GuardedBoth (retained g u q d) (formula (FOL.substAt φ x (.var q)))
      (formula (FOL.substAt φ x (succTerm u))) :=
  qfree_substitution (retained g u q d) x q (succTerm u)
    (equality_alignment g u hu x q d hqd hud hdom) φ hf

end PASoundness.PAtoCompactSuccessorEqualityComplete

#print axioms PASoundness.PAtoCompactSuccessorEqualityComplete.equality_alignment
#print axioms PASoundness.PAtoCompactSuccessorEqualityComplete.qfree_alignment
