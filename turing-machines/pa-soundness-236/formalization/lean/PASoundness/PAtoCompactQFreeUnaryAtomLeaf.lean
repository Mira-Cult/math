import PASoundness.PAtoCompactAllElimTermEqualityGeneral
import PASoundness.PAtoCompactReverseUnaryAtomGuarded
import PASoundness.PAtoCompactGuardedLogicalCongruence

/-! Bidirectional finite-K substitution for a single nonvacuous equality
leaf, retaining the canonical PA guard and the substituting term graph.
This does not establish substitution for other atoms or quantified formulas. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQFreeUnaryAtomLeaf

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactAllElimTermEqualityGeneral PASoundness.PAtoCompactReverseUnaryAtomGuarded
open PASoundness.PAtoCompactGuardedLogicalCongruence

/-- Under the retained PA guard and unary graph, substituting t or its graph
output q into an atom x=s yields both finite-K implication directions. The
right term s is arbitrary, but may not contain x. The guard covers t's free
variables; allocation bounds are explicit. -/
noncomputable def unary_atom_both
    (φ : Peano.Formula) (x : Nat) (t s : Peano.Term)
    (ht : UnaryTerm t) (q d : Nat) (hx : x ∉ s.varFinset)
    (hb : guardBase φ ≤ d) (hq : q < d)
    (hcover : ∀ a ∈ t.varFinset, a ∈ φ.freeVarFinset) :
    GuardedBoth (andF (guardFormula φ) (termGraph id t q d))
      (formula (FOL.substAt ((.var x : Peano.Term).equal s) x (.var q)))
      (formula (FOL.substAt ((.var x : Peano.Term).equal s) x t)) := by
  have htd : ∀ a ∈ t.varFinset, a < d := by
    intro a ha
    have h : a ≤ φ.freeVarFinset.sup id := Finset.le_sup (f := id) (hcover a ha)
    unfold guardBase at hb
    omega
  have hf := atomic_of_graph_fresh t s q d hq htd
  have hf' : KDerivation (imp (termGraph id t q d).encode
      (imp (code (FOL.substAt ((.var x : Peano.Term).equal s) x (.var q)))
        (code (FOL.substAt ((.var x : Peano.Term).equal s) x t)))) := by
    simpa only [atom_subst_fresh_right s (.var q) x hx, atom_subst_fresh_right s t x hx] using hf
  have hr := reverse_atomic_guarded φ x t s ht q d hx hb hq hcover
  let G := (guardFormula φ).encode
  let X := (termGraph id t q d).encode
  let A := code (FOL.substAt ((.var x : Peano.Term).equal s) x (.var q))
  let B := code (FOL.substAt ((.var x : Peano.Term).equal s) x t)
  change KDerivation (imp (both G X) (imp A B)) × KDerivation (imp (both G X) (imp B A))
  constructor
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [A, both G X]
    have ha : Context Γ A := Context.head _ _
    have hgx : Context Γ (both G X) := .hypothesis (by simp [Γ])
    have hx' : Context Γ X := Context.conjunctionRight hgx
    exact .mp ha (.mp hx' (.closed hf'))
  · apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [B, both G X]
    have hb' : Context Γ B := Context.head _ _
    have hgx : Context Γ (both G X) := .hypothesis (by simp [Γ])
    have hg : Context Γ G := Context.conjunctionLeft hgx
    have hx' : Context Γ X := Context.conjunctionRight hgx
    exact .mp hb' (.mp hx' (.mp hg (.closed hr)))

theorem guarded_unary_atom_forward_certificate
    (φ : Peano.Formula) (x : Nat) (t s : Peano.Term)
    (ht : UnaryTerm t) (q d : Nat) (hx : x ∉ s.varFinset)
    (hb : guardBase φ ≤ d) (hq : q < d)
    (hcover : ∀ a ∈ t.varFinset, a ∈ φ.freeVarFinset) :
    theoremCode (certificate (unary_atom_both φ x t s ht q d hx hb hq hcover).1) =
      imp (andF (guardFormula φ) (termGraph id t q d)).encode
        (imp (code (FOL.substAt ((.var x : Peano.Term).equal s) x (.var q)))
          (code (FOL.substAt ((.var x : Peano.Term).equal s) x t))) := certificate_correct _

theorem guarded_unary_atom_backward_certificate
    (φ : Peano.Formula) (x : Nat) (t s : Peano.Term)
    (ht : UnaryTerm t) (q d : Nat) (hx : x ∉ s.varFinset)
    (hb : guardBase φ ≤ d) (hq : q < d)
    (hcover : ∀ a ∈ t.varFinset, a ∈ φ.freeVarFinset) :
    theoremCode (certificate (unary_atom_both φ x t s ht q d hx hb hq hcover).2) =
      imp (andF (guardFormula φ) (termGraph id t q d)).encode
        (imp (code (FOL.substAt ((.var x : Peano.Term).equal s) x t))
          (code (FOL.substAt ((.var x : Peano.Term).equal s) x (.var q)))) := certificate_correct _

end PASoundness.PAtoCompactQFreeUnaryAtomLeaf

#print axioms PASoundness.PAtoCompactQFreeUnaryAtomLeaf.unary_atom_both
#print axioms PASoundness.PAtoCompactQFreeUnaryAtomLeaf.guarded_unary_atom_forward_certificate
#print axioms PASoundness.PAtoCompactQFreeUnaryAtomLeaf.guarded_unary_atom_backward_certificate
