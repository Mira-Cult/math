import PASoundness.PAtoCompactUnarySubstitutionReduce
import PASoundness.PAtoCompactScopedSuccessorComplete

/-! Guarded PA universal elimination for substitution by a successor of a
unary term. The quantified formula may have arbitrary depth. -/
namespace PASoundness.PAtoCompactSuccessorAllElim

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedAllElim
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactUnarySubstitutionReduce PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactTermSubstSuccessorInduction
open PASoundness.PAtoCompactScopedSuccessorComplete
open PASoundness.PAtoCompactAllElimVariableFull

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Every guarded universal-elimination leaf with substitution `S u` has
finite K proof data when u is unary. No uniformity or executability of the
constructed proof data is asserted. -/
noncomputable def successor_allElim (φ : Peano.Formula) (x : Nat)
    (u : Peano.Term) (hu : UnaryTerm u) :
    KDerivation (guardedCode (allElimFormula φ x (succTerm u))) := by
  apply unary_allElim_of_variable_graph φ x (succTerm u) (UnaryTerm.succ hu)
  intro hx
  let A := allElimFormula φ x (succTerm u)
  let q := outputName A
  let d := allocatorBase A
  let g := guardFormula A
  have hcover : ∀ a ∈ u.varFinset, a ∈ A.freeVarFinset := by
    intro a ha
    apply termVars_in_axiom_of_occurs φ x (succTerm u) hx
    simpa [succTerm, Term.varFinset] using ha
  have hlt : ∀ a ∈ u.varFinset, a < guardBase A := by
    intro a ha
    have hle : a ≤ A.freeVarFinset.sup id := Finset.le_sup (f := id) (hcover a ha)
    unfold guardBase
    omega
  have hqd : q < d := by dsimp [q, d, allocatorBase]; omega
  have hud : ∀ a ∈ u.varFinset, a < d := by
    intro a ha
    have h := hlt a ha
    dsimp [d, allocatorBase, outputName]
    omega
  have hdom (a : Nat) (ha : a ∈ u.varFinset) :
      KDerivation (imp g.encode (domainAt d a).encode) := by
    have h := PASoundness.PAtoCompactGuardedEqualityReflexivity.guardFormula_projection
      A a (hcover a ha)
    exact compose h (domainAt_transport (guardBase A) d a (by have := hlt a ha; omega)
      (by have := hud a ha; omega))
  have halign := (formula_successor_substitution g u hu x q d hqd hud hdom φ).1
  change KDerivation (imp g.encode (imp (termGraph id (succTerm u) q d).encode
    (imp (code (FOL.substAt φ x (.var q))) (code (FOL.substAt φ x (succTerm u))))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let G := (termGraph id (succTerm u) q d).encode
  let V := code (FOL.substAt φ x (.var q))
  let Γ := [V, G, g.encode]
  have hv : Context Γ V := Context.head _ _
  have hg : Context Γ g.encode := .hypothesis (by simp [Γ])
  have hG : Context Γ G := .hypothesis (by simp [Γ])
  have hret : Context Γ (retained g u q d).encode := by
    have hh := Context.conjunctionIntro hg hG
    simpa [retained, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, G] using hh
  exact .mp hv (.mp hret (.closed halign))

theorem successor_allElim_certificate (φ : Peano.Formula) (x : Nat)
    (u : Peano.Term) (hu : UnaryTerm u) :
    theoremCode (certificate (successor_allElim φ x u hu)) =
      guardedCode (allElimFormula φ x (succTerm u)) := certificate_correct _

/-- The zero-substitution family is the only additional input needed to
cover all unary terms; variable and successor terms are constructed above
and in the variable-substitution endpoint. -/
noncomputable def unary_allElim_of_zero
    (zero : ∀ (φ : Peano.Formula) (x : Nat),
      KDerivation (guardedCode (allElimFormula φ x (.func .zero Fin.elim0))))
    (φ : Peano.Formula) (x : Nat) {t : Peano.Term} (ht : UnaryTerm t) :
    KDerivation (guardedCode (allElimFormula φ x t)) := by
  cases ht with
  | var a => exact allElim_variable φ x a
  | zero => exact zero φ x
  | succ h => exact successor_allElim φ x _ h

theorem unary_allElim_of_zero_certificate
    (zero : ∀ (φ : Peano.Formula) (x : Nat),
      KDerivation (guardedCode (allElimFormula φ x (.func .zero Fin.elim0))))
    (φ : Peano.Formula) (x : Nat) {t : Peano.Term} (ht : UnaryTerm t) :
    theoremCode (certificate (unary_allElim_of_zero zero φ x ht)) =
      guardedCode (allElimFormula φ x t) := certificate_correct _

end PASoundness.PAtoCompactSuccessorAllElim

#print axioms PASoundness.PAtoCompactSuccessorAllElim.successor_allElim
#print axioms PASoundness.PAtoCompactSuccessorAllElim.successor_allElim_certificate
#print axioms PASoundness.PAtoCompactSuccessorAllElim.unary_allElim_of_zero
#print axioms PASoundness.PAtoCompactSuccessorAllElim.unary_allElim_of_zero_certificate
