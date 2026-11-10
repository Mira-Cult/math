import PASoundness.PAtoCompactSuccessorAllElim
import PASoundness.PAtoCompactScopedZeroComplete

/-! Guarded universal elimination for every unary PA term, including zero.
The unused-variable case is handled separately by the imported reducer. -/
namespace PASoundness.PAtoCompactUnaryAllElimComplete

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedAllElim
open PASoundness.PAtoCompactUnaryTermTransport PASoundness.PAtoCompactUnaryGuardedCanonical
open PASoundness.PAtoCompactUnarySubstitutionReduce PASoundness.PAtoCompactSuccessorAllElim
open PASoundness.PAtoCompactTermSubstZeroInduction PASoundness.PAtoCompactScopedZeroComplete

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Universal elimination for substitution by zero, for any PA formula. -/
noncomputable def zero_allElim (φ : Peano.Formula) (x : Nat) :
    KDerivation (guardedCode (allElimFormula φ x Peano.zero)) := by
  apply unary_allElim_of_variable_graph φ x Peano.zero UnaryTerm.zero
  intro _hx
  let A := allElimFormula φ x Peano.zero
  let q := outputName A
  let d := allocatorBase A
  let g := guardFormula A
  have hqd : q < d := by dsimp [q, d, allocatorBase]; omega
  have halign := (formula_zero_substitution g x q d hqd φ).1
  change KDerivation (imp g.encode (imp (termGraph id Peano.zero q d).encode
    (imp (code (FOL.substAt φ x (.var q))) (code (FOL.substAt φ x Peano.zero)))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let G := (termGraph id Peano.zero q d).encode
  let V := code (FOL.substAt φ x (.var q))
  let Γ := [V, G, g.encode]
  have hv : Context Γ V := Context.head _ _
  have hg : Context Γ g.encode := .hypothesis (by simp [Γ])
  have hG : Context Γ G := .hypothesis (by simp [Γ])
  have hret : Context Γ (retainedZero g q d).encode := by
    have hh := Context.conjunctionIntro hg hG
    simpa [retainedZero, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg, G] using hh
  exact .mp hv (.mp hret (.closed halign))

/-- Every guarded PA universal-elimination axiom with a unary replacement
term has a finite K derivation, for arbitrary quantified source formulas. -/
noncomputable def unary_allElim (φ : Peano.Formula) (x : Nat)
    {t : Peano.Term} (ht : UnaryTerm t) :
    KDerivation (guardedCode (allElimFormula φ x t)) := by
  apply unary_allElim_of_zero _ φ x ht
  intro ψ y
  exact zero_allElim ψ y

theorem zero_allElim_certificate (φ : Peano.Formula) (x : Nat) :
    theoremCode (certificate (zero_allElim φ x)) =
      guardedCode (allElimFormula φ x Peano.zero) := certificate_correct _

theorem unary_allElim_certificate (φ : Peano.Formula) (x : Nat)
    {t : Peano.Term} (ht : UnaryTerm t) :
    theoremCode (certificate (unary_allElim φ x ht)) =
      guardedCode (allElimFormula φ x t) := certificate_correct _

end PASoundness.PAtoCompactUnaryAllElimComplete

#print axioms PASoundness.PAtoCompactUnaryAllElimComplete.zero_allElim
#print axioms PASoundness.PAtoCompactUnaryAllElimComplete.unary_allElim
#print axioms PASoundness.PAtoCompactUnaryAllElimComplete.zero_allElim_certificate
#print axioms PASoundness.PAtoCompactUnaryAllElimComplete.unary_allElim_certificate
