import PASoundness.PAtoCompactGuardedOutputFormula
import PASoundness.PAtoCompactZeroGraphOutputTransport
import PASoundness.PAtoCompactSuccGraphOutputClosed
import PASoundness.PAtoCompactUnaryGraphFunctionalityFull

/-! Draft guarded output and functionality interfaces for unary terms.
The source-variable candidate requirements are explicit K proof inputs.
This file has not been checked in a clean build. -/
namespace PASoundness.PAtoCompactGuardedUnaryOutput
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactUnaryTermTransport
open PASoundness.PAtoCompactTermSubstPolyReplacement PASoundness.PAtoCompactGuardedOutputReplacement
open PASoundness.PAtoCompactZeroGraphOutputTransport PASoundness.PAtoCompactSuccGraphOutputClosed
open PASoundness.PAtoCompactUnaryGraphFunctionalityFull
open PASoundness.PAtoCompactGuardedOutputFormula PASoundness.PAtoCompactGuardedLogicalCongruence
open PASoundness.PAtoCompactFormulaTranslation

/-- A unary term's graph admits output transport under its source guard. -/
noncomputable def unary_output (g : Formula) {t : Peano.Term}
    (ht : UnaryTerm t) : GuardedOutputTransport g t := by
  cases ht with
  | var a => exact variable_output g a
  | zero =>
      apply guard_unguarded_output
      intro b q r hq hr _
      exact zero_graph_output id b q r hq hr
  | @succ u hu =>
      apply guard_unguarded_output
      intro b q r hq hr hv
      have hvars : ∀ a ∈ u.varFinset, id a < b := by
        intro a ha
        apply hv a
        simp [Term.varFinset, ha]
      exact succ_graph_output id u b q r hq hr hvars

/-- The existing unary graph functionality supplies the same guarded family. -/
noncomputable def unary_functionality (g : Formula) {t : Peano.Term}
    (ht : UnaryTerm t) : GuardFunctionality g t := by
  intro b q r hq hr hv hg hd
  exact unary_functional id g ht b q r hv hg hd hq hr

/-- Under the displayed guard-to-variable candidates, substitution by a
unary term and by its retained output agree at arbitrary formula depth. -/
noncomputable def unary_formula_substitution (g : Formula) (t : Peano.Term)
    (ht : UnaryTerm t) (x q d : Nat) (hqd : q < d)
    (htd : ∀ a ∈ t.varFinset, a < d)
    (hdom : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (φ : Peano.Formula) :
    GuardedBoth (retained g t q d)
      (formula (FOL.substAt φ x (.var q))) (formula (FOL.substAt φ x t)) :=
  formula_replacement_substitution g t x q d hqd htd hdom
    (unary_output g ht) (unary_functionality g ht) φ

end PASoundness.PAtoCompactGuardedUnaryOutput
#print axioms PASoundness.PAtoCompactGuardedUnaryOutput.unary_output
#print axioms PASoundness.PAtoCompactGuardedUnaryOutput.unary_functionality
#print axioms PASoundness.PAtoCompactGuardedUnaryOutput.unary_formula_substitution
