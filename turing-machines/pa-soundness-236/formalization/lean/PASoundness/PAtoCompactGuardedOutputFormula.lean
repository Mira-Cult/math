import PASoundness.PAtoCompactScopedSuccessorComplete
import PASoundness.PAtoCompactGuardedOutputEquality

/-! Draft formula substitution under a retained term graph, with explicitly
guarded graph output transport and guarded graph functionality inputs. -/
namespace PASoundness.PAtoCompactGuardedOutputFormula

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactGuardedLogicalCongruence
open PASoundness.PAtoCompactScopedSuccessorComplete
open PASoundness.PAtoCompactTermSubstPolyReplacement PASoundness.PAtoCompactSuccSubstSyntax
open PASoundness.PAtoCompactGuardedOutputEquality PASoundness.PAtoCompactGuardedOutputReplacement

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Under the same retained graph, substitution by its value name and by the
original term agree in both finite K directions at arbitrary formula depth.
Bound levels and free source names remain distinct even when labels alias. -/
noncomputable def scoped_replacement_substitution
    (g : Formula) (replacement : Peano.Term) (x q d : Nat)
    (hqd : q < d) (htd : ∀ a ∈ replacement.varFinset, a < d)
    (hdom : ∀ a ∈ replacement.varFinset,
      KDerivation (imp g.encode (domainAt d a).encode))
    (output : GuardedOutputTransport g replacement) (functional : GuardFunctionality g replacement)
    {n : Nat} (φ : Peano.language.BoundedFormula Nat n) (bound : Fin n → Nat) :
    GuardedBoth (retained g replacement q d)
      (scopedFormula n (φ.subst (singleSubst x (.var q))) bound)
      (scopedFormula n (φ.subst (singleSubst x replacement)) bound) := by
  apply scoped_of_handler (retained g replacement q d)
    (singleSubst x (.var q)) (singleSubst x replacement) _ φ bound
  intro n s t bound
  exact scoped_equal_of_replacement g replacement x q d hqd htd hdom output functional s t bound

/-- Formula-level graph substitution remains conditional on the explicit
output-transport and guarded-functionality K proof families. -/
noncomputable def formula_replacement_substitution
    (g : Formula) (replacement : Peano.Term) (x q d : Nat)
    (hqd : q < d) (htd : ∀ a ∈ replacement.varFinset, a < d)
    (hdom : ∀ a ∈ replacement.varFinset,
      KDerivation (imp g.encode (domainAt d a).encode))
    (output : GuardedOutputTransport g replacement) (functional : GuardFunctionality g replacement)
    (φ : Peano.Formula) :
    GuardedBoth (retained g replacement q d)
      (formula (FOL.substAt φ x (.var q))) (formula (FOL.substAt φ x replacement)) := by
  change GuardedBoth (retained g replacement q d)
    (scopedFormula 0 (φ.subst (singleSubst x (.var q))) Fin.elim0)
    (scopedFormula 0 (φ.subst (singleSubst x replacement)) Fin.elim0)
  exact scoped_replacement_substitution g replacement x q d hqd htd hdom output functional φ Fin.elim0

theorem formula_replacement_forward_certificate
    (g : Formula) (replacement : Peano.Term) (x q d : Nat)
    (hqd : q < d) (htd : ∀ a ∈ replacement.varFinset, a < d)
    (hdom : ∀ a ∈ replacement.varFinset,
      KDerivation (imp g.encode (domainAt d a).encode))
    (output : GuardedOutputTransport g replacement) (functional : GuardFunctionality g replacement)
    (φ : Peano.Formula) :
    theoremCode (certificate ((formula_replacement_substitution g replacement x q d
      hqd htd hdom output functional φ).1)) =
      imp (retained g replacement q d).encode
        (imp (formula (FOL.substAt φ x (.var q))).encode
          (formula (FOL.substAt φ x replacement)).encode) := certificate_correct _

theorem formula_replacement_backward_certificate
    (g : Formula) (replacement : Peano.Term) (x q d : Nat)
    (hqd : q < d) (htd : ∀ a ∈ replacement.varFinset, a < d)
    (hdom : ∀ a ∈ replacement.varFinset,
      KDerivation (imp g.encode (domainAt d a).encode))
    (output : GuardedOutputTransport g replacement) (functional : GuardFunctionality g replacement)
    (φ : Peano.Formula) :
    theoremCode (certificate ((formula_replacement_substitution g replacement x q d
      hqd htd hdom output functional φ).2)) =
      imp (retained g replacement q d).encode
        (imp (formula (FOL.substAt φ x replacement)).encode
          (formula (FOL.substAt φ x (.var q))).encode) := certificate_correct _

end PASoundness.PAtoCompactGuardedOutputFormula

#print axioms PASoundness.PAtoCompactGuardedOutputFormula.scoped_replacement_substitution
#print axioms PASoundness.PAtoCompactGuardedOutputFormula.formula_replacement_substitution
#print axioms PASoundness.PAtoCompactGuardedOutputFormula.formula_replacement_forward_certificate
#print axioms PASoundness.PAtoCompactGuardedOutputFormula.formula_replacement_backward_certificate
