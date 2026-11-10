import PASoundness.PAtoCompactEqSubstGuardedGraphReduction

/-! Reduce the guarded PA equality-substitution handler to uniform finite K
term-graph output transport and functionality. Both graph-law families are
explicit proof-data inputs; this is not an unconditional handler. -/

namespace PASoundness.PAtoCompactEqSubstFromUniformGraphLaws

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactTermSubstPolyReplacement
open PASoundness.PAtoCompactGuardedOutputReplacement
open PASoundness.PAtoCompactEqSubstScopedReduction
open PASoundness.PAtoCompactEqSubstGuardedGraphReduction

/-- Guarded output transport for each PA term, as finite K proof data. -/
abbrev UniformOutput : Type :=
  ∀ (g : Formula) (t : Peano.Term), GuardedOutputTransport g t

/-- Guarded graph functionality for each PA term, as finite K proof data. -/
abbrev UniformFunctionality : Type :=
  ∀ (g : Formula) (t : Peano.Term), GuardFunctionality g t

/-- The full literal guarded equality-substitution family follows from the
two displayed uniform K graph-law inputs. -/
noncomputable def handler (output : UniformOutput) (functional : UniformFunctionality)
    (φ : Peano.Formula) (x : Nat) (t u : Peano.Term) :
    KDerivation (guardedCode ((t.equal u).imp
      ((FOL.substAt φ x t).imp (FOL.substAt φ x u)))) := by
  let G := guardFormula (axiomFormula φ x t u)
  exact eqSubst_of_guarded_graph_laws φ x t u
    (output G t) (functional G t) (output G u) (functional G u)

theorem handler_certificate (output : UniformOutput) (functional : UniformFunctionality)
    (φ : Peano.Formula) (x : Nat) (t u : Peano.Term) :
    theoremCode (certificate (handler output functional φ x t u)) =
      guardedCode ((t.equal u).imp
        ((FOL.substAt φ x t).imp (FOL.substAt φ x u))) := certificate_correct _

end PASoundness.PAtoCompactEqSubstFromUniformGraphLaws

#print axioms PASoundness.PAtoCompactEqSubstFromUniformGraphLaws.UniformOutput
#print axioms PASoundness.PAtoCompactEqSubstFromUniformGraphLaws.UniformFunctionality
#print axioms PASoundness.PAtoCompactEqSubstFromUniformGraphLaws.handler
#print axioms PASoundness.PAtoCompactEqSubstFromUniformGraphLaws.handler_certificate
