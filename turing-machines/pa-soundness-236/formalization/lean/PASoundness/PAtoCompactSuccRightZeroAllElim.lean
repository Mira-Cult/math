import PASoundness.PAtoCompactRightZeroAllElim
import PASoundness.PAtoCompactSuccRightZeroFunctional
import PASoundness.PAtoCompactSuccRightZeroTotality
import PASoundness.PAtoCompactSuccGraphOutputClosed

/-! Guarded PA universal elimination for the closure of unary terms under
successor and right-zero addition. Graph totality and guard coverage are used
only in the branch where the eliminated variable occurs. -/
namespace PASoundness.PAtoCompactSuccRightZeroAllElim

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedAllElim PASoundness.PAtoCompactRightZeroAllElim
open PASoundness.PAtoCompactSuccRightZeroGrammar

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Every formula admits guarded universal elimination for a replacement
term built from a unary term by successor and right-zero addition, in any
order. The result constructs finite K proof data with no K proof input. -/
noncomputable def succRightZero_allElim (φ : Peano.Formula) (x : Nat)
    {t : Peano.Term} (ht : SuccRightZeroTerm t) :
    KDerivation (guardedCode (allElimFormula φ x t)) := by
  cases ht with
  | unary h => exact PASoundness.PAtoCompactUnaryAllElimComplete.unary_allElim φ x h
  | @succ u h =>
      let T : Peano.Term := .func .succ ![u]
      have hT : SuccRightZeroTerm T := SuccRightZeroTerm.succ h
      change KDerivation (guardedCode (allElimFormula φ x T))
      apply allElim_of_graph_laws φ x T
      · intro hx
        apply PASoundness.PAtoCompactSuccRightZeroTotality.canonical_total id
          (allElimFormula φ x T) hT
        intro a ha
        exact termVars_in_axiom_of_occurs φ x T hx ha
      · intro _hx b q r hq hr hv
        apply PASoundness.PAtoCompactSuccGraphOutputClosed.succ_graph_output id u b q r hq hr
        intro a ha
        apply hv a
        simpa [T, Term.varFinset] using ha
      · intro _hx b q r hq hr hv hg hd
        exact PASoundness.PAtoCompactSuccRightZeroFunctional.functional id
          (guardFormula (allElimFormula φ x T)) hT b q r hv hg hd hq hr
  | @addZero u h =>
      let T : Peano.Term := .func .add ![u, .func .zero Fin.elim0]
      have hT : SuccRightZeroTerm T := SuccRightZeroTerm.addZero h
      change KDerivation (guardedCode (allElimFormula φ x T))
      apply allElim_of_graph_laws φ x T
      · intro hx
        apply PASoundness.PAtoCompactSuccRightZeroTotality.canonical_total id
          (allElimFormula φ x T) hT
        intro a ha
        exact termVars_in_axiom_of_occurs φ x T hx ha
      · intro _hx b q r hq hr hv
        exact PASoundness.PAtoCompactAddZeroGraphOutput.add_zero_output id u b q r hq hr hv
      · intro _hx b q r hq hr hv hg hd
        exact PASoundness.PAtoCompactSuccRightZeroFunctional.functional id
          (guardFormula (allElimFormula φ x T)) hT b q r hv hg hd hq hr

theorem succRightZero_allElim_certificate (φ : Peano.Formula) (x : Nat)
    {t : Peano.Term} (ht : SuccRightZeroTerm t) :
    theoremCode (certificate (succRightZero_allElim φ x ht)) =
      guardedCode (allElimFormula φ x t) := certificate_correct _

end PASoundness.PAtoCompactSuccRightZeroAllElim

#print axioms PASoundness.PAtoCompactSuccRightZeroAllElim.succRightZero_allElim
#print axioms PASoundness.PAtoCompactSuccRightZeroAllElim.succRightZero_allElim_certificate
