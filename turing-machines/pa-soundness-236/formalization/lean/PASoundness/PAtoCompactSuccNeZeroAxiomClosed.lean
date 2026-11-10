import PASoundness.PAtoCompactSuccNeZeroAxiomConditional
import PASoundness.PAtoCompactSuccNeZeroDynamic

/-! A finite K proof of the actual guarded PA successor-not-zero axiom, for
every PA argument term. No totality or functionality of that term is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccNeZeroAxiomClosed

open PASoundness.CompactProof PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactSuccNeZeroAxiomConditional PASoundness.PAtoCompactSuccNeZeroDynamic

/-- Construct the genuine guarded PA `S(t) ≠ 0` axiom for arbitrary t. -/
noncomputable def succ_ne_zero (t : Peano.Term) :
    KDerivation (guardedCode ((Peano.succ t).equal Peano.zero).not) := by
  let b := scopeBase ((Peano.succ t).equal Peano.zero) Fin.elim0
  let e := b+2+termCost (Peano.succ t)+termCost Peano.zero
  have ht := termCost_ge_block (Peano.succ t)
  have hz := termCost_ge_block Peano.zero
  have hbad := succ_not_equiv_zero e (b+2) b (b+1)
    (by dsimp [e]; omega) (by dsimp [e]; omega) (by dsimp [e]; omega)
  exact succ_ne_zero_of_same_base t hbad

theorem succ_ne_zero_certificate (t : Peano.Term) :
    theoremCode (certificate (succ_ne_zero t)) =
      guardedCode ((Peano.succ t).equal Peano.zero).not := certificate_correct _

end PASoundness.PAtoCompactSuccNeZeroAxiomClosed

#print axioms PASoundness.PAtoCompactSuccNeZeroAxiomClosed.succ_ne_zero
#print axioms PASoundness.PAtoCompactSuccNeZeroAxiomClosed.succ_ne_zero_certificate
