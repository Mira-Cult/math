import PASoundness.PAtoCompactMulReversalCompilerAdapter
import PASoundness.PAtoCompactMulReversalInduction
import PASoundness.PAtoCompactFirstFactorZeroAxiom
import PASoundness.PAtoCompactGuardedAdditionBridge

/-! Dispatch reversed checked PA arithmetic leaves using finite K proofs.
The first-factor multiplication-successor proof family remains an explicit
input; this module does not construct it or assert PA soundness. -/

namespace PASoundness.PAtoCompactReversedArithmeticLeaves

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactMulReversalSyntax
open PASoundness.PAtoCompactMulReversalFormulaNaturality
open PASoundness.PAtoCompactMulReversalInduction
open PASoundness.PAtoCompactMulReversalCompilerAdapter

/-- The finite K proof family for the first-factor successor equation. Its
construction remains an independent arithmetic obligation. -/
abbrev FirstFactorSuccessor := ∀ t u : Peano.Term,
  KDerivation (guardedCode ((Peano.mul (Peano.succ t) u).equal
    (Peano.add (Peano.mul t u) u)))

private theorem reverse_not (φ : Peano.Formula) :
    reverseBounded 0 φ.not = (reverseBounded 0 φ).not := rfl

/-- Under first-factor successor, build the reversed PA arithmetic leaf family
for all checked axiom constructors, including full parameterized induction.
The other proof families are supplied by the imported finite-K constructions;
no soundness theorem is used. -/
noncomputable def arithmetic (firstSucc : FirstFactorSuccessor) : ReversedArithmeticLeaves := by
  intro c φ hc
  cases c with
  | succNeZero t =>
      cases hc
      simpa only [reverse_not, reverse_term_equal, reverseTerm_succ, reverseTerm_zero] using
        PAtoCompactSuccNeZeroAxiomClosed.succ_ne_zero (reverseTerm t)
  | succInjective t u =>
      cases hc
      simpa only [reverseBounded_imp, reverse_term_equal, reverseTerm_succ,
        PAtoCompactSuccInjectivityGuardedFrame.succInjective] using
        PAtoCompactSuccInjectivityProofClosed.guarded_successor_injective (reverseTerm t) (reverseTerm u)
  | addZero t =>
      cases hc
      simpa only [reverse_term_equal, reverseTerm_add, reverseTerm_zero] using
        PAtoCompactPAAddZeroAllTerms.add_zero (reverseTerm t)
  | addSucc t u =>
      cases hc
      simpa only [reverse_term_equal, reverseTerm_add, reverseTerm_succ] using
        PAtoCompactPAAddSuccAllTerms.add_succ (reverseTerm t) (reverseTerm u)
  | mulZero t =>
      cases hc
      simpa only [reverse_term_equal, reverseTerm_mul, reverseTerm_zero] using
        PAtoCompactFirstFactorZeroAxiom.first_factor_zero (reverseTerm t)
  | mulSucc t u =>
      cases hc
      simpa only [reverse_term_equal, reverseTerm_mul, reverseTerm_add, reverseTerm_succ] using
        firstSucc (reverseTerm u) (reverseTerm t)
  | induction ψ x =>
      cases hc
      simpa only [reverse_inductionAxiom] using
        PAtoCompactFullInductionProofClosed.full_induction_closed (reverseBounded 0 ψ) x

theorem arithmetic_certificate (firstSucc : FirstFactorSuccessor)
    (c : Certificates.PACode) (φ : Peano.Formula)
    (hc : Certificates.paDecode c = some φ) :
    theoremCode (certificate (arithmetic firstSucc c φ hc)) =
      guardedCode (reverseBounded 0 φ) := certificate_correct _

end PASoundness.PAtoCompactReversedArithmeticLeaves

#print axioms PASoundness.PAtoCompactReversedArithmeticLeaves.FirstFactorSuccessor
#print axioms PASoundness.PAtoCompactReversedArithmeticLeaves.arithmetic
#print axioms PASoundness.PAtoCompactReversedArithmeticLeaves.arithmetic_certificate
