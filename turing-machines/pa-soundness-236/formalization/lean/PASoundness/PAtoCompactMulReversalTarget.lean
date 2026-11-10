import PASoundness.PAtoCompactMulReversalFormulaNaturality
import PASoundness.PeanoBetaProductIncrement
import PASoundness.Certificates

/-! A checked PA proof source for the multiplication-reversal route. The
reversed conclusion is the desired PA multiplication-successor axiom. This
module does not translate the checked proof into K or prove that axiom in K. -/

namespace PASoundness.PAtoCompactMulReversalTarget

open FirstOrder FirstOrder.Language
open PASoundness.PAtoCompactMulReversalSyntax
open PASoundness.PAtoCompactMulReversalFormulaNaturality

/-- The PA first-factor successor equation at reversed source operands. -/
def source (t u : Peano.Term) : Peano.Formula :=
  (Peano.mul (Peano.succ (reverseTerm u)) (reverseTerm t)).equal
    (Peano.add (Peano.mul (reverseTerm u) (reverseTerm t)) (reverseTerm t))

/-- The equation has a genuine syntactic PA derivation. -/
theorem source_derivation (t u : Peano.Term) : Peano.FormulaProves (source t u) :=
  PeanoBetaProductIncrement.succ_mul (reverseTerm u) (reverseTerm t)

/-- An actual PA certificate checks to that exact equation. The existential
choice is a proposition; no executable proof extraction is asserted. -/
theorem source_certificate (t u : Peano.Term) :
    ∃ c : Certificates.PAProofCode, Certificates.paCheck c = some (source t u) :=
  Certificates.paCheck_complete (source_derivation t u)

/-- Reversing the first-factor equation yields the actual second-factor PA
multiplication-successor axiom for the original terms. This is purely a
syntactic identity, and it does not derive the formula in K. -/
theorem reverse_source (t u : Peano.Term) :
    reverseBounded 0 (source t u) =
      (Peano.mul t (Peano.succ u)).equal (Peano.add (Peano.mul t u) t) := by
  simp only [source, reverse_term_equal, reverseTerm_mul, reverseTerm_succ,
    reverseTerm_add, reverseTerm_involutive]

end PASoundness.PAtoCompactMulReversalTarget

#print axioms PASoundness.PAtoCompactMulReversalTarget.source
#print axioms PASoundness.PAtoCompactMulReversalTarget.source_derivation
#print axioms PASoundness.PAtoCompactMulReversalTarget.source_certificate
#print axioms PASoundness.PAtoCompactMulReversalTarget.reverse_source
