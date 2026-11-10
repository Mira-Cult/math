import PASoundness.PeanoPowerSingleton
import PASoundness.PeanoDivisionTotality

/-! Object-level positivity of the bit modulus attached to a power trace. -/
namespace PASoundness.PeanoPowerDoublePositive
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic

/-- PA proves the double of the endpoint of a literal power trace is
positive. The result does not assert the existence of such a trace. -/
theorem double_positive (n p : Peano.Term) : FormulaProves
    ((pow2 n p).imp (less zero (add p p))) :=
  FOL.Derivation.compose (PeanoPowerSingleton.power_positive n p)
    (PeanoQuotientGap.less_add_right zero p p)

/-- PA can divide an arbitrary dividend by twice the endpoint of a supplied
literal power trace. The witnesses remain inside the division formula. -/
theorem division_by_double (n p a : Peano.Term) : FormulaProves
    ((pow2 n p).imp (PeanoDivisionTotality.division a (add p p))) :=
  FOL.Derivation.compose (double_positive n p)
    (PeanoDivisionTotality.division_totality a (add p p))

end PASoundness.PeanoPowerDoublePositive

#print axioms PASoundness.PeanoPowerDoublePositive.double_positive
#print axioms PASoundness.PeanoPowerDoublePositive.division_by_double
