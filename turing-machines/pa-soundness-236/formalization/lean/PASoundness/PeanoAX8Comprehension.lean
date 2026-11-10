import PASoundness.PeanoAX8AliasClosed
import PASoundness.PeanoAX8Distinct

/-! Literal AX8 arithmetic comprehension in PA, split on the actual index
alias. This is one direction of the K-to-PA bridge; it does not establish the
reverse proof translation or an end-to-end machine theorem. -/
namespace PASoundness.PeanoAX8Comprehension
open Peano CompactLogicalTransport

/-- For the genuine guarded AX8 instance, PA proves the exact displayed
comprehension formula. The case a=b uses the literal bound-variable alias;
the case a≠b uses the distinct-name construction. -/
theorem comprehension (a b c : Nat) (hca : c ≠ a) (hcb : c ≠ b) :
    FormulaProves (comprehensionFormula a b c) := by
  by_cases hab : a = b
  · subst a
    exact PeanoAX8AliasClosed.alias_comprehension b c (Ne.symm hcb)
  · exact PeanoAX8Distinct.distinct_comprehension a b c hab hca hcb

end PASoundness.PeanoAX8Comprehension

#print axioms PASoundness.PeanoAX8Comprehension.comprehension
