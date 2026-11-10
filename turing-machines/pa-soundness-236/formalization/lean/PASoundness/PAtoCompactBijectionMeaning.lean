import PASoundness.PAtoCompactOrderIsomorphism

/-! Conditional semantic reading of the candidate bijection formula. The
hypotheses identify each of its three graph-formula instances with one shared
binary relation; a separate graph-meaning result must discharge them. -/
namespace PASoundness.PAtoCompactBijectionMeaning
open PASoundness.CompactNamed PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.CompactMatrix (Environment bit update)

private def andF (a b : Formula) : Formula := (a.imp b.not).not
private def fwdF : Formula :=
  .all 2 (.imp (.member 0 2) (.ex 3
    (andF (.member 1 3) (andF (graphFormula 6 2 3)
      (.all 4 (.imp (andF (.member 1 4) (graphFormula 6 2 4)) (.equal 4 3)))))))
private def backF : Formula :=
  .all 3 (.imp (.member 1 3) (.ex 2
    (andF (.member 0 2) (andF (graphFormula 6 2 3)
      (.all 4 (.imp (andF (.member 0 4) (graphFormula 6 4 3)) (.equal 4 2)))))))

theorem bijection_meaning (η : Environment) (R : Nat → Nat → Nat → Prop)
    (h23 : ∀ ρ, (graphFormula 6 2 3).Realize ρ ↔ R (ρ 6) (ρ 2) (ρ 3))
    (h24 : ∀ ρ, (graphFormula 6 2 4).Realize ρ ↔ R (ρ 6) (ρ 2) (ρ 4))
    (h43 : ∀ ρ, (graphFormula 6 4 3).Realize ρ ↔ R (ρ 6) (ρ 4) (ρ 3)) :
    bijectionFormula.Realize η ↔
      (∀ a, bit (η 0) a = true → ∃ b, bit (η 1) b = true ∧ R (η 6) a b ∧
        ∀ b', bit (η 1) b' = true → R (η 6) a b' → b' = b) ∧
      (∀ b, bit (η 1) b = true → ∃ a, bit (η 0) a = true ∧ R (η 6) a b ∧
        ∀ a', bit (η 0) a' = true → R (η 6) a' b → a' = a) := by
  change (andF fwdF backF).Realize η ↔ _
  simp [andF, fwdF, backF, Formula.Realize, Formula.not, h23, h24, h43, update]

end PASoundness.PAtoCompactBijectionMeaning

#print axioms PASoundness.PAtoCompactBijectionMeaning.bijection_meaning
