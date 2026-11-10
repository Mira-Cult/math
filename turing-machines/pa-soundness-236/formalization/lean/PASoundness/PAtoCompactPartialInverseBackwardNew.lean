import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.PAtoCompactZeroSuccessor

/-! The fixed new-endpoint branch of partial inverse backward coverage. The
coordinate equalities, endpoint equality, successor graph, and forward edge
are explicit K antecedents. No inverse graph, graph existence, uniform
quantification, or induction is constructed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseBackwardNew
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- At the appended pair's coordinates, the queried source belongs to the
successor prefix and the queried forward edge follows by equality transport.
Names 2,3,6,8,10,12,13,15 avoid graph binders 19–22. -/
def backward_new_branch : KDerivation
    (imp (equal 3 13) (imp (equal 2 12) (imp (equal 12 8)
      (imp (successorCode 8 10 15) (imp (graphFormula 6 12 13).encode
        (both (member 10 2) (graphFormula 6 2 3).encode)))))) := by
  have hsrc := (equalityReplace 12 2 (graphFormula 6 12 13) (by decide) (by decide)).1
  have himg := (equalityReplace 13 3 (graphFormula 6 2 13) (by decide) (by decide)).1
  have hrenameSrc : replace 12 2 (graphFormula 6 12 13) = graphFormula 6 2 13 := by decide
  have hrenameImg : replace 13 3 (graphFormula 6 2 13) = graphFormula 6 2 3 := by decide
  rw [hrenameSrc] at hsrc
  rw [hrenameImg] at himg
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 12 13).encode, successorCode 8 10 15,
    equal 12 8, equal 2 12, equal 3 13]
  have hg : Context Γ (graphFormula 6 12 13).encode := Context.head _ _
  have hs : Context Γ (successorCode 8 10 15) := .hypothesis (by simp [Γ])
  have he₁ : Context Γ (equal 12 8) := .hypothesis (by simp [Γ])
  have he₂ : Context Γ (equal 2 12) := .hypothesis (by simp [Γ])
  have he₃ : Context Γ (equal 3 13) := .hypothesis (by simp [Γ])
  have h8in10 : Context Γ (member 10 8) :=
    .mp hs (.closed (successor_contains_input 8 10 15 (by decide) (by decide)))
  have h8eq2 : Context Γ (equal 8 2) := Context.eqSymm (Context.eqTrans he₂ he₁)
  have h2in10 : Context Γ (member 10 2) :=
    .mp h8eq2 (.mp h8in10 (.closed (memberRightEquality 10 8 2)))
  have hg2 : Context Γ (graphFormula 6 2 13).encode :=
    .mp hg (.mp (Context.eqSymm he₂) (.closed hsrc))
  have hg3 : Context Γ (graphFormula 6 2 3).encode :=
    .mp hg2 (.mp (Context.eqSymm he₃) (.closed himg))
  exact Context.conjunctionIntro h2in10 hg3

theorem backward_new_branch_certificate : theoremCode (certificate backward_new_branch) =
    imp (equal 3 13) (imp (equal 2 12) (imp (equal 12 8)
      (imp (successorCode 8 10 15) (imp (graphFormula 6 12 13).encode
        (both (member 10 2) (graphFormula 6 2 3).encode))))) :=
  certificate_correct backward_new_branch

end PASoundness.PAtoCompactPartialInverseBackwardNew

#print axioms PASoundness.PAtoCompactPartialInverseBackwardNew.backward_new_branch
#print axioms PASoundness.PAtoCompactPartialInverseBackwardNew.backward_new_branch_certificate
