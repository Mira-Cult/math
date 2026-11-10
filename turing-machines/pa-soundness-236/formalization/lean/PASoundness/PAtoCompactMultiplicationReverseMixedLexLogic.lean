import PASoundness.PAtoCompactMultiplicationMixedLexLogic

/-! Pointwise lexicographic logic for a new-row point followed by an old-row
point. Compact `member a b` means b is a member of a. The old first coordinate
7 lies in old factor 30, while the new coordinate 3 equals that factor. The
output comparison is supplied explicitly; no product graph, row collection,
global comparability, or PA bridge is asserted. -/
namespace PASoundness.PAtoCompactMultiplicationReverseMixedLexLogic
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactMultiplicationMixedLexLogic
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Given old coordinate 7∈30, new coordinate 3=30, old output 9∈new output 5,
and the reverse output nonmembership, both exact product-lex comparisons
hold. All conditions are literal K antecedents. -/
def reverse_mixed_lex : KDerivation (imp (transitiveCode 30 42 43)
    (imp (member 30 7) (imp (equal 3 30)
      (imp (member 5 9) (imp (neg (member 9 5))
        (both forwardComparison reverseComparison)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [neg (member 9 5),member 5 9,equal 3 30,member 30 7,transitiveCode 30 42 43]
  have hn : Context Γ (neg (member 9 5)) := .head _ _
  have hp : Context Γ (member 5 9) := .hypothesis (by simp [Γ])
  have he : Context Γ (equal 3 30) := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 30 7) := .hypothesis (by simp [Γ])
  have ht : Context Γ (transitiveCode 30 42 43) := .hypothesis (by simp [Γ])
  have h73 : Context Γ (member 3 7) := by
    have hs : Context Γ (equal 30 3) := .mp he (.closed (equalitySymmetry 3 30))
    exact .mp hm (.mp hs (.closed (memberLeftEquality 30 3 7)))
  have hr : Context Γ newToOldLex := Context.disjunctionLeft h73
  have hreverse : Context Γ reverseComparison := by
    apply Context.conjunctionIntro
    · exact Context.deduction (.under hr _)
    · exact Context.deduction (.under hp _)
  have hforwardLex : Context Γ (neg oldToNewLex) := by
    apply Context.deduction
    let Δ := [oldToNewLex,neg (member 9 5),member 5 9,equal 3 30,member 30 7,transitiveCode 30 42 43]
    have hd : Context Δ oldToNewLex := .head _ _
    have he' : Context Δ (equal 3 30) := .hypothesis (by simp [Δ])
    have hm' : Context Δ (member 30 7) := .hypothesis (by simp [Δ])
    have ht' : Context Δ (transitiveCode 30 42 43) := .hypothesis (by simp [Δ])
    apply Context.disjunctionElim hd
    · let Θ := member 7 3 :: Δ
      have h37 : Context Θ (member 7 3) := .head _ _
      have h307 : Context Θ (member 7 30) :=
        .mp (.under he' _) (.mp h37 (.closed (memberRightEquality 7 3 30)))
      have hself : Context Θ (member 30 30) :=
        .mp h307 (.mp (.under hm' _) (.mp (.under ht' _) (.closed
          (transitive_instance 30 7 42 43 (by decide) (by decide) (by decide) (by decide) (by decide)))))
      exact .mp hself (.closed (self_membership_implies_code_one 30))
    · let Θ := both (equal 3 7) (member 8 4) :: Δ
      have hpair : Context Θ (both (equal 3 7) (member 8 4)) := .head _ _
      have heq : Context Θ (equal 7 30) :=
        .mp (.under he' _) (.mp (Context.conjunctionLeft hpair) (.closed (equalityEuclidean 3 7 30)))
      have hself : Context Θ (member 30 30) :=
        .mp heq (.mp (.under hm' _) (.closed (memberRightEquality 30 7 30)))
      exact .mp hself (.closed (self_membership_implies_code_one 30))
  have hforward : Context Γ forwardComparison := by
    apply Context.conjunctionIntro
    · apply Context.deduction
      have hc : Context (member 9 5 :: Γ) (member 9 5) := .head _ _
      exact Context.explode oldToNewLex (.mp hc (.under hn _))
    · apply Context.deduction
      have hc : Context (oldToNewLex :: Γ) oldToNewLex := .head _ _
      exact Context.explode (member 9 5) (.mp hc (.under hforwardLex _))
  exact Context.conjunctionIntro hforward hreverse

theorem reverse_mixed_lex_certificate : theoremCode (certificate reverse_mixed_lex) =
    imp (transitiveCode 30 42 43) (imp (member 30 7) (imp (equal 3 30)
      (imp (member 5 9) (imp (neg (member 9 5))
        (both forwardComparison reverseComparison))))) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationReverseMixedLexLogic
#print axioms PASoundness.PAtoCompactMultiplicationReverseMixedLexLogic.reverse_mixed_lex
#print axioms PASoundness.PAtoCompactMultiplicationReverseMixedLexLogic.reverse_mixed_lex_certificate
