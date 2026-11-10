import PASoundness.PAtoCompactTransitiveClosure

/-! Pointwise mixed-row lexicographic comparison for the proposed product
matrix. Literal compact `member a b` means b is a member of a. The old first
coordinate 3 lies in old factor 31; the new coordinate 7 equals that factor.
The old/new output comparison is supplied explicitly. No product graph,
collection, global comparability, or PA bridge is asserted. -/
namespace PASoundness.PAtoCompactMultiplicationMixedLexLogic
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

def oldToNewLex : Nat := either (member 7 3) (both (equal 3 7) (member 8 4))
def newToOldLex : Nat := either (member 3 7) (both (equal 7 3) (member 4 8))
def forwardComparison : Nat := both (imp (member 9 5) oldToNewLex)
  (imp oldToNewLex (member 9 5))
def reverseComparison : Nat := both (imp (member 5 9) newToOldLex)
  (imp newToOldLex (member 5 9))

/-- With the old major coordinate strictly below the newly adjoined major
coordinate, and the corresponding comparison of their outputs, both mixed
lexicographic comparisons follow. All hypotheses are literal K antecedents. -/
def mixed_lex : KDerivation (imp (transitiveCode 31 42 43)
    (imp (member 31 3) (imp (equal 7 31)
      (imp (member 9 5) (imp (neg (member 5 9))
        (both forwardComparison reverseComparison)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [neg (member 5 9), member 9 5, equal 7 31, member 31 3, transitiveCode 31 42 43]
  have hn : Context Γ (neg (member 5 9)) := .head _ _
  have hp : Context Γ (member 9 5) := .hypothesis (by simp [Γ])
  have he : Context Γ (equal 7 31) := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 31 3) := .hypothesis (by simp [Γ])
  have ht : Context Γ (transitiveCode 31 42 43) := .hypothesis (by simp [Γ])
  have h37 : Context Γ (member 7 3) := by
    have hs : Context Γ (equal 31 7) := .mp he (.closed (equalitySymmetry 7 31))
    exact .mp hm (.mp hs (.closed (memberLeftEquality 31 7 3)))
  have hf : Context Γ oldToNewLex := Context.disjunctionLeft h37
  have hforward : Context Γ forwardComparison := by
    apply Context.conjunctionIntro
    · exact Context.deduction (.under hf _)
    · exact Context.deduction (.under hp _)
  have hreverseLex : Context Γ (neg newToOldLex) := by
    apply Context.deduction
    let Δ := [newToOldLex,neg (member 5 9), member 9 5, equal 7 31,
      member 31 3, transitiveCode 31 42 43]
    have hd : Context Δ newToOldLex := .head _ _
    have he' : Context Δ (equal 7 31) := .hypothesis (by simp [Δ])
    have hm' : Context Δ (member 31 3) := .hypothesis (by simp [Δ])
    have ht' : Context Δ (transitiveCode 31 42 43) := .hypothesis (by simp [Δ])
    apply Context.disjunctionElim hd
    · let Θ := member 3 7 :: Δ
      have h73 : Context Θ (member 3 7) := .head _ _
      have h313 : Context Θ (member 3 31) :=
        .mp (.under he' _) (.mp h73 (.closed (memberRightEquality 3 7 31)))
      have hself : Context Θ (member 31 31) :=
        .mp h313 (.mp (.under hm' _) (.mp (.under ht' _) (.closed
          (transitive_instance 31 3 42 43 (by decide) (by decide) (by decide) (by decide) (by decide)))))
      exact .mp hself (.closed (self_membership_implies_code_one 31))
    · let Θ := both (equal 7 3) (member 4 8) :: Δ
      have hpair : Context Θ (both (equal 7 3) (member 4 8)) := .head _ _
      have heq : Context Θ (equal 3 31) :=
        .mp (.under he' _) (.mp (Context.conjunctionLeft hpair) (.closed (equalityEuclidean 7 3 31)))
      have hself : Context Θ (member 31 31) :=
        .mp heq (.mp (.under hm' _) (.closed (memberRightEquality 31 3 31)))
      exact .mp hself (.closed (self_membership_implies_code_one 31))
  have hreverse : Context Γ reverseComparison := by
    apply Context.conjunctionIntro
    · apply Context.deduction
      have hc : Context (member 5 9 :: Γ) (member 5 9) := .head _ _
      exact Context.explode newToOldLex (.mp hc (.under hn _))
    · apply Context.deduction
      have hc : Context (newToOldLex :: Γ) newToOldLex := .head _ _
      exact Context.explode (member 5 9) (.mp hc (.under hreverseLex _))
  exact Context.conjunctionIntro hforward hreverse

theorem mixed_lex_certificate : theoremCode (certificate mixed_lex) =
    imp (transitiveCode 31 42 43) (imp (member 31 3) (imp (equal 7 31)
      (imp (member 9 5) (imp (neg (member 5 9))
        (both forwardComparison reverseComparison))))) := certificate_correct mixed_lex
end PASoundness.PAtoCompactMultiplicationMixedLexLogic
#print axioms PASoundness.PAtoCompactMultiplicationMixedLexLogic.mixed_lex
#print axioms PASoundness.PAtoCompactMultiplicationMixedLexLogic.mixed_lex_certificate
