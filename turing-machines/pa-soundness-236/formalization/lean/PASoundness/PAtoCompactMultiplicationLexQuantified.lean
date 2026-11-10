import PASoundness.PAtoCompactMultiplicationFourCaseLexClosed
import PASoundness.PAtoCompactProductNewLexShape
import PASoundness.PAtoCompactFreeVacuity

/-! Six-point quantification of the actual product-graph lex comparison.
The original shared candidate, cut, old/suffix cleanliness and graph64
no-garbage assumptions remain literal K antecedents. This proves neither a
row graph nor multiplication totality or PA soundness. -/
namespace PASoundness.PAtoCompactMultiplicationLexQuantified
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactMultiplicationCandidate PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationLexSharedContext PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactMultiplicationFourCaseLex PASoundness.PAtoCompactMultiplicationFourCaseLexClosed
open PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha PASoundness.PAtoCompactProductCleanLexTransfer
open PASoundness.PAtoCompactMultiplicationSameRowLex PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactProductNewLexShape
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private theorem first_triple_shape : tripleAt 64 3 4 5 = queriedTriple := by rfl
private theorem second_triple_shape : tripleAt 64 7 8 9 =
    PAtoCompactMultiplicationSecondBranchSplit.tripleAt 64 :=
  PAtoCompactMultiplicationSecondBranchSplit.triple_shape

/-- The explicit shared and no-garbage hypotheses remain vacuous at all six
query names even where those names occur bound within a hypothesis. -/
def context_vacuity (x : Nat) (hx : x ∈ [3,4,5,7,8,9]) :
    ∀ h, h ∈ [(noGarbage 64).encode, sharedPremise.encode] →
      KDerivation (imp h (allCode x h)) := by
  intro h hh
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hh
  by_cases he : h = (noGarbage 64).encode
  · subst h
    apply free_vacuity x (noGarbage 64)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · have he' : h = sharedPremise.encode := hh.resolve_left he
    subst h
    apply free_vacuity x sharedPremise
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The exact six-quantifier lexicographic clause follows from the proved
pointwise comparison and explicit common and no-garbage assumptions. -/
def lex_clause : KDerivation (imp sharedPremise.encode (imp (noGarbage 64).encode newLex.encode)) := by
  let Γ := [(noGarbage 64).encode,sharedPremise.encode]
  have hp : Context Γ sharedPremise.encode := .hypothesis (by simp [Γ])
  have hn : Context Γ (noGarbage 64).encode := .head _ _
  have hpoint : Context Γ newPoint.encode := by
    change Context Γ (imp newAntecedent.encode comparison.encode)
    apply Context.deduction
    let Δ := [newAntecedent.encode,(noGarbage 64).encode,sharedPremise.encode]
    have ha : Context Δ newAntecedent.encode := .head _ _
    have ha' : Context Δ (both (member 38 3) (both (member 31 4) (both (member 45 5)
      (both (member 38 7) (both (member 31 8) (both (member 45 9)
        (both queriedTriple.encode (PAtoCompactMultiplicationSecondBranchSplit.tripleAt 64).encode))))))) := by
      simpa [newAntecedent,first_triple_shape,second_triple_shape,namedBoth,Formula.not,Formula.encode,both,neg] using ha
    have htriples := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight
      (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight ha')))))
    have h1 := Context.conjunctionLeft htriples
    have h2 := Context.conjunctionRight htriples
    have hc : Context Δ comparisons := .mp h2 (.mp h1 (.mp (.under hn _) (.mp (.under hp _) (.closed point_lex))))
    have hf : Context Δ forwardClause := Context.conjunctionLeft hc
    simpa [comparison_encode,forwardClause,forwardLex] using hf
  have h9 := Context.generalize 9 (context_vacuity 9 (by decide)) hpoint
  have h8 := Context.generalize 8 (context_vacuity 8 (by decide)) h9
  have h7 := Context.generalize 7 (context_vacuity 7 (by decide)) h8
  have h5 := Context.generalize 5 (context_vacuity 5 (by decide)) h7
  have h4 := Context.generalize 4 (context_vacuity 4 (by decide)) h5
  have h3 := Context.generalize 3 (context_vacuity 3 (by decide)) h4
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  rw [new_lex_shape]
  exact h3

theorem lex_clause_certificate : theoremCode (certificate lex_clause) =
    imp sharedPremise.encode (imp (noGarbage 64).encode newLex.encode) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationLexQuantified
#print axioms PASoundness.PAtoCompactMultiplicationLexQuantified.lex_clause
#print axioms PASoundness.PAtoCompactMultiplicationLexQuantified.lex_clause_certificate
