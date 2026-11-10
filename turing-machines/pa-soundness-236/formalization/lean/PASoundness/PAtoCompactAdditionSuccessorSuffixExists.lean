import PASoundness.PAtoCompactAdditionSuccessorSuffix

/-! K constructs the next suffix, together with its adjunction graph, from
the preceding suffix and result successor. No isomorphism extension,
collection theorem, arithmetic totality, or PA interpretation is asserted.
Compact negation is literal implication to code 1. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorSuffixExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactPointAdjoinSelector PASoundness.PAtoCompactAdditionSuccessorSuffix
attribute [local irreducible] imp Cantor.pair Cantor.triangle
private def N : Formula := (Formula.member 33 32).not
private def F : Formula := .all 35 (namedFilterBody 32 34 35 (Formula.member 33 35).not)
private def S : Formula := .all 39 (namedSuccessorBody 32 38 39)
private def A : Formula := namedAdjoin 34 32 40 41
private def G : Formula := .all 35 (namedFilterBody 38 40 35 (Formula.member 33 35).not)
private def P : Formula := namedBoth N (namedBoth F S)
private def B : Formula := namedBoth A G
private theorem fresh40 : 40 ∉ P.names := by decide

/-- Fixed-output adjunction is constructible in K, with no supplied graph. -/
def successor_suffix_adjoin_exists : KDerivation (existsCode 40 (adjoinCode 34 32 40 41)) := by
  have hc := predicate_names_lt 34 32 42
  have hqc : 41 ≠ adjoinPredicate 34 32 42 := by omega
  have hdc : 40 ≠ adjoinPredicate 34 32 42 := by omega
  exact adjoin_graph_exists_fresh 34 32 42 41 40 (by decide) (by decide)
    (by decide) (by decide) (by decide) hqc (by decide) (by decide) (by decide) (by decide) hdc

theorem successor_suffix_adjoin_exists_certificate :
    theoremCode (certificate successor_suffix_adjoin_exists) =
      existsCode 40 (adjoinCode 34 32 40 41) :=
  certificate_correct successor_suffix_adjoin_exists

private def step : KDerivation (imp P.encode (imp A.encode B.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [A.encode,P.encode]
  have ha : Context Γ A.encode := .head _ _
  have hp : Context Γ P.encode := .hypothesis (by simp [Γ])
  have hn := Context.conjunctionLeft hp
  have hf := Context.conjunctionLeft (Context.conjunctionRight hp)
  have hs := Context.conjunctionRight (Context.conjunctionRight hp)
  have hg : Context Γ G.encode := by
    simpa [N,F,S,A,G,namedFilterBody,namedAdjoin,namedSuccessorBody,namedBoth,
      namedEither,Formula.not,Formula.encode,filterGraph,filterPredicate,
      successorCode,adjoinCode,both,neg,either] using
      (Context.mp ha (Context.mp hs (Context.mp hf (Context.mp hn (.closed successor_suffix)))))
  exact Context.conjunctionIntro ha hg

/-- A fresh suffix exists and is exactly the old suffix with the old result
adjoined; it also satisfies the new literal filter graph. -/
def successor_suffix_exists : KDerivation (imp (neg (member 33 32))
    (imp (filterGraph 32 34 35 (neg (member 33 35)))
      (imp (successorCode 32 38 39) (existsCode 40
        (both (adjoinCode 34 32 40 41) (filterGraph 38 40 35 (neg (member 33 35)))))))) := by
  have hcong := conditionalExistsCongr 40 (P.vacuity 40 fresh40) step
  have hex : KDerivation (existsCode 40 A.encode) := by
    simpa [A,namedAdjoin,namedBoth,namedEither,Formula.encode,adjoinCode,both,neg,either]
      using successor_suffix_adjoin_exists
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [successorCode 32 38 39, filterGraph 32 34 35 (neg (member 33 35)), neg (member 33 32)]
  have hn : Context Γ N.encode := by
    change Context Γ (neg (member 33 32))
    exact .hypothesis (by simp [Γ])
  have hf : Context Γ F.encode := by
    change Context Γ (filterGraph 32 34 35 (neg (member 33 35)))
    exact .hypothesis (by simp [Γ])
  have hs : Context Γ S.encode := by
    change Context Γ (successorCode 32 38 39)
    exact .head _ _
  have hp : Context Γ P.encode := Context.conjunctionIntro hn (Context.conjunctionIntro hf hs)
  have hresult : Context Γ (existsCode 40 B.encode) := .mp (.closed hex) (.mp hp (.closed hcong))
  change Context Γ (existsCode 40
    (both (adjoinCode 34 32 40 41) (filterGraph 38 40 35 (neg (member 33 35))))) at hresult
  exact hresult

theorem successor_suffix_exists_certificate : theoremCode (certificate successor_suffix_exists) =
    imp (neg (member 33 32)) (imp (filterGraph 32 34 35 (neg (member 33 35)))
      (imp (successorCode 32 38 39) (existsCode 40
        (both (adjoinCode 34 32 40 41) (filterGraph 38 40 35 (neg (member 33 35))))))) :=
  certificate_correct successor_suffix_exists
end PASoundness.PAtoCompactAdditionSuccessorSuffixExists
#print axioms PASoundness.PAtoCompactAdditionSuccessorSuffixExists.successor_suffix_adjoin_exists
#print axioms PASoundness.PAtoCompactAdditionSuccessorSuffixExists.successor_suffix_adjoin_exists_certificate
#print axioms PASoundness.PAtoCompactAdditionSuccessorSuffixExists.successor_suffix_exists
#print axioms PASoundness.PAtoCompactAdditionSuccessorSuffixExists.successor_suffix_exists_certificate
