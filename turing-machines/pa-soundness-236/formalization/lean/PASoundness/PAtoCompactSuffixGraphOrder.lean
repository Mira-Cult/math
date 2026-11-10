import PASoundness.PAtoCompactSegmentRestrictedOrderAll
import PASoundness.PAtoCompactRestrictionSubset

/-! Order preservation on one supplied graph restricted to two suffixes.
Both suffix filters, the original order clause and the graph endpoint filter
are explicit. This does not construct the graph, prove coverage or uniqueness,
or establish suffix equivalence. Numeric labels are syntactic names; the
objects assigned to them may coincide. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuffixGraphOrder
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactGraphRestriction
open PASoundness.PAtoCompactRestrictionFilterVacuity PASoundness.PAtoCompactRestrictionSubset
open PASoundness.PAtoCompactRestrictedOrderInstance
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact filters for source suffix 40, target suffix 41, and graph 8. -/
def sourceFilter : Nat := filterGraph 0 40 42 (neg (member 2 42))
def targetFilter : Nat := filterGraph 1 41 43 (neg (member 5 43))
def graphFilter : Nat := filterGraph 6 8 14 (edgePredicate 14 40 41).encode

/-- The complete order clause on the *same* supplied graph 8, restricted to
suffix endpoints 40 and 41. The comparison uses literal membership order. -/
def suffixOrder : Nat :=
  allCode 30 (allCode 31 (allCode 32 (allCode 33
    (imp (both (member 40 30) (both (member 40 31)
      (both (member 41 32) (both (member 41 33)
        (both (graphFormula 8 30 32).encode (graphFormula 8 31 33).encode)))))
      (both (imp (member 31 30) (member 33 32))
        (imp (member 33 32) (member 31 30)))))))

private def namedSource : Formula := .all 42 (namedBoth
  (.imp (.member 40 42) (namedBoth (.member 0 42) (Formula.member 2 42).not))
  (.imp (namedBoth (.member 0 42) (Formula.member 2 42).not) (.member 40 42)))
private def namedTarget : Formula := .all 43 (namedBoth
  (.imp (.member 41 43) (namedBoth (.member 1 43) (Formula.member 5 43).not))
  (.imp (namedBoth (.member 1 43) (Formula.member 5 43).not) (.member 41 43)))

private theorem named_source_code : namedSource.encode = sourceFilter := by
  simp [namedSource, sourceFilter, namedBoth, Formula.not, Formula.encode,
    filterGraph, filterPredicate, CompactProof.both, CompactProof.neg]
private theorem named_target_code : namedTarget.encode = targetFilter := by
  simp [namedTarget, targetFilter, namedBoth, Formula.not, Formula.encode,
    filterGraph, filterPredicate, CompactProof.both, CompactProof.neg]

private def premise_vacuity (n : Nat)
    (hs : n ∉ namedSource.names) (ht : n ∉ namedTarget.names)
    (ho : n ∉ orderFormula.names) (hg : n ∉ (namedFilter 6 8 14 40 41).names) :
    ∀ z, z ∈ [graphFilter,orderFormula.encode,targetFilter,sourceFilter] →
      KDerivation (imp z (allCode n z)) := by
  intro z hz
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
  by_cases he : z = graphFilter
  · subst z
    simpa only [graphFilter] using restriction_filter_vacuity 6 8 14 40 41 n hg
  by_cases he : z = orderFormula.encode
  · subst z; exact orderFormula.vacuity n ho
  by_cases he : z = targetFilter
  · subst z; simpa only [named_target_code] using namedTarget.vacuity n ht
  have he : z = sourceFilter := by simp_all
  subst z
  simpa only [named_source_code] using namedSource.vacuity n hs

/-- Pointwise extraction of original edges and outer membership, followed by
the tracked order instance and four capture-safe universal generalizations.
The assumptions retain the exact source, target and graph filters. -/
def suffix_graph_order : KDerivation
    (imp sourceFilter (imp targetFilter (imp orderFormula.encode (imp graphFilter suffixOrder)))) := by
  let F := sourceFilter
  let G := targetFilter
  let O := orderFormula.encode
  let H := graphFilter
  let A := member 40 30
  let B := member 40 31
  let C := member 41 32
  let D := member 41 33
  let E := (graphFormula 8 30 32).encode
  let J := (graphFormula 8 31 33).encode
  let Guard := both A (both B (both C (both D (both E J))))
  let Result := both (imp (member 31 30) (member 33 32))
    (imp (member 33 32) (member 31 30))
  let Γ := [H,O,G,F]
  have hp : Context Γ (imp Guard Result) := by
    apply Context.deduction
    let Δ := Guard :: Γ
    have hd : Context Δ Guard := .head _ _
    have hf : Context Δ F := .hypothesis (by simp [Δ,Γ])
    have hg : Context Δ G := .hypothesis (by simp [Δ,Γ])
    have ho : Context Δ O := .hypothesis (by simp [Δ,Γ])
    have hh : Context Δ H := .hypothesis (by simp [Δ,Γ])
    have ha : Context Δ A := Context.conjunctionLeft hd
    have hb : Context Δ B := Context.conjunctionLeft (Context.conjunctionRight hd)
    have hc : Context Δ C := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight hd))
    have hx : Context Δ D := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hd)))
    have he : Context Δ E := Context.conjunctionLeft (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hd))))
    have hj : Context Δ J := Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight (Context.conjunctionRight hd))))
    have ha0 : Context Δ (member 0 30) := .mp ha (.mp hf (.closed
      (filter_member_source 0 40 42 (neg (member 2 42)) 30 (by decide) (by decide) (by decide))))
    have hb0 : Context Δ (member 0 31) := .mp hb (.mp hf (.closed
      (filter_member_source 0 40 42 (neg (member 2 42)) 31 (by decide) (by decide) (by decide))))
    have hc1 : Context Δ (member 1 32) := .mp hc (.mp hg (.closed
      (filter_member_source 1 41 43 (neg (member 5 43)) 32 (by decide) (by decide) (by decide))))
    have hd1 : Context Δ (member 1 33) := .mp hx (.mp hg (.closed
      (filter_member_source 1 41 43 (neg (member 5 43)) 33 (by decide) (by decide) (by decide))))
    have hfresh : 19 ∉ (namedFilter 6 8 14 40 41).names := by decide
    have he0 : Context Δ (graphFormula 6 30 32).encode := .mp he (.mp hh (.closed
      (PAtoCompactRestrictionEdgeReverseClosed.restricted_edge_source 6 8 14 40 41 30 32
        (by decide) (by decide) (by decide) hfresh)))
    have hj0 : Context Δ (graphFormula 6 31 33).encode := .mp hj (.mp hh (.closed
      (PAtoCompactRestrictionEdgeReverseClosed.restricted_edge_source 6 8 14 40 41 31 33
        (by decide) (by decide) (by decide) hfresh)))
    exact .mp hj0 (.mp he0 (.mp hd1 (.mp hc1 (.mp hb0 (.mp ha0
      (.mp ho (.closed guarded_order_fresh)))))))
  have h33 := Context.generalize 33 (premise_vacuity 33 (by decide) (by decide) (by decide) (by decide)) hp
  have h32 := Context.generalize 32 (premise_vacuity 32 (by decide) (by decide) (by decide) (by decide)) h33
  have h31 := Context.generalize 31 (premise_vacuity 31 (by decide) (by decide) (by decide) (by decide)) h32
  have h30 := Context.generalize 30 (premise_vacuity 30 (by decide) (by decide) (by decide) (by decide)) h31
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact h30

theorem suffix_graph_order_certificate : theoremCode (certificate suffix_graph_order) =
    imp sourceFilter (imp targetFilter (imp orderFormula.encode (imp graphFilter suffixOrder))) :=
  certificate_correct suffix_graph_order

end PASoundness.PAtoCompactSuffixGraphOrder

#print axioms PASoundness.PAtoCompactSuffixGraphOrder.suffix_graph_order
#print axioms PASoundness.PAtoCompactSuffixGraphOrder.suffix_graph_order_certificate
