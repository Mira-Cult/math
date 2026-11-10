import PASoundness.PAtoCompactSuffixGraphMatrixAlignment
import PASoundness.PAtoCompactSuffixGraphFilterExists

/-! Existential elimination of the same selected suffix-restriction graph.
The original isomorphism's matrix and selected matching cut edge remain
explicit hypotheses. This is the proper-cut suffix ingredient, not an
addition output-transport theorem or the whole-output-cut case. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuffixGraphEquivalent
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuffixBoundaryPoint PASoundness.PAtoCompactSuffixGraphForwardCoverage
open PASoundness.PAtoCompactSuffixGraphMatrix PASoundness.PAtoCompactSuffixGraphMatrixAlignment
open PASoundness.PAtoCompactSuffixGraphQuotientAlignment PASoundness.PAtoCompactSuffixGraphFilterExists
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def sourceFilterNamed : Formula :=
  .all 42 (namedFilterBody 0 40 42 (Formula.member 2 42).not)
private def targetFilterNamed : Formula :=
  .all 43 (namedFilterBody 1 41 43 (Formula.member 5 43).not)
private theorem source_filter_code : sourceFilterNamed.encode = sourceFilter := by rfl
private theorem target_filter_code : targetFilterNamed.encode = targetFilter := by rfl

/-- Under one original isomorphism graph6, its order/bijection matrices, actual
matched cut edge2→5 and cut memberships, the two supplied relative-complement
suffixes40 and41 are isomorphic. K constructs and eliminates one graph8,
using the same graph for forward, reverse and order clauses. Fixed names are
syntactic; the denoted objects may coincide. -/
noncomputable def suffix_graph_equivalent : KDerivation
    (imp orderFormula.encode (imp sourceFilter (imp targetFilter
      (imp (member 0 2) (imp (member 1 5) (imp (graphFormula 6 2 5).encode
        (imp bijectionFormula.encode suffixEquivalent.encode))))))) := by
  let O := orderFormula.encode
  let S := sourceFilter
  let T := targetFilter
  let C := member 0 2
  let D := member 1 5
  let E := (graphFormula 6 2 5).encode
  let B := bijectionFormula.encode
  let F := graphFilter
  let R := suffixEquivalent.encode
  let Γ := [B,E,D,C,T,S,O]
  have hpoint : Context Γ (imp F R) := by
    apply Context.deduction
    let Δ := F :: Γ
    have hf : Context Δ F := .head _ _
    have hb : Context Δ B := .hypothesis (by simp [Δ,Γ])
    have he : Context Δ E := .hypothesis (by simp [Δ,Γ])
    have hd : Context Δ D := .hypothesis (by simp [Δ,Γ])
    have hc : Context Δ C := .hypothesis (by simp [Δ,Γ])
    have ht : Context Δ T := .hypothesis (by simp [Δ,Γ])
    have hs : Context Δ S := .hypothesis (by simp [Δ,Γ])
    have ho : Context Δ O := .hypothesis (by simp [Δ,Γ])
    have hm : Context Δ suffixMatrix :=
      .mp hf (.mp hb (.mp he (.mp hd (.mp hc (.mp ht (.mp hs
        (.mp ho (.closed suffix_graph_matrix))))))))
    have hbody : Context Δ suffixMatrixNamed.encode := by
      simpa only [suffix_matrix_body_code] using hm
    have hi : Context Δ (existsCode 8 suffixMatrix) := by
      have h := Context.mp hbody (.closed (existsIntroduce 8 suffixMatrixNamed (by decide)))
      simpa only [suffix_matrix_body_code] using h
    exact .mp hi (.closed suffix_matrix_to_equivalent)
  have hv : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 8 z)) := by
    intro z hz
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hz
    by_cases h : z = B
    · subst z; exact bijectionFormula.vacuity 8 (by decide)
    by_cases h : z = E
    · subst z; exact (graphFormula 6 2 5).vacuity 8 (by decide)
    by_cases h : z = D
    · subst z; exact membershipVacuity 1 5 8 (by decide) (by decide)
    by_cases h : z = C
    · subst z; exact membershipVacuity 0 2 8 (by decide) (by decide)
    by_cases h : z = T
    · subst z; simpa only [T, ← target_filter_code] using (targetFilterNamed.vacuity 8 (by decide))
    by_cases h : z = S
    · subst z; simpa only [S, ← source_filter_code] using (sourceFilterNamed.vacuity 8 (by decide))
    have h : z = O := by simp_all
    subst z
    exact orderFormula.vacuity 8 (by decide)
  have hall : Context Γ (allCode 8 (imp F R)) := Context.generalize 8 hv hpoint
  have hres : Context Γ R := Context.existsElim (suffixEquivalent.vacuity 8 (by decide))
    hall (.closed suffix_graph_filter_exists)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hres

theorem suffix_graph_equivalent_certificate :
    theoremCode (certificate suffix_graph_equivalent) =
      imp orderFormula.encode (imp sourceFilter (imp targetFilter
        (imp (member 0 2) (imp (member 1 5) (imp (graphFormula 6 2 5).encode
          (imp bijectionFormula.encode suffixEquivalent.encode)))))) :=
  certificate_correct suffix_graph_equivalent

end PASoundness.PAtoCompactSuffixGraphEquivalent

#print axioms PASoundness.PAtoCompactSuffixGraphEquivalent.suffix_graph_equivalent
#print axioms PASoundness.PAtoCompactSuffixGraphEquivalent.suffix_graph_equivalent_certificate
