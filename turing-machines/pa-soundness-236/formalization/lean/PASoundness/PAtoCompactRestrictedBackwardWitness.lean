import PASoundness.PAtoCompactRestrictedBackwardUnique
import PASoundness.PAtoCompactRestrictedBackwardPoint
import PASoundness.PAtoCompactRestrictionFilterVacuity
import PASoundness.PAtoCompactTransitiveWitness

/-! Transfer one actual backward-bijection witness to the supplied endpoint
restriction, retaining that very same witness and its uniqueness clause. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedBackwardWitness
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactRestrictedBackwardPoint PASoundness.PAtoCompactRestrictionFilterVacuity
open PASoundness.PAtoCompactBijectionBackwardAtThree PASoundness.PAtoCompactRestrictedBackwardUnique
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The exact old-domain reverse-bijection body for preimage 7 of target 3,
with uniqueness tested in the restricted graph 8. -/
def restrictedWitness : Formula := namedBoth (.member 2 7) (namedBoth (graphFormula 8 7 3)
  (.all 4 (.imp (namedBoth (.member 2 4) (graphFormula 8 4 3)) (.equal 4 7))))

/-- Given the exact supplied successor graphs, order/bijection, endpoint
filter, top edge and old target membership 3∈5, K derives an existential
restricted backward witness including its uniqueness clause. The original
and restricted conclusions use the same existential name 7. Fixed labels
are syntactic; denoted objects may coincide. Code 1 is literal `member 0 0`.
This is one target instance, not yet the fully quantified bijection clause. -/
def backward_witness : KDerivation
    (imp sourceSuccessor (imp targetSuccessor (imp orderFormula.encode
      (imp bijectionFormula.encode (imp restriction (imp topEdge
        (imp (member 5 3) (existsCode 7 restrictedWitness.encode)))))))) := by
  let SX := sourceSuccessor
  let SY := targetSuccessor
  let O := orderFormula.encode
  let B := bijectionFormula.encode
  let F := restriction
  let T := topEdge
  let V := member 5 3
  let W := (witness 7).encode
  let R := restrictedWitness.encode
  let Γ := [V,T,F,B,O,SY,SX]
  have hctx : ∀ z, z ∈ Γ → KDerivation (imp z (allCode 7 z)) := by
    intro z hz
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hz
    by_cases he : z = V
    · subst z; exact membershipVacuity 5 3 7 (by decide) (by decide)
    by_cases he : z = T
    · subst z; exact (graphFormula 6 2 5).vacuity 7 (by decide)
    by_cases he : z = F
    · subst z; exact restriction_filter_vacuity 6 8 14 2 5 7 (by decide)
    by_cases he : z = B
    · subst z; exact bijectionFormula.vacuity 7 (by decide)
    by_cases he : z = O
    · subst z; exact orderFormula.vacuity 7 (by decide)
    by_cases he : z = SY
    · subst z; exact successor_vacuity 5 1 10 7 (by decide) (by decide) (by decide)
    have he : z = SX := by simp_all
    subst z
    exact successor_vacuity 2 0 9 7 (by decide) (by decide) (by decide)
  have hlocal : Context Γ (imp W R) := by
    apply Context.deduction
    let Δ := W :: Γ
    have hw : Context Δ W := .head _ _
    have hu : Context Δ (member 0 7) := Context.conjunctionLeft hw
    have he : Context Δ oldEdge := Context.conjunctionLeft (Context.conjunctionRight hw)
    have hsx : Context Δ SX := .hypothesis (by simp [Δ,Γ])
    have hsy : Context Δ SY := .hypothesis (by simp [Δ,Γ])
    have ho : Context Δ O := .hypothesis (by simp [Δ,Γ])
    have hf : Context Δ F := .hypothesis (by simp [Δ,Γ])
    have ht : Context Δ T := .hypothesis (by simp [Δ,Γ])
    have hv : Context Δ V := .hypothesis (by simp [Δ,Γ])
    have hpoint : Context Δ (both (member 2 7) restrictedEdge) :=
      .mp he (.mp hv (.mp hu (.mp ht (.mp hf (.mp ho
        (.mp hsy (.mp hsx (.closed backward_point))))))))
    have huniq : Context Δ (allCode 4
        (imp (both (member 2 4) (graphFormula 8 4 3).encode) (equal 4 7))) :=
      .mp hw (.mp hf (.mp hsx (.closed backward_unique)))
    exact Context.conjunctionIntro (Context.conjunctionLeft hpoint)
      (Context.conjunctionIntro (Context.conjunctionRight hpoint) huniq)
  have horiginal : Context Γ (existsCode 7 W) := by
    have hv : Context Γ V := .head _ _
    have hsy : Context Γ SY := .hypothesis (by simp [Γ])
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have hmember : Context Γ (member 1 3) :=
      .mp (Context.disjunctionRight hv)
        (.mp hsy (.closed (successor_include 5 1 10 3 (by decide) (by decide) (by decide))))
    exact .mp hmember (.mp hb (.closed PAtoCompactBijectionBackwardAtThree.backward_witness))
  have hresult : Context Γ (existsCode 7 R) :=
    exists_map_context (Context.generalize 7 hctx hlocal) horiginal
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hresult

theorem backward_witness_certificate : theoremCode (certificate backward_witness) =
    imp sourceSuccessor (imp targetSuccessor (imp orderFormula.encode
      (imp bijectionFormula.encode (imp restriction (imp topEdge
        (imp (member 5 3) (existsCode 7 restrictedWitness.encode))))))) :=
  certificate_correct backward_witness

end PASoundness.PAtoCompactRestrictedBackwardWitness

#print axioms PASoundness.PAtoCompactRestrictedBackwardWitness.backward_witness
#print axioms PASoundness.PAtoCompactRestrictedBackwardWitness.backward_witness_certificate
