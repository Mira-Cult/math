import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactDerivations

/-! Pointwise order reversal under explicit inverse-edge hypotheses. This is
literal K proof data; it does not construct an inverse graph, quantify the
edge hypotheses, or establish symmetry of the candidate isomorphism. Compact
negation uses literal code 1, with no semantic soundness assumption. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactIsoInversePoint
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Two supplied pointwise reverse-to-forward edge implications and a
forward edge-guarded order biconditional yield the reversed biconditional.
All arguments are literal compact formula codes; no freshness is required
for this propositional transformation. -/
def reverse_pointwise (G₁ G₂ H₁ H₂ M N : Nat) :
    KDerivation (imp (imp H₁ G₁) (imp (imp H₂ G₂)
      (imp (imp (both G₁ G₂) (both (imp M N) (imp N M)))
        (imp (both H₁ H₂) (both (imp N M) (imp M N)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let A := imp H₁ G₁
  let B := imp H₂ G₂
  let C := imp (both G₁ G₂) (both (imp M N) (imp N M))
  let D := both H₁ H₂
  let Γ := [D,C,B,A]
  have hd : Context Γ D := Context.head _ _
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hg₁ : Context Γ G₁ := .mp (Context.conjunctionLeft hd) ha
  have hg₂ : Context Γ G₂ := .mp (Context.conjunctionRight hd) hb
  have hm : Context Γ (both (imp M N) (imp N M)) :=
    .mp (Context.conjunctionIntro hg₁ hg₂) hc
  exact Context.conjunctionIntro (Context.conjunctionRight hm) (Context.conjunctionLeft hm)

theorem reverse_pointwise_certificate (G₁ G₂ H₁ H₂ M N : Nat) :
    theoremCode (certificate (reverse_pointwise G₁ G₂ H₁ H₂ M N)) =
      imp (imp H₁ G₁) (imp (imp H₂ G₂)
        (imp (imp (both G₁ G₂) (both (imp M N) (imp N M)))
          (imp (both H₁ H₂) (both (imp N M) (imp M N))))) :=
  certificate_correct (reverse_pointwise G₁ G₂ H₁ H₂ M N)

/-- Specialization to the exact Kuratowski graph predicate in the candidate
isomorphism. Names 2,4 are input coordinates, 3,5 output coordinates, 6 the
forward graph, and 8 the alleged reverse graph; the graph formula itself
binds names 19–22. The forward order clause is an explicit local premise. -/
def candidate_reverse_pointwise : KDerivation
    (let G₁ := (graphFormula 6 2 3).encode
     let G₂ := (graphFormula 6 4 5).encode
     let H₁ := (graphFormula 8 3 2).encode
     let H₂ := (graphFormula 8 5 4).encode
     let M := member 4 2
     let N := member 5 3
     imp (imp H₁ G₁) (imp (imp H₂ G₂)
       (imp (imp (both G₁ G₂) (both (imp M N) (imp N M)))
         (imp (both H₁ H₂) (both (imp N M) (imp M N)))))) :=
  reverse_pointwise _ _ _ _ _ _

theorem candidate_reverse_pointwise_certificate :
    theoremCode (certificate candidate_reverse_pointwise) =
      (let G₁ := (graphFormula 6 2 3).encode
       let G₂ := (graphFormula 6 4 5).encode
       let H₁ := (graphFormula 8 3 2).encode
       let H₂ := (graphFormula 8 5 4).encode
       let M := member 4 2
       let N := member 5 3
       imp (imp H₁ G₁) (imp (imp H₂ G₂)
         (imp (imp (both G₁ G₂) (both (imp M N) (imp N M)))
           (imp (both H₁ H₂) (both (imp N M) (imp M N)))))) :=
  certificate_correct candidate_reverse_pointwise

end PASoundness.PAtoCompactIsoInversePoint

#print axioms PASoundness.PAtoCompactIsoInversePoint.reverse_pointwise
#print axioms PASoundness.PAtoCompactIsoInversePoint.candidate_reverse_pointwise
#print axioms PASoundness.PAtoCompactIsoInversePoint.candidate_reverse_pointwise_certificate
