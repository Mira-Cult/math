import PASoundness.PAtoCompactMultiplicationRowMapEdge
import PASoundness.PAtoCompactFixedFirstPreservedBase
import PASoundness.PAtoCompactFreeVacuity

/-! Eliminate the F-edge witness from an explicit inside-row successor
transformer. The transformer is a finite K proof-data input; this module
does not by itself prove the row successor step, row collection, or
multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstMapEdgeElim
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactFixedFirstPreservedBase
open PASoundness.PAtoCompactMultiplicationRowMapEdge
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- The post-step graph-existence goal, with prefix 0 renamed to successor 1. -/
def target : Formula := .ex 11 (replace 0 1 (rowInvariantPreserved 11))

/-- From a supplied inside-row transformer for each F-edge at value name 4,
use the supplied bijection and the source membership to obtain and eliminate
that edge. All graph, successor and prefix hypotheses remain explicit. -/
def inside_from_map
    (inside : KDerivation (imp (successorCode 0 1 2)
      (imp (member 31 0) (imp (rowInvariantPreserved 7).encode
        (imp (graphFormula 6 0 4).encode target.encode))))) :
    KDerivation (imp mapBijection.encode (imp (successorCode 0 1 2)
      (imp (member 31 0) (imp (rowInvariantPreserved 7).encode target.encode)))) := by
  let B := mapBijection
  let S := namedSuccessor 0 1 2
  let Y : Formula := .member 31 0
  let O := rowInvariantPreserved 7
  let F := graphFormula 6 0 4
  let Γ := [O.encode,Y.encode,S.encode,B.encode]
  have hvE : KDerivation (imp target.encode (allCode 4 target.encode)) :=
    free_vacuity 4 target (by decide)
  have hv : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 4 q)) := by
    intro q hq
    simp only [Γ,List.mem_cons,List.not_mem_nil,or_false] at hq
    by_cases hO : q = O.encode
    · subst q; exact free_vacuity 4 O (by decide)
    · by_cases hY : q = Y.encode
      · subst q; exact Y.vacuity 4 (by decide)
      · by_cases hS : q = S.encode
        · subst q; exact S.vacuity 4 (by decide)
        · have hB : q = B.encode := by simpa [hO,hY,hS] using hq
          subst q; exact free_vacuity 4 B (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hb : Context Γ mapBijection.encode := .hypothesis (by simp [Γ,B])
  have hs : Context Γ (successorCode 0 1 2) := by
    have h : Context Γ S.encode := .hypothesis (by simp [Γ])
    simpa [S,namedSuccessor,namedSuccessorBody,namedBoth,namedEither,
      Formula.not,Formula.encode,successorCode,both,neg,either] using h
  have hy : Context Γ (member 31 0) := .hypothesis (by simp [Γ,Y,Formula.encode])
  have ho : Context Γ (rowInvariantPreserved 7).encode := .hypothesis (by simp [Γ,O])
  have hex : Context Γ (existsCode 4 F.encode) :=
    .mp hy (.mp hb (.closed source_point_has_edge))
  apply Context.existsElim hvE _ hex
  apply Context.generalize 4 hv
  apply Context.deduction
  let Δ := F.encode :: Γ
  have hf : Context Δ F.encode := .head _ _
  exact .mp hf (.mp (.under ho _) (.mp (.under hy _) (.mp (.under hs _) (.closed inside))))

theorem inside_from_map_certificate
    (inside : KDerivation (imp (successorCode 0 1 2)
      (imp (member 31 0) (imp (rowInvariantPreserved 7).encode
        (imp (graphFormula 6 0 4).encode target.encode))))) :
    theoremCode (certificate (inside_from_map inside)) =
      imp mapBijection.encode (imp (successorCode 0 1 2)
        (imp (member 31 0) (imp (rowInvariantPreserved 7).encode target.encode))) :=
  certificate_correct (inside_from_map inside)
end PASoundness.PAtoCompactFixedFirstMapEdgeElim
#print axioms PASoundness.PAtoCompactFixedFirstMapEdgeElim.inside_from_map
#print axioms PASoundness.PAtoCompactFixedFirstMapEdgeElim.inside_from_map_certificate
