import PASoundness.PAtoCompactMultiplicationNoGarbageAtEdge63
import PASoundness.PAtoCompactMultiplicationOldTripleIntro
import PASoundness.PAtoCompactMultiplicationRowQueryFirstExists

/-! The pointwise old/new branch split for an actual member edge of the
fixed-first row invariant. All queried pair descriptions are explicit; both
branches retain the same outer edge 63. No extensionality, unique pair
representatives, row collection or multiplication totality is assumed. -/
namespace PASoundness.PAtoCompactMultiplicationEdgeBranchFirst
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationNoGarbageAtEdge63
open PASoundness.PAtoCompactMultiplicationOldTripleIntro
open PASoundness.PAtoCompactMultiplicationRowQueryFirst
open PASoundness.PAtoCompactMultiplicationRowQueryFirstExists
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- If actual new-graph member 63 is the queried edge, the no-garbage
invariant gives either the queried old-graph triple or an explicit row-query
witness. The graph label 64 remains distinct from both queried coordinates. -/
def edge_branch : KDerivation (imp (noGarbage 64).encode
    (imp queryPairs.encode (imp (member 64 63)
      (either oldTriple.encode queriedNewRow.encode)))) := by
  let B := namedBoth queryPairs (replace 9 63 rowWitness)
  have hi63 := existsIntroduce 63 B (by decide)
  have hi18 := existsIntroduce 18 (.ex 63 B) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 64 63,queryPairs.encode,(noGarbage 64).encode]
  have hm : Context Γ (member 64 63) := .head _ _
  have hq : Context Γ queryPairs.encode := .hypothesis (by simp [Γ])
  have hn : Context Γ (noGarbage 64).encode := .hypothesis (by simp [Γ])
  have hq' : Context Γ (both (pairFormula 63 18 5).encode (pairFormula 18 3 4).encode) := by
    simpa [queryPairs,namedBoth,Formula.not,Formula.encode,both,neg] using hq
  have hcases : Context Γ (either (member 10 63) (replace 9 63 rowWitness).encode) :=
    .mp hm (.mp hn (.closed no_garbage_at_edge))
  apply Context.disjunctionElim hcases
  · let Δ := member 10 63 :: Γ
    have hold : Context Δ oldTriple.encode := .mp (.under (Context.conjunctionRight hq') _)
      (.mp (.under (Context.conjunctionLeft hq') _)
        (.mp (.head _ _) (.closed triple_from_shared_edge)))
    exact Context.disjunctionLeft hold
  · let Δ := (replace 9 63 rowWitness).encode :: Γ
    have hr : Context Δ (replace 9 63 rowWitness).encode := .head _ _
    have hb : Context Δ B.encode := by
      have hc := Context.conjunctionIntro (.under hq _) hr
      simpa [B,namedBoth,Formula.not,Formula.encode,both,neg] using hc
    have he63 : Context Δ (existsCode 63 B.encode) := .mp hb (.closed hi63)
    have he18 : Context Δ (existsCode 18 (existsCode 63 B.encode)) := .mp he63 (.closed hi18)
    have hrq : Context Δ queriedNewRow.encode := by simpa [queriedNewRow,B,Formula.encode] using he18
    exact Context.disjunctionRight hrq

theorem edge_branch_certificate : theoremCode (certificate edge_branch) =
    imp (noGarbage 64).encode (imp queryPairs.encode (imp (member 64 63)
      (either oldTriple.encode queriedNewRow.encode))) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationEdgeBranchFirst
#print axioms PASoundness.PAtoCompactMultiplicationEdgeBranchFirst.edge_branch
#print axioms PASoundness.PAtoCompactMultiplicationEdgeBranchFirst.edge_branch_certificate
