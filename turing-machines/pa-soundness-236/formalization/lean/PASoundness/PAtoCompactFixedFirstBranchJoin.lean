import PASoundness.PAtoCompactFixedFirstOutsideStep
import PASoundness.PAtoCompactMultiplicationRowMapEdge

/-! Finite K case split between inside- and outside-index row successors.
The inside branch remains an explicit proof-data input; this module does not
construct it, establish graph collection or prove multiplication totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFixedFirstBranchJoin
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFixedFirstPreservedBase
open PASoundness.PAtoCompactFixedFirstOutsideStep PASoundness.PAtoCompactMultiplicationRowMapEdge
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Given a finite K inside-branch proof, split on membership in the row
source and retain the actual outside-branch proof. -/
def join (inside : KDerivation (imp mapBijection.encode (imp (successorCode 0 1 2)
    (imp (member 31 0) (imp (existsCode 7 (rowInvariantPreserved 7).encode)
      (existsCode 7 (replace 0 1 (rowInvariantPreserved 7)).encode)))))) :
    KDerivation (imp mapBijection.encode (imp (successorCode 0 1 2)
      (imp (existsCode 7 (rowInvariantPreserved 7).encode)
        (existsCode 7 (replace 0 1 (rowInvariantPreserved 7)).encode)))) := by
  let B := mapBijection.encode
  let S := successorCode 0 1 2
  let X := member 31 0
  let O := existsCode 7 (rowInvariantPreserved 7).encode
  let N := existsCode 7 (replace 0 1 (rowInvariantPreserved 7)).encode
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [O,S,B]
  have ho : Context Γ O := .head _ _
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hex : Context Γ (either X (neg X)) := .closed (CompactHilbertBasis.identity (neg X))
  apply Context.disjunctionElim hex
  · let Δ := X :: Γ
    have hx : Context Δ X := .head _ _
    exact .mp (.under ho _) (.mp hx (.mp (.under hs _) (.mp (.under hb _) (.closed inside))))
  · let Δ := neg X :: Γ
    have hn : Context Δ (neg X) := .head _ _
    exact .mp (.under ho _) (.mp hn (.mp (.under hs _) (.closed outside_exists)))

theorem join_certificate (inside : KDerivation (imp mapBijection.encode (imp (successorCode 0 1 2)
    (imp (member 31 0) (imp (existsCode 7 (rowInvariantPreserved 7).encode)
      (existsCode 7 (replace 0 1 (rowInvariantPreserved 7)).encode)))))) :
    theoremCode (certificate (join inside)) = imp mapBijection.encode (imp (successorCode 0 1 2)
      (imp (existsCode 7 (rowInvariantPreserved 7).encode)
        (existsCode 7 (replace 0 1 (rowInvariantPreserved 7)).encode))) := certificate_correct _
end PASoundness.PAtoCompactFixedFirstBranchJoin
#print axioms PASoundness.PAtoCompactFixedFirstBranchJoin.join
#print axioms PASoundness.PAtoCompactFixedFirstBranchJoin.join_certificate
