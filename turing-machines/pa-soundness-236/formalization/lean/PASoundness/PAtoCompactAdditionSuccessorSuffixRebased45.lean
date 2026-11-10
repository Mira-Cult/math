import PASoundness.PAtoCompactAdditionSuccessorSuffixExists

/-! Capture-safe rebasing of the result-successor name in the literal K
successor suffix construction. The new result name is 45, distinct from the
source-successor name 38 used in the graph-extension construction. The old
suffix and its filter, result successor and nonmembership remain explicit K
antecedents. This does not prove the graph isomorphism or addition totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorSuffixRebased45
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactPointAdjoin
open PASoundness.PAtoCompactAdditionSuccessorSuffixExists
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def N : Formula := (Formula.member 33 32).not
private def F : Formula := .all 35 (namedFilterBody 32 34 35 (Formula.member 33 35).not)
private def S (z : Nat) : Formula := .all 39 (namedSuccessorBody 32 z 39)
private def A : Formula := namedAdjoin 34 32 40 41
private def G (z : Nat) : Formula := .all 35 (namedFilterBody z 40 35 (Formula.member 33 35).not)
private def stmt (z : Nat) : Formula := .imp N (.imp F (.imp (S z) (.ex 40 (namedBoth A (G z)))))

private theorem stmt_code (z : Nat) : (stmt z).encode =
    imp (neg (member 33 32)) (imp (filterGraph 32 34 35 (neg (member 33 35)))
      (imp (successorCode 32 z 39) (existsCode 40
        (both (adjoinCode 34 32 40 41) (filterGraph z 40 35 (neg (member 33 35))))))) := by rfl

/-- The original suffix constructor at a result-successor name 45. Its
independent name avoids identifying the result successor with a separately
named successor of the second summand. -/
def successor_suffix_exists_45 : KDerivation (imp (neg (member 33 32))
    (imp (filterGraph 32 34 35 (neg (member 33 35)))
      (imp (successorCode 32 45 39) (existsCode 40
        (both (adjoinCode 34 32 40 41) (filterGraph 45 40 35 (neg (member 33 35)))))))) := by
  have h : KDerivation (stmt 38).encode := by
    rw [stmt_code]
    exact successor_suffix_exists
  have hi := universalInstance 38 45 (stmt 38) (by decide) (by decide) (by decide)
  have hrep : replace 38 45 (stmt 38) = stmt 45 := by decide
  rw [hrep] at hi
  have hout : KDerivation (stmt 45).encode := .mp (.generalize 38 h) hi
  simpa only [stmt_code] using hout

theorem successor_suffix_exists_45_certificate :
    theoremCode (certificate successor_suffix_exists_45) =
      imp (neg (member 33 32))
        (imp (filterGraph 32 34 35 (neg (member 33 35)))
          (imp (successorCode 32 45 39) (existsCode 40
            (both (adjoinCode 34 32 40 41) (filterGraph 45 40 35 (neg (member 33 35))))))) :=
  certificate_correct successor_suffix_exists_45
end PASoundness.PAtoCompactAdditionSuccessorSuffixRebased45
#print axioms PASoundness.PAtoCompactAdditionSuccessorSuffixRebased45.successor_suffix_exists_45
#print axioms PASoundness.PAtoCompactAdditionSuccessorSuffixRebased45.successor_suffix_exists_45_certificate
