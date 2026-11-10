import PASoundness.PAtoCompactAdditionBinaryGraphPoint
import PASoundness.PAtoCompactBinaryGraphFunctionalFromPointFresh

/-! Lift the addition graph-aware point to guarded binary term-graph
functionality, using the original guard and explicit child proofs. -/
namespace PASoundness.PAtoCompactAdditionBinaryFunctionalGuarded

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstBinaryStep
open PASoundness.PAtoCompactAdditionBinaryGraphPoint PASoundness.PAtoCompactBinaryGraphFunctionalFromPointFresh

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The two child functionality proofs lift to the addition node. All
freshness and allocator conditions are explicit. -/
noncomputable def addition_functionality_fresh {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b c p q e f : Nat) (g : Formula)
    (hbc : b+1 < c) (hp : p < b) (hq : q < b)
    (ht : ∀ a ∈ t.varFinset, v a < b) (hu : ∀ a ∈ u.varFinset, v a < b)
    (hg : ∀ a ∈ g.free, a < b)
    (hbe : b+1 < e+2) (hce : c+1 < e+2) (hpf : p < f+2) (hqf : q < f+2)
    (left : KDerivation (imp g.encode
      (imp (termGraph v t b (b+64)).encode
        (imp (termGraph v t c (c+64)).encode (equivAt e b c).encode))))
    (right : KDerivation (imp g.encode
      (imp (termGraph v u (b+1) (b+64+termCost t)).encode
        (imp (termGraph v u (c+1) (c+64+termCost t)).encode
          (equivAt e (b+1) (c+1)).encode)))) :
    KDerivation (imp g.encode
      (imp (termGraph v (binaryTerm true t u) p b).encode
        (imp (termGraph v (binaryTerm true t u) q c).encode (equivAt f p q).encode))) := by
  have hpoint := addition_binary_point v t u b c p q e f g hbe hce
    (by omega) (by omega) (by omega) (by omega) hpf hqf left right
  exact binary_functionality_from_point_fresh v t u true b c p q f g hbc hp hq ht hu hg hpoint

end PASoundness.PAtoCompactAdditionBinaryFunctionalGuarded

#print axioms PASoundness.PAtoCompactAdditionBinaryFunctionalGuarded.addition_functionality_fresh
