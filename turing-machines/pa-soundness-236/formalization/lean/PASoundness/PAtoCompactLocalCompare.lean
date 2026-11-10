import PASoundness.PAtoCompactPairGraphCompare
import PASoundness.PAtoCompactPairWitnessElim

/-! Two elements of one set satisfying the displayed least-subsets condition
are comparable. This K derivation does not establish comparability across
separate domain objects or a quotient by order type. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLocalCompare
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactPairFilter PASoundness.PAtoCompactPairGraphCompare
open PASoundness.PAtoCompactPairWitnessElim

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The filtered-pair graph is constructed and eliminated; no pair witness is
assumed in the conclusion. All displayed names, including the generated witness,
are pairwise fresh. -/
def local_comparable (x t a b u s m r : Nat)
    (fresh : [x,t,a,b,u,s,m,r,pairWitness x t a b].Nodup) :
    KDerivation (imp (leastSubsetsCode x u t s m r) (imp (member x a) (imp (member x b)
      (either (equal a b) (either (member b a) (member a b)))))) := by
  have hxt : x ≠ t := by intro h; have hf := fresh; simp [h] at hf
  have hcu : pairWitness x t a b ≠ u := by intro h; have hf := fresh; simp [h] at hf
  have hct : pairWitness x t a b ≠ t := by intro h; have hf := fresh; simp [h] at hf
  have hcs : pairWitness x t a b ≠ s := by intro h; have hf := fresh; simp [h] at hf
  have hcm : pairWitness x t a b ≠ m := by intro h; have hf := fresh; simp [h] at hf
  have hcr : pairWitness x t a b ≠ r := by intro h; have hf := fresh; simp [h] at hf
  exact eliminate_pair_witness x t a b u t s m r hxt hcu hct hcs hcm hcr
    (compare_from_pair_graph x t a b u s m r fresh)

theorem local_comparable_certificate (x t a b u s m r : Nat)
    (fresh : [x,t,a,b,u,s,m,r,pairWitness x t a b].Nodup) :
    theoremCode (certificate (local_comparable x t a b u s m r fresh)) =
      imp (leastSubsetsCode x u t s m r) (imp (member x a) (imp (member x b)
        (either (equal a b) (either (member b a) (member a b))))) :=
  certificate_correct (local_comparable x t a b u s m r fresh)

end PASoundness.PAtoCompactLocalCompare

#print axioms PASoundness.PAtoCompactLocalCompare.local_comparable
#print axioms PASoundness.PAtoCompactLocalCompare.local_comparable_certificate
