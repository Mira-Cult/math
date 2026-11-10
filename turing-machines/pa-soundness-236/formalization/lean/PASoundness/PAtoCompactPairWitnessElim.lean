import PASoundness.PAtoCompactPairFilterBounds

/-! Explicit elimination of the selector-8 filtered-pair witness. The local
comparison under the pair graph remains an explicit proof premise. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPairWitnessElim
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactGreatestSuccessor
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactPairFilter
open PASoundness.PAtoCompactPairFilterBounds

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- If comparison follows from the exact filtered-pair graph, K eliminates
the generated pair witness. The displayed auxiliary binders must avoid its
computed numeric name. -/
def eliminate_pair_witness (x t a b u k e m r : Nat) (hxt : x ≠ t)
    (hcu : pairWitness x t a b ≠ u) (hck : pairWitness x t a b ≠ k)
    (hce : pairWitness x t a b ≠ e) (hcm : pairWitness x t a b ≠ m)
    (hcr : pairWitness x t a b ≠ r)
    (hlocal : KDerivation (imp (pairGraph x t a b)
      (imp (leastSubsetsCode x u k e m r) (imp (member x a) (imp (member x b)
        (either (equal a b) (either (member b a) (member a b)))))))) :
    KDerivation (imp (leastSubsetsCode x u k e m r) (imp (member x a) (imp (member x b)
      (either (equal a b) (either (member b a) (member a b)))))) := by
  let c := pairWitness x t a b
  let C := either (equal a b) (either (member b a) (member a b))
  let F := imp (leastSubsetsCode x u k e m r) (imp (member x a) (imp (member x b) C))
  let f : CompactNamed.Formula := .imp (.all u (namedLeastSubsetsBody x u k e m r))
    (.imp (.member x a) (.imp (.member x b) (namedEither (.equal a b)
      (namedEither (.member b a) (.member a b)))))
  have hb := pair_witness_bounds x t a b
  have hcx : c ≠ x := by dsimp [c]; omega
  have hca : c ≠ a := by dsimp [c]; omega
  have hcb : c ≠ b := by dsimp [c]; omega
  have hcu' : c ≠ u := hcu
  have hck' : c ≠ k := hck
  have hce' : c ≠ e := hce
  have hcm' : c ≠ m := hcm
  have hcr' : c ≠ r := hcr
  have hn : c ∉ f.names := by
    simp [f, namedLeastSubsetsBody, namedLeastMember, namedBoth, namedEither,
      CompactNamed.Formula.names, hcx, hca, hcb, hcu', hck', hce', hcm', hcr']
  have hv : KDerivation (imp F (allCode c F)) := by
    have h := f.vacuity c hn
    simpa [f, F, C, namedLeastSubsetsBody, namedLeastMember, namedBoth, namedEither,
      leastSubsetsCode, leastMemberCode, subsetCode, nonemptyCode,
      CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg,
      CompactDerivations.either] using h
  apply Context.closeEmpty
  exact Context.existsElim hv (.closed (.generalize c hlocal)) (.closed (pair_filter_exists x t a b hxt))

theorem eliminate_pair_witness_certificate (x t a b u k e m r : Nat) (hxt : x ≠ t)
    (hcu : pairWitness x t a b ≠ u) (hck : pairWitness x t a b ≠ k)
    (hce : pairWitness x t a b ≠ e) (hcm : pairWitness x t a b ≠ m)
    (hcr : pairWitness x t a b ≠ r)
    (hlocal : KDerivation (imp (pairGraph x t a b)
      (imp (leastSubsetsCode x u k e m r) (imp (member x a) (imp (member x b)
        (either (equal a b) (either (member b a) (member a b)))))))) :
    theoremCode (certificate (eliminate_pair_witness x t a b u k e m r hxt hcu hck hce hcm hcr hlocal)) =
      imp (leastSubsetsCode x u k e m r) (imp (member x a) (imp (member x b)
        (either (equal a b) (either (member b a) (member a b))))) :=
  certificate_correct (eliminate_pair_witness x t a b u k e m r hxt hcu hck hce hcm hcr hlocal)

end PASoundness.PAtoCompactPairWitnessElim

#print axioms PASoundness.PAtoCompactPairWitnessElim.eliminate_pair_witness
#print axioms PASoundness.PAtoCompactPairWitnessElim.eliminate_pair_witness_certificate
