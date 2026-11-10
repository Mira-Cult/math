import PASoundness.PAtoCompactPairFilter
import PASoundness.PAtoCompactLeastPairExists
import PASoundness.PAtoCompactLeastSuccessorEmpty

/-! A graph-conditional K comparison step for two selected members. The pair
witness and the least-subsets condition remain explicit premises. The final
existential elimination of the pair witness is separate. Code 1 is literally
`member 0 0`; no semantic soundness is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPairGraphCompare
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactPairFilter PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactLeastPairExists PASoundness.PAtoCompactLeastSuccessorEmpty
open PASoundness.PAtoCompactPredecessor

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Under an exact x-filtered pair graph and a least-subsets hypothesis, two
x-members a and b are comparable. All generated and user names are pairwise
fresh in this bounded interface. -/
def compare_from_pair_graph (x t a b u s m r : Nat)
    (fresh : [x,t,a,b,u,s,m,r,pairWitness x t a b].Nodup) :
    KDerivation (imp (pairGraph x t a b) (imp (leastSubsetsCode x u t s m r)
      (imp (member x a) (imp (member x b)
        (either (equal a b) (either (member b a) (member a b))))))) := by
  let c := pairWitness x t a b
  have hxt : x ≠ t := by intro h; have hf := fresh; simp [h] at hf
  have hta : t ≠ a := by intro h; have hf := fresh; simp [h] at hf
  have htb : t ≠ b := by intro h; have hf := fresh; simp [h] at hf
  have htm : t ≠ m := by intro h; have hf := fresh; simp [h] at hf
  have hux : u ≠ x := by intro h; have hf := fresh; simp [h] at hf
  have huc : u ≠ c := by intro h; have hf := fresh; simp [h, c] at hf
  have hut : u ≠ t := by intro h; have hf := fresh; simp [h] at hf
  have hus : u ≠ s := by intro h; have hf := fresh; simp [h] at hf
  have hum : u ≠ m := by intro h; have hf := fresh; simp [h] at hf
  have hur : u ≠ r := by intro h; have hf := fresh; simp [h] at hf
  have hct : c ≠ t := by intro h; have hf := fresh; simp [h, c] at hf
  have hcs : c ≠ s := by intro h; have hf := fresh; simp [h, c] at hf
  have hcm : c ≠ m := by intro h; have hf := fresh; simp [h, c] at hf
  have hcr : c ≠ r := by intro h; have hf := fresh; simp [h, c] at hf
  have hsc : s ≠ c := Ne.symm hcs
  have hsa : s ≠ a := by intro h; have hf := fresh; simp [h] at hf
  have hmx : m ≠ x := by intro h; have hf := fresh; simp [h] at hf
  have hmt : m ≠ t := Ne.symm htm
  have hma : m ≠ a := by intro h; have hf := fresh; simp [h] at hf
  have hmb : m ≠ b := by intro h; have hf := fresh; simp [h] at hf
  have hmc : m ≠ c := Ne.symm hcm
  have hcmp : [c,m,r,a,b].Nodup := by
    dsimp [c]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, not_false_eq_true] at fresh ⊢
    aesop
  let G := pairGraph x t a b
  let L := leastSubsetsCode x u t s m r
  let C := either (equal a b) (either (member b a) (member a b))
  let E := imp (member c m) (either (equal m a) (equal m b))
  let f : CompactNamed.Formula := .all t (namedPairBody x t a b)
  have hmfree : m ∉ f.names := by
    simp [f, namedPairBody, namedBoth, namedEither, CompactNamed.Formula.names,
      hmx, hmt, hma, hmb, hmc, c]
  have hgv : KDerivation (imp G (allCode m G)) := by
    have h := f.vacuity m hmfree
    simpa [f, G, namedPairBody, namedBoth, namedEither, CompactNamed.Formula.encode,
      pairGraph, pairWitness, pairPredicate, filterGraph, filterPredicate,
      CompactProof.both, CompactProof.neg, CompactDerivations.either] using h
  have hge : KDerivation (imp G (allCode m E)) := by
    have hpoint : KDerivation (imp G E) := pair_filter_member_cases x t a b m hxt hta htb htm
    apply Context.closeEmpty
    apply Context.deduction
    have hg : Context [G] G := Context.head [] G
    have hgm : Context [G] (allCode m G) := .mp hg (.closed hgv)
    exact Context.allMP hgm (.closed (.generalize m hpoint))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member x b,member x a,L,G]
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hl : Context Γ L := .hypothesis (by simp [Γ])
  have ha : Context Γ (member x a) := .hypothesis (by simp [Γ])
  have hb : Context Γ (member x b) := .hypothesis (by simp [Γ])
  have hca : Context Γ (member c a) := .mp ha (.mp hg (.closed (pair_filter_member_left x t a b hxt hta htb)))
  have hcb : Context Γ (member c b) := .mp hb (.mp hg (.closed (pair_filter_member_right x t a b hxt hta htb)))
  have hs : Context Γ (subsetCode c x t) := .mp hg (.closed (pair_filter_subset x t a b))
  have hn : Context Γ (nonemptyCode c s) := .mp hca (.closed (nonempty_from_member c s a hsc hsa))
  have hex : Context Γ (existsCode m (leastMemberCode c m r)) :=
    .mp hn (.mp hs (.mp hl (.closed (least_subsets_instance x u t s m r c
      hux huc hut hus hum hur hct hcs hcm hcr))))
  have he : Context Γ (allCode m E) := .mp hg (.closed hge)
  exact .mp hex (.mp he (.mp hcb (.mp hca (.closed (compare_exists_least c m r a b hcmp)))))

theorem compare_from_pair_graph_certificate (x t a b u s m r : Nat)
    (fresh : [x,t,a,b,u,s,m,r,pairWitness x t a b].Nodup) :
    theoremCode (certificate (compare_from_pair_graph x t a b u s m r fresh)) =
      imp (pairGraph x t a b) (imp (leastSubsetsCode x u t s m r)
        (imp (member x a) (imp (member x b)
          (either (equal a b) (either (member b a) (member a b)))))) :=
  certificate_correct (compare_from_pair_graph x t a b u s m r fresh)

end PASoundness.PAtoCompactPairGraphCompare

#print axioms PASoundness.PAtoCompactPairGraphCompare.compare_from_pair_graph
#print axioms PASoundness.PAtoCompactPairGraphCompare.compare_from_pair_graph_certificate
