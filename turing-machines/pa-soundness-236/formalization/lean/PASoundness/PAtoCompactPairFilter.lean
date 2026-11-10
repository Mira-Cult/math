import PASoundness.PAtoCompactFilteredSubset
import PASoundness.PAtoCompactLeastCounterexample

/-! A represented two-element selection obtained by K filtering. The graph
is the intersection of x with {a,b}. The existence theorem is the existing
selector-8 filtering derivation specialized to the equality disjunction.
Compact negation/disjunction use literal code 1, i.e. `member 0 0`; ordinary
logical readings are established separately in standard semantics. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPairFilter
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactLeastCounterexample

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def pairPredicate (t a b : Nat) : Nat := either (equal t a) (equal t b)
def pairWitness (x t a b : Nat) : Nat := filterPredicate x t (pairPredicate t a b)
def pairGraph (x t a b : Nat) : Nat := filterGraph x (pairWitness x t a b) t (pairPredicate t a b)

def namedPairBody (x t a b : Nat) : CompactNamed.Formula :=
  let c := pairWitness x t a b
  let p := namedEither (.equal t a) (.equal t b)
  let q := namedBoth (.member x t) p
  namedBoth (.imp (.member c t) q) (.imp q (.member c t))

/-- Selector 8 constructs the exact x-filtered pair graph. -/
def pair_filter_exists (x t a b : Nat) (hxt : x ≠ t) :
    KDerivation (existsCode (pairWitness x t a b) (pairGraph x t a b)) :=
  filtered_subset_exists x t (pairPredicate t a b) hxt

theorem pair_filter_exists_certificate (x t a b : Nat) (hxt : x ≠ t) :
    theoremCode (certificate (pair_filter_exists x t a b hxt)) =
      existsCode (pairWitness x t a b) (pairGraph x t a b) :=
  certificate_correct (pair_filter_exists x t a b hxt)

/-- Instantiate the exact filter at v, with no hypothesis yet that either
selected element belongs to x. -/
def pair_filter_at (x t a b v : Nat) (hxt : x ≠ t) (hta : t ≠ a)
    (htb : t ≠ b) (htv : t ≠ v) :
    KDerivation (imp (pairGraph x t a b)
      (both (imp (member (pairWitness x t a b) v)
              (both (member x v) (either (equal v a) (equal v b))))
        (imp (both (member x v) (either (equal v a) (equal v b)))
              (member (pairWitness x t a b) v)))) := by
  let c := pairWitness x t a b
  have hc := filterPredicate_bounds x t (pairPredicate t a b)
  have htc : t ≠ c := by dsimp [c, pairWitness]; omega
  have hct' : imp (imp (member x t) (imp (imp (imp (equal t a) 1) (equal t b)) 1)) 1 ≠ t := by
    change c ≠ t
    exact Ne.symm htc
  let body := namedPairBody x t a b
  have hu := CompactNamed.universalInstance t v body htv
    (by simp [body, namedPairBody, namedBoth, namedEither, CompactNamed.Formula.binders])
    (by simp [body, namedPairBody, namedBoth, namedEither, CompactNamed.Formula.binders])
  simpa [body, namedPairBody, namedBoth, namedEither, CompactNamed.Formula.encode,
    CompactNamed.replace, CompactNamed.rename, pairGraph, pairWitness, pairPredicate,
    filterGraph, filterPredicate, CompactProof.both, CompactProof.neg, CompactDerivations.either,
    hxt, htc, hct', hta, htb, htv, Ne.symm hxt, Ne.symm htc, Ne.symm hta,
    Ne.symm htb, Ne.symm htv] using hu

/-- Under the filter graph, a selected x-member a belongs to the pair. -/
def pair_filter_member_left (x t a b : Nat) (hxt : x ≠ t) (hta : t ≠ a)
    (htb : t ≠ b) :
    KDerivation (imp (pairGraph x t a b)
      (imp (member x a) (member (pairWitness x t a b) a))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member x a, pairGraph x t a b]
  have hx : Context Γ (member x a) := Context.head _ _
  have hg : Context Γ (pairGraph x t a b) := .hypothesis (by simp [Γ])
  have hp : Context Γ (either (equal a a) (equal a b)) :=
    Context.disjunctionLeft (.closed (equalityReflexive a))
  have he := Context.conjunctionIntro hx hp
  have hgraph := Context.mp hg (.closed (pair_filter_at x t a b a hxt hta htb hta))
  exact .mp he (Context.conjunctionRight hgraph)

/-- Under the filter graph, a selected x-member b belongs to the pair. -/
def pair_filter_member_right (x t a b : Nat) (hxt : x ≠ t) (hta : t ≠ a)
    (htb : t ≠ b) :
    KDerivation (imp (pairGraph x t a b)
      (imp (member x b) (member (pairWitness x t a b) b))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member x b, pairGraph x t a b]
  have hx : Context Γ (member x b) := Context.head _ _
  have hg : Context Γ (pairGraph x t a b) := .hypothesis (by simp [Γ])
  have hp : Context Γ (either (equal b a) (equal b b)) :=
    Context.disjunctionRight (.closed (equalityReflexive b))
  have he := Context.conjunctionIntro hx hp
  have hgraph := Context.mp hg (.closed (pair_filter_at x t a b b hxt hta htb htb))
  exact .mp he (Context.conjunctionRight hgraph)

/-- Every selected member is one of the two selected names. -/
def pair_filter_member_cases (x t a b v : Nat) (hxt : x ≠ t) (hta : t ≠ a)
    (htb : t ≠ b) (htv : t ≠ v) :
    KDerivation (imp (pairGraph x t a b)
      (imp (member (pairWitness x t a b) v) (either (equal v a) (equal v b)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member (pairWitness x t a b) v, pairGraph x t a b]
  have hm : Context Γ (member (pairWitness x t a b) v) := Context.head _ _
  have hg : Context Γ (pairGraph x t a b) := .hypothesis (by simp [Γ])
  have hgraph := Context.mp hg (.closed (pair_filter_at x t a b v hxt hta htb htv))
  exact Context.conjunctionRight (.mp hm (Context.conjunctionLeft hgraph))

/-- The selected graph is a subset of x. -/
def pair_filter_subset (x t a b : Nat) :
    KDerivation (imp (pairGraph x t a b)
      (PAtoCompactPredecessor.subsetCode (pairWitness x t a b) x t)) :=
  filter_graph_subset x (pairWitness x t a b) t (pairPredicate t a b)

end PASoundness.PAtoCompactPairFilter

#print axioms PASoundness.PAtoCompactPairFilter.pair_filter_exists
#print axioms PASoundness.PAtoCompactPairFilter.pair_filter_at
#print axioms PASoundness.PAtoCompactPairFilter.pair_filter_member_left
#print axioms PASoundness.PAtoCompactPairFilter.pair_filter_member_right
#print axioms PASoundness.PAtoCompactPairFilter.pair_filter_member_cases
#print axioms PASoundness.PAtoCompactPairFilter.pair_filter_subset
