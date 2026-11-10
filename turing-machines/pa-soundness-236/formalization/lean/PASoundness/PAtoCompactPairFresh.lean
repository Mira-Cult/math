import PASoundness.PAtoCompactPairSelector
import PASoundness.PAtoCompactSingletonSelector

/-! Explicit labels for combining a singleton witness and the distinct-name
unordered-pair construction. This is only numerical syntax hygiene. -/
namespace PASoundness.PAtoCompactPairFresh
open PASoundness.PAtoCompactPairSelector PASoundness.PAtoCompactSingletonSelector

def point (a b : Nat) : Nat := max a b + 1
def pairWitness (a b : Nat) : Nat := pairPredicate a b (point a b)
def singletonWitness (a b : Nat) : Nat := singletonPredicate a (point a b)
def singleTest (a b : Nat) : Nat := pairWitness a b + singletonWitness a b + 1
def pairTest (a b : Nat) : Nat := singleTest a b + 1
def singletonName (a b : Nat) : Nat := pairTest a b + 1
def pairName (a b : Nat) : Nat := singletonName a b + 1

/-- Freshness of both selector labels and all pair construction names; a=b as
numeric names is handled by the separate repeated-name construction. -/
theorem construction_fresh (a b : Nat) (hab : a ≠ b) :
    let t := point a b
    let c := pairWitness a b
    let c' := singletonWitness a b
    let q := singleTest a b
    let r := pairTest a b
    let s := singletonName a b
    let d := pairName a b
    [c,s,a,b,t,q,r,d].Nodup ∧ q ≠ c' ∧ s ≠ c' := by
  dsimp only
  have hc := PAtoCompactPairSelector.predicate_names_lt a b (point a b)
  have hc' := PAtoCompactSingletonSelector.predicate_names_lt a (point a b)
  have ha : a < point a b := by unfold point; omega
  have hb : b < point a b := by unfold point; omega
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    not_false_eq_true, List.nodup_nil, and_true]
  simp only [pairName, singletonName, pairTest, singleTest, pairWitness, singletonWitness]
  repeat' apply And.intro
  all_goals omega

end PASoundness.PAtoCompactPairFresh
