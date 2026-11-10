import PASoundness.PAtoCompactLocalPairFresh
import PASoundness.PAtoCompactLocalCompare
import PASoundness.PAtoCompactTransitiveClosure

/-! Explicit fresh-name choice for local K comparability. Colliding input
names are handled by reflexivity or by deriving literal code 1 from
self-membership. No quotient, global comparison, or induction is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLocalCompareChosen
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactPairFilter PASoundness.PAtoCompactLocalPairFresh
open PASoundness.PAtoCompactLocalCompare PASoundness.PAtoCompactTransitiveClosure

def chosenLeast (x a b : Nat) : Nat :=
  let t := testName x a b
  let c := pairWitness x t a b
  leastSubsetsCode x (c+1) t (c+2) (c+3) (c+4)

/-- The existential pair witness and all auxiliary bound names are chosen
explicitly from x,a,b; no syntactic distinctness of those inputs is needed. -/
def local_comparable_chosen (x a b : Nat) :
    KDerivation (imp (chosenLeast x a b) (imp (member x a) (imp (member x b)
      (either (equal a b) (either (member b a) (member a b)))))) := by
  by_cases hab : a = b
  · subst b
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    exact Context.disjunctionLeft (.closed (equalityReflexive a))
  by_cases hxa : x = a
  · subst a
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [member x b, member x x, chosenLeast x x b]
    have hm : Context Γ (member x x) := .hypothesis (by simp [Γ])
    have hfalse : Context Γ 1 := .mp hm (.closed (self_membership_implies_code_one x))
    exact Context.explode _ hfalse
  by_cases hxb : x = b
  · subst b
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [member x x, member x a, chosenLeast x a x]
    have hm : Context Γ (member x x) := .hypothesis (by simp [Γ])
    have hfalse : Context Γ 1 := .mp hm (.closed (self_membership_implies_code_one x))
    exact Context.explode _ hfalse
  have hnames : [x,a,b].Nodup := by simp [hxa,hxb,hab]
  let t := testName x a b
  let c := pairWitness x t a b
  have hfresh : [x,t,a,b,c+1,c+2,c+3,c+4,c].Nodup := pair_fresh_allocation x a b hnames
  exact local_comparable x t a b (c+1) (c+2) (c+3) (c+4) hfresh

theorem local_comparable_chosen_certificate (x a b : Nat) :
    theoremCode (certificate (local_comparable_chosen x a b)) =
      imp (chosenLeast x a b) (imp (member x a) (imp (member x b)
        (either (equal a b) (either (member b a) (member a b))))) :=
  certificate_correct (local_comparable_chosen x a b)

end PASoundness.PAtoCompactLocalCompareChosen

#print axioms PASoundness.PAtoCompactLocalCompareChosen.local_comparable_chosen
#print axioms PASoundness.PAtoCompactLocalCompareChosen.local_comparable_chosen_certificate
