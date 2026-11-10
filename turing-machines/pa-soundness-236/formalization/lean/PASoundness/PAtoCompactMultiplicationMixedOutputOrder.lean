import PASoundness.PAtoCompactFilterInstantiation
import PASoundness.PAtoCompactTransitiveClosure
import PASoundness.PAtoCompactLocalCompareChosen

/-! A local finite-K comparison needed when extending a lexicographic product
by a new row. The old output lies in a transitive cut; the new output lies in
the explicitly filtered suffix of a transitive whole result. Local least-set
comparability is required only within that whole result. No transitivity of
the suffix, global ordinal comparison, row collection, multiplication
totality, or semantic soundness is assumed. Compact negation is literal
implication to code 1. -/
namespace PASoundness.PAtoCompactMultiplicationMixedOutputOrder
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactLocalCompareChosen
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Suffix membership yields both whole-result membership and literal
nonmembership in the cut. -/
def suffix_facts : KDerivation
    (imp (filterGraph 45 40 35 (neg (member 32 35)))
      (imp (member 40 9) (both (member 45 9) (neg (member 32 9))))) := by
  let P : Formula := (Formula.member 32 35).not
  have hi := filter_at 45 40 35 9 P (by decide) (by decide) (by decide) (by decide) (by decide)
  have hi' : KDerivation (imp (filterGraph 45 40 35 (neg (member 32 35)))
      (both (imp (member 40 9) (both (member 45 9) (neg (member 32 9))))
        (imp (both (member 45 9) (neg (member 32 9))) (member 40 9)))) := by
    simpa [P, Formula.not, Formula.encode, replace, rename, neg] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 40 9, filterGraph 45 40 35 (neg (member 32 35))]
  have hm : Context Γ (member 40 9) := .head _ _
  have hf : Context Γ (filterGraph 45 40 35 (neg (member 32 35))) := .hypothesis (by simp [Γ])
  exact .mp hm (Context.conjunctionLeft (.mp hf (.closed hi')))

/-- If a cut is equal to, or a member of, the result, then a witnessed
outside-cut result member forces the membership alternative. -/
def proper_cut : KDerivation
    (imp (either (equal 32 45) (member 45 32))
      (imp (member 45 9) (imp (neg (member 32 9)) (member 45 32)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [neg (member 32 9),member 45 9,either (equal 32 45) (member 45 32)]
  have hn : Context Γ (neg (member 32 9)) := .head _ _
  have hm : Context Γ (member 45 9) := .hypothesis (by simp [Γ])
  have ha : Context Γ (either (equal 32 45) (member 45 32)) := .hypothesis (by simp [Γ])
  apply Context.disjunctionElim ha
  · let Δ := equal 32 45 :: Γ
    have he : Context Δ (equal 32 45) := .head _ _
    have hc : Context Δ (member 32 9) :=
      .mp (.under hm _) (.mp (Context.eqSymm he) (.closed (memberLeftEquality 45 32 9)))
    exact Context.explode _ (.mp hc (.under hn _))
  · exact Context.head _ _

/-- The new suffix point cannot lie inside any old cut point. -/
def reverse_impossible : KDerivation
    (imp (transitiveCode 32 41 42)
      (imp (member 32 5) (imp (neg (member 32 9)) (neg (member 5 9))))) := by
  apply Context.closeEmpty
  repeat apply Context.deduction
  let Γ := [member 5 9,neg (member 32 9),member 32 5,transitiveCode 32 41 42]
  have hb : Context Γ (member 5 9) := .head _ _
  have hn : Context Γ (neg (member 32 9)) := .hypothesis (by simp [Γ])
  have ha : Context Γ (member 32 5) := .hypothesis (by simp [Γ])
  have ht : Context Γ (transitiveCode 32 41 42) := .hypothesis (by simp [Γ])
  have hc : Context Γ (member 32 9) :=
    .mp hb (.mp ha (.mp ht (.closed (transitive_chain 32 41 42 5 9
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))))
  exact .mp hc hn

/-- In the old/new mixed case the old output belongs to the new output,
and the reverse membership implies literal K bottom. The least-subsets
premise is the explicit chosen local-comparability instance. -/
def old_before_new : KDerivation
    (imp (chosenLeast 45 5 9)
      (imp (transitiveCode 45 41 42)
        (imp (transitiveCode 32 41 42)
          (imp (either (equal 32 45) (member 45 32))
            (imp (filterGraph 45 40 35 (neg (member 32 35)))
              (imp (member 32 5) (imp (member 40 9)
                (both (member 9 5) (neg (member 5 9)))))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 40 9,member 32 5,filterGraph 45 40 35 (neg (member 32 35)),
    either (equal 32 45) (member 45 32),transitiveCode 32 41 42,
    transitiveCode 45 41 42,chosenLeast 45 5 9]
  have hs : Context Γ (member 40 9) := .hypothesis (by simp [Γ])
  have ho : Context Γ (member 32 5) := .hypothesis (by simp [Γ])
  have hf : Context Γ (filterGraph 45 40 35 (neg (member 32 35))) := .hypothesis (by simp [Γ])
  have ha : Context Γ (either (equal 32 45) (member 45 32)) := .hypothesis (by simp [Γ])
  have ht : Context Γ (transitiveCode 32 41 42) := .hypothesis (by simp [Γ])
  have hw : Context Γ (transitiveCode 45 41 42) := .hypothesis (by simp [Γ])
  have hl : Context Γ (chosenLeast 45 5 9) := .hypothesis (by simp [Γ])
  have hsf := Context.mp hs (Context.mp hf (.closed suffix_facts))
  have hn : Context Γ (neg (member 32 9)) := Context.conjunctionRight hsf
  have hw9 : Context Γ (member 45 9) := Context.conjunctionLeft hsf
  have hc : Context Γ (member 45 32) := .mp hn (.mp hw9 (.mp ha (.closed proper_cut)))
  have hw5 : Context Γ (member 45 5) := .mp ho (.mp hc (.mp hw (.closed
    (transitive_chain 45 41 42 32 5 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)))))
  have hr : Context Γ (neg (member 5 9)) := .mp hn (.mp ho (.mp ht (.closed reverse_impossible)))
  have hcmp : Context Γ (either (equal 5 9) (either (member 9 5) (member 5 9))) :=
    .mp hw9 (.mp hw5 (.mp hl (.closed (local_comparable_chosen 45 5 9))))
  have hfwd : Context Γ (member 9 5) := by
    apply Context.disjunctionElim hcmp
    · let Δ := equal 5 9 :: Γ
      have he : Context Δ (equal 5 9) := .head _ _
      have hc' : Context Δ (member 32 9) := .mp he (.mp (.under ho _)
        (.closed (memberRightEquality 32 5 9)))
      exact Context.explode _ (.mp hc' (.under hn _))
    · let Δ := either (member 9 5) (member 5 9) :: Γ
      have hc' : Context Δ (either (member 9 5) (member 5 9)) := .head _ _
      apply Context.disjunctionElim hc'
      · exact Context.head _ _
      · let Θ := member 5 9 :: Δ
        have hb : Context Θ (member 5 9) := .head _ _
        exact Context.explode _ (.mp hb (.under (.under hr _) _))
  exact Context.conjunctionIntro hfwd hr

theorem old_before_new_certificate : theoremCode (certificate old_before_new) =
    imp (chosenLeast 45 5 9)
      (imp (transitiveCode 45 41 42)
        (imp (transitiveCode 32 41 42)
          (imp (either (equal 32 45) (member 45 32))
            (imp (filterGraph 45 40 35 (neg (member 32 35)))
              (imp (member 32 5) (imp (member 40 9)
                (both (member 9 5) (neg (member 5 9))))))))) :=
  certificate_correct old_before_new
end PASoundness.PAtoCompactMultiplicationMixedOutputOrder
#print axioms PASoundness.PAtoCompactMultiplicationMixedOutputOrder.old_before_new
#print axioms PASoundness.PAtoCompactMultiplicationMixedOutputOrder.old_before_new_certificate
