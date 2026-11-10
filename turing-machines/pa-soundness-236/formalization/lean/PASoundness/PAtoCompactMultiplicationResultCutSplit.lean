import PASoundness.PAtoCompactFilterInstantiation

/-! A pointwise K split for the literal anchored addition suffix used in
multiplication. Every member of the new result is either a member of the old
result or a member of the supplied filtered suffix. This is only a filter
consequence; no graph, bijectivity, product or PA soundness is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationResultCutSplit
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactFilterInstantiation
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The suffix is result 45 filtered outside the old result 32. -/
def suffixFilter : Nat := filterGraph 45 40 35 (neg (member 32 35))

/-- Every new-result member lies in the old result or the suffix. The only
freshness restriction concerns the filter's bound test name. -/
def result_member_split (v : Nat) (h : 35 ≠ v) : KDerivation
    (imp suffixFilter (imp (member 45 v) (either (member 32 v) (member 40 v)))) := by
  let P : Formula := (Formula.member 32 35).not
  have hf := filter_at 45 40 35 v P (by decide) (by decide) h
    (by simp [P,Formula.not,Formula.binders]) (by simp [P,Formula.not,Formula.binders])
  have hi : KDerivation (imp suffixFilter
      (both (imp (member 40 v) (both (member 45 v) (neg (member 32 v))))
        (imp (both (member 45 v) (neg (member 32 v))) (member 40 v)))) := by
    simpa [suffixFilter,P,Formula.not,Formula.encode,replace,rename,neg,h] using hf
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 45 v,suffixFilter]
  have hm : Context Γ (member 45 v) := .head _ _
  have hs : Context Γ suffixFilter := .hypothesis (by simp [Γ])
  have hex : Context Γ (either (member 32 v) (neg (member 32 v))) :=
    .closed (CompactHilbertBasis.identity (neg (member 32 v)))
  apply Context.disjunctionElim hex
  · exact Context.disjunctionLeft (Context.head Γ (member 32 v))
  · let Δ := neg (member 32 v) :: Γ
    have hn : Context Δ (neg (member 32 v)) := .head _ _
    have hr : Context Δ (member 40 v) :=
      .mp (Context.conjunctionIntro (.under hm _) hn)
        (.under (Context.conjunctionRight (.mp hs (.closed hi))) _)
    exact Context.disjunctionRight hr

/-- An element cannot simultaneously belong to the old result and its
filtered suffix, where negation means implication to literal compact code 1. -/
def old_suffix_disjoint (v : Nat) (h : 35 ≠ v) : KDerivation
    (imp suffixFilter (imp (member 40 v) (neg (member 32 v)))) := by
  let P : Formula := (Formula.member 32 35).not
  have hf := filter_at 45 40 35 v P (by decide) (by decide) h
    (by simp [P,Formula.not,Formula.binders]) (by simp [P,Formula.not,Formula.binders])
  have hi : KDerivation (imp suffixFilter
      (both (imp (member 40 v) (both (member 45 v) (neg (member 32 v))))
        (imp (both (member 45 v) (neg (member 32 v))) (member 40 v)))) := by
    simpa [suffixFilter,P,Formula.not,Formula.encode,replace,rename,neg,h] using hf
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 40 v,suffixFilter]
  have hm : Context Γ (member 40 v) := .head _ _
  have hs : Context Γ suffixFilter := .hypothesis (by simp [Γ])
  exact Context.conjunctionRight (.mp hm (Context.conjunctionLeft (.mp hs (.closed hi))))

theorem result_member_split_certificate (v : Nat) (h : 35 ≠ v) :
    theoremCode (certificate (result_member_split v h)) =
      imp suffixFilter (imp (member 45 v) (either (member 32 v) (member 40 v))) :=
  certificate_correct (result_member_split v h)

theorem old_suffix_disjoint_certificate (v : Nat) (h : 35 ≠ v) :
    theoremCode (certificate (old_suffix_disjoint v h)) =
      imp suffixFilter (imp (member 40 v) (neg (member 32 v))) :=
  certificate_correct (old_suffix_disjoint v h)
end PASoundness.PAtoCompactMultiplicationResultCutSplit
#print axioms PASoundness.PAtoCompactMultiplicationResultCutSplit.result_member_split
#print axioms PASoundness.PAtoCompactMultiplicationResultCutSplit.old_suffix_disjoint
#print axioms PASoundness.PAtoCompactMultiplicationResultCutSplit.result_member_split_certificate
#print axioms PASoundness.PAtoCompactMultiplicationResultCutSplit.old_suffix_disjoint_certificate
