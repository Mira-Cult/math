import PASoundness.PAtoCompactAdditionEmptySuffix
import PASoundness.PAtoCompactTransitiveClosure
import PASoundness.CompactQuantifiers
import PASoundness.PAtoCompactEmptyExtrema

/-! If the represented suffix is zero, every member of the result lies in
its cut; the cut-alternative in the proposed addition matrix then forces
equality of cut and result. These are literal K derivations under the given
zero, filter, and cut-alternative premises, not a quotient axiom or addition
functionality. Compact negation is implication to code 1. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionZeroSuffixContained
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactFilterInstantiation PASoundness.PAtoCompactAdditionEmptySuffix
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactEmptyExtrema
attribute [local irreducible] imp Cantor.pair Cantor.triangle

private def P : Formula := (Formula.member 33 35).not
private def F : Nat := filterGraph 32 34 35 (neg (member 33 35))
private def Z : Nat := zeroCode 34 36
private def C : Formula := .imp (.member 32 37) (.member 33 37)

/-- Under a zero suffix, result membership implies cut membership. -/
def zero_suffix_contained : KDerivation (imp Z (imp F (allCode 37 C.encode))) := by
  have hi := filter_at 32 34 35 37 P (by decide) (by decide) (by decide)
    (by decide) (by decide)
  have hi' : KDerivation (imp F
      (both (imp (member 34 37) (both (member 32 37) (neg (member 33 37))))
        (imp (both (member 32 37) (neg (member 33 37))) (member 34 37)))) := by
    simpa [F,P,Formula.not,Formula.encode,replace,rename,neg] using hi
  have hz : KDerivation (imp Z (neg (member 34 37))) := by
    have h := universalInstance 36 37 ((Formula.member 34 36).not)
      (by decide) (by decide) (by decide)
    simpa [Z,zeroCode,Formula.not,Formula.encode,replace,rename,neg] using h
  let Γ := [F,Z]
  have hf : Context Γ F := .head _ _
  have hzero : Context Γ Z := .hypothesis (by simp [Γ])
  have hc : Context Γ C.encode := by
    change Context Γ (imp (member 32 37) (member 33 37))
    apply Context.deduction
    apply Context.dne
    apply Context.deduction
    let Δ := [neg (member 33 37),member 32 37,F,Z]
    have hnot : Context Δ (neg (member 33 37)) := .head _ _
    have hmem : Context Δ (member 32 37) := .hypothesis (by simp [Δ])
    have hs : Context Δ (member 34 37) := by
      have hfilter : Context Δ
          (both (imp (member 34 37) (both (member 32 37) (neg (member 33 37))))
            (imp (both (member 32 37) (neg (member 33 37))) (member 34 37))) :=
        .mp (.hypothesis (by simp [Δ])) (.closed hi')
      exact .mp (Context.conjunctionIntro hmem hnot) (Context.conjunctionRight hfilter)
    have hn : Context Δ (neg (member 34 37)) := .mp (Context.under (Context.under hzero _) _) (.closed hz)
    exact .mp hs hn
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 37 h)) := by
    intro h hh
    by_cases hf' : h = F
    · subst h
      exact suffix_graph_vacuity 32 33 34 35 37 (by decide)
    · have hz' : h = Z := by simpa [Γ,hf'] using hh
      subst h
      exact zero_vacuity 34 36 37 (by decide) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact Context.generalize 37 hv hc

/-- A zero suffix rules out a proper-member cut, so the displayed cut
alternative entails literal equality of the cut and the result. -/
def zero_suffix_cut_equal : KDerivation (imp Z (imp F
    (imp (either (equal 33 32) (member 32 33)) (equal 33 32)))) := by
  have hpoint : KDerivation (imp (allCode 37 C.encode)
      (imp (member 32 33) (member 33 33))) := by
    have h := universalInstance 37 33 C (by decide) (by decide) (by decide)
    simpa [C,Formula.encode,replace,rename] using h
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [either (equal 33 32) (member 32 33),F,Z]
  have ha : Context Γ (either (equal 33 32) (member 32 33)) := .head _ _
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  have hc : Context Γ (imp (member 32 33) (member 33 33)) :=
    .mp (.mp hf (.mp hz (.closed zero_suffix_contained))) (.closed hpoint)
  apply Context.disjunctionElim ha
  · exact .head _ _
  · have hm : Context (member 32 33 :: Γ) (member 32 33) := .head _ _
    have hself : Context (member 32 33 :: Γ) (member 33 33) := .mp hm (.under hc _)
    exact Context.explode _ (.mp hself (.closed (self_membership_implies_code_one 33)))

theorem zero_suffix_contained_certificate : theoremCode (certificate zero_suffix_contained) =
    imp Z (imp F (allCode 37 C.encode)) := certificate_correct zero_suffix_contained

theorem zero_suffix_cut_equal_certificate : theoremCode (certificate zero_suffix_cut_equal) =
    imp Z (imp F (imp (either (equal 33 32) (member 32 33)) (equal 33 32))) :=
  certificate_correct zero_suffix_cut_equal
end PASoundness.PAtoCompactAdditionZeroSuffixContained

#print axioms PASoundness.PAtoCompactAdditionZeroSuffixContained.zero_suffix_contained
#print axioms PASoundness.PAtoCompactAdditionZeroSuffixContained.zero_suffix_contained_certificate
#print axioms PASoundness.PAtoCompactAdditionZeroSuffixContained.zero_suffix_cut_equal
#print axioms PASoundness.PAtoCompactAdditionZeroSuffixContained.zero_suffix_cut_equal_certificate
