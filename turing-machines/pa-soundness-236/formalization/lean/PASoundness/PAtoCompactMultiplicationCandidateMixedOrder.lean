import PASoundness.PAtoCompactMultiplicationMixedOutputOrder
import PASoundness.PAtoCompactMultiplicationLocalCandidateOrder

/-! Candidate-guarded old/new output order for a fixed-cut product extension.
This is a local finite-K point comparison, not a row graph, full lex matrix,
multiplication totality, or PA proof transport. -/
namespace PASoundness.PAtoCompactMultiplicationCandidateMixedOrder
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFilteredSubset
open PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactMultiplicationMixedOutputOrder
open PASoundness.PAtoCompactMultiplicationLocalCandidateOrder
set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Under candidate guards for whole result 45 and cut 32, with the cut
alternative, suffix filter, and displayed old/new memberships, the old point
belongs to the new point and the reverse membership implies literal code 1. -/
def candidate_old_before_new : KDerivation
    (imp (domainAt 100 45).encode
      (imp (domainAt 100 32).encode
        (imp (either (equal 32 45) (member 45 32))
          (imp (filterGraph 45 40 35 (neg (member 32 35)))
            (imp (member 32 5) (imp (member 40 9)
              (both (member 9 5) (neg (member 5 9))))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 40 9,member 32 5,filterGraph 45 40 35 (neg (member 32 35)),
    either (equal 32 45) (member 45 32), (domainAt 100 32).encode,(domainAt 100 45).encode]
  have hs : Context Γ (member 40 9) := .hypothesis (by simp [Γ])
  have ho : Context Γ (member 32 5) := .hypothesis (by simp [Γ])
  have hf : Context Γ (filterGraph 45 40 35 (neg (member 32 35))) := .hypothesis (by simp [Γ])
  have ha : Context Γ (either (equal 32 45) (member 45 32)) := .hypothesis (by simp [Γ])
  have hd : Context Γ (domainAt 100 32).encode := .hypothesis (by simp [Γ])
  have hw : Context Γ (domainAt 100 45).encode := .hypothesis (by simp [Γ])
  have hsf := Context.mp hs (Context.mp hf (.closed suffix_facts))
  have hn : Context Γ (neg (member 32 9)) := Context.conjunctionRight hsf
  have hw9 : Context Γ (member 45 9) := Context.conjunctionLeft hsf
  have hc : Context Γ (member 45 32) := .mp hn (.mp hw9 (.mp ha (.closed proper_cut)))
  have hw5 : Context Γ (member 45 5) := .mp ho (.mp hc
    (.mp (.mp hw (.closed result_transitive)) (.closed
      (transitive_chain 45 54 55 32 5 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)))))
  have hr : Context Γ (neg (member 5 9)) := by
    apply Context.deduction
    let Δ := member 5 9 :: Γ
    have hm : Context Δ (member 5 9) := .head _ _
    have hnew : Context Δ (member 32 9) := .mp hm (.mp (.under ho _)
      (.mp (.mp (.under hd _) (.closed cut_transitive)) (.closed
        (transitive_chain 32 54 55 5 9 (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)))))
    exact .mp hnew (.under hn _)
  have hcmp : Context Γ (either (equal 5 9) (either (member 9 5) (member 5 9))) :=
    .mp hw9 (.mp hw5 (.mp hw (.closed candidate_comparable)))
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

theorem candidate_old_before_new_certificate : theoremCode (certificate candidate_old_before_new) =
    imp (domainAt 100 45).encode (imp (domainAt 100 32).encode
      (imp (either (equal 32 45) (member 45 32))
        (imp (filterGraph 45 40 35 (neg (member 32 35)))
          (imp (member 32 5) (imp (member 40 9)
            (both (member 9 5) (neg (member 5 9)))))))) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationCandidateMixedOrder
#print axioms PASoundness.PAtoCompactMultiplicationCandidateMixedOrder.candidate_old_before_new
#print axioms PASoundness.PAtoCompactMultiplicationCandidateMixedOrder.candidate_old_before_new_certificate
