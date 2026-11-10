import PASoundness.PAtoCompactLocalCompareChosen
import PASoundness.PAtoCompactTransitiveClosure

/-! Mixed prefix/suffix order for a split candidate-like whole, at arbitrary
operand labels. All order assumptions are object-level K antecedents. Only
whole and cut transitivity are used; the relative complement need not be
transitive or a candidate. This constructs no isomorphism or graph. -/
namespace PASoundness.PAtoCompactAdditionGenericMixedOrder

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactLocalCompareChosen

set_option maxRecDepth 65536
set_option maxHeartbeats 0
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Fresh test names used by the two explicit transitivity hypotheses. -/
def firstTest (whole cut old new : Nat) : Nat := max whole (max cut (max old new)) + 1

def secondTest (whole cut old new : Nat) : Nat := firstTest whole cut old new + 1

/-- A prefix point precedes a point of the whole outside the cut. The cut may
be equal to or a member of the whole; existence of an outside-cut point rules
out the equality branch. The operand names may alias. -/
def prefix_before_outside (whole cut old new : Nat) :
    let p := firstTest whole cut old new
    let q := secondTest whole cut old new
    KDerivation (imp (chosenLeast whole old new)
      (imp (transitiveCode whole p q)
        (imp (transitiveCode cut p q)
          (imp (either (equal cut whole) (member whole cut))
            (imp (member cut old) (imp (member whole new)
              (imp (neg (member cut new))
                (both (member new old) (neg (member old new)))))))))) := by
  dsimp only
  let p := firstTest whole cut old new
  let q := secondTest whole cut old new
  have hpwhole : p ≠ whole := by dsimp [p, firstTest]; omega
  have hpcut : p ≠ cut := by dsimp [p, firstTest]; omega
  have hpold : p ≠ old := by dsimp [p, firstTest]; omega
  have hpq : p ≠ q := by dsimp [q, secondTest]; omega
  have hqwhole : q ≠ whole := by dsimp [q, secondTest, p, firstTest]; omega
  have hqcut : q ≠ cut := by dsimp [q, secondTest, p, firstTest]; omega
  have hqold : q ≠ old := by dsimp [q, secondTest, p, firstTest]; omega
  have hqnew : q ≠ new := by dsimp [q, secondTest, p, firstTest]; omega
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [neg (member cut new), member whole new, member cut old,
    either (equal cut whole) (member whole cut), transitiveCode cut p q,
    transitiveCode whole p q, chosenLeast whole old new]
  have hn : Context Γ (neg (member cut new)) := .head _ _
  have hwnew : Context Γ (member whole new) := .hypothesis (by simp [Γ])
  have hcold : Context Γ (member cut old) := .hypothesis (by simp [Γ])
  have hcut : Context Γ (either (equal cut whole) (member whole cut)) := .hypothesis (by simp [Γ])
  have htc : Context Γ (transitiveCode cut p q) := .hypothesis (by simp [Γ])
  have htw : Context Γ (transitiveCode whole p q) := .hypothesis (by simp [Γ])
  have hl : Context Γ (chosenLeast whole old new) := .hypothesis (by simp [Γ])
  have hproper : Context Γ (member whole cut) := by
    apply Context.disjunctionElim hcut
    · let Δ := equal cut whole :: Γ
      have he : Context Δ (equal cut whole) := .head _ _
      have hm : Context Δ (member cut new) :=
        .mp (.under hwnew _) (.mp (Context.eqSymm he) (.closed (memberLeftEquality whole cut new)))
      exact Context.explode _ (.mp hm (.under hn _))
    · exact .head _ _
  have hwold : Context Γ (member whole old) :=
    .mp hcold (.mp hproper (.mp htw (.closed
      (transitive_chain whole p q cut old hpwhole hpcut hpq hqwhole hqcut hqold))))
  have hreverse : Context Γ (neg (member old new)) := by
    apply Context.deduction
    let Δ := member old new :: Γ
    have hm : Context Δ (member old new) := .head _ _
    have hbad : Context Δ (member cut new) :=
      .mp hm (.mp (.under hcold _) (.mp (.under htc _) (.closed
        (transitive_chain cut p q old new hpcut hpold hpq hqcut hqold hqnew))))
    exact .mp hbad (.under hn _)
  have hcmp : Context Γ (either (equal old new)
      (either (member new old) (member old new))) :=
    .mp hwnew (.mp hwold (.mp hl (.closed (local_comparable_chosen whole old new))))
  have hforward : Context Γ (member new old) := by
    apply Context.disjunctionElim hcmp
    · let Δ := equal old new :: Γ
      have he : Context Δ (equal old new) := .head _ _
      have hbad : Context Δ (member cut new) :=
        .mp he (.mp (.under hcold _) (.closed (memberRightEquality cut old new)))
      exact Context.explode _ (.mp hbad (.under hn _))
    · let Δ := either (member new old) (member old new) :: Γ
      have hc : Context Δ (either (member new old) (member old new)) := .head _ _
      apply Context.disjunctionElim hc
      · exact .head _ _
      · let Θ := member old new :: Δ
        have hm : Context Θ (member old new) := .head _ _
        exact Context.explode _ (.mp hm (.under (.under hreverse _) _))
  exact Context.conjunctionIntro hforward hreverse

theorem prefix_before_outside_certificate (whole cut old new : Nat) :
    let p := firstTest whole cut old new
    let q := secondTest whole cut old new
    theoremCode (certificate (prefix_before_outside whole cut old new)) =
      imp (chosenLeast whole old new)
        (imp (transitiveCode whole p q)
          (imp (transitiveCode cut p q)
            (imp (either (equal cut whole) (member whole cut))
              (imp (member cut old) (imp (member whole new)
                (imp (neg (member cut new))
                  (both (member new old) (neg (member old new))))))))) :=
  certificate_correct _

end PASoundness.PAtoCompactAdditionGenericMixedOrder

#print axioms PASoundness.PAtoCompactAdditionGenericMixedOrder.firstTest
#print axioms PASoundness.PAtoCompactAdditionGenericMixedOrder.secondTest
#print axioms PASoundness.PAtoCompactAdditionGenericMixedOrder.prefix_before_outside
#print axioms PASoundness.PAtoCompactAdditionGenericMixedOrder.prefix_before_outside_certificate
