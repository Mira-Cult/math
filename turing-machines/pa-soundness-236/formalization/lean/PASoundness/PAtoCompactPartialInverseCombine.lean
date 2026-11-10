import PASoundness.PAtoCompactPartialInverseCoverageAll

/-! Combine separately supplied quantified inverse-invariant directions into
the exact graph- and prefix-renamed successor invariant. No witness
construction, backward proof, alias elimination, or induction is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseCombine
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPartialInverseBase
open PASoundness.PAtoCompactPartialInverseCoverageAll
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Combine two consequences under the same guard by finite K proof data. -/
def guard_conjoin (Q A B : Nat) : KDerivation
    (imp (imp Q A) (imp (imp Q B) (imp Q (both A B)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [Q,imp Q B,imp Q A]
  have hq : Context Γ Q := Context.head _ _
  have ha : Context Γ (imp Q A) := .hypothesis (by simp [Γ])
  have hb : Context Γ (imp Q B) := .hypothesis (by simp [Γ])
  exact Context.conjunctionIntro (.mp hq ha) (.mp hq hb)

/-- Pointwise conjunction transported under one universal binder. -/
def all_guard_conjoin (v Q A B : Nat) : KDerivation
    (imp (allCode v (imp Q A)) (imp (allCode v (imp Q B))
      (allCode v (imp Q (both A B))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [allCode v (imp Q B),allCode v (imp Q A)]
  have ha : Context Γ (allCode v (imp Q A)) := .hypothesis (by simp [Γ])
  have hb : Context Γ (allCode v (imp Q B)) := Context.head _ _
  have hc : Context Γ (allCode v (imp (imp Q A) (imp (imp Q B) (imp Q (both A B))))) :=
    .closed (.generalize v (guard_conjoin Q A B))
  exact Context.allMP hb (Context.allMP ha hc)

/-- Pointwise conjunction transported through two nested universal binders. -/
def all2_guard_conjoin (v w Q A B : Nat) : KDerivation
    (imp (allCode v (allCode w (imp Q A))) (imp (allCode v (allCode w (imp Q B)))
      (allCode v (allCode w (imp Q (both A B)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [allCode v (allCode w (imp Q B)),allCode v (allCode w (imp Q A))]
  have ha : Context Γ (allCode v (allCode w (imp Q A))) := .hypothesis (by simp [Γ])
  have hb : Context Γ (allCode v (allCode w (imp Q B))) := Context.head _ _
  have hc : Context Γ (allCode v (imp (allCode w (imp Q A))
      (imp (allCode w (imp Q B)) (allCode w (imp Q (both A B)))))) :=
    .closed (.generalize v (all_guard_conjoin w Q A B))
  exact Context.allMP hb (Context.allMP ha hc)

private def conj (a b : Formula) : Formula := (a.imp b.not).not

def backwardCoverage : Formula := .all 2 (.all 3
  (.imp (conj (.member 0 2) (.member 1 3))
    (.imp (graphFormula 9 3 2) (conj (.member 10 2) (graphFormula 6 2 3)))))

def newPartial : Formula := replace 8 10 (replace 7 9 partialInverse)

/-- This is exactly the renamed original invariant, with backward direction
first and forward direction second. -/
theorem newPartial_code : newPartial.encode =
    allCode 2 (allCode 3 (imp (both (member 0 2) (member 1 3))
      (both (imp (graphFormula 9 3 2).encode
          (both (member 10 2) (graphFormula 6 2 3).encode))
        (imp (both (member 10 2) (graphFormula 6 2 3).encode)
          (graphFormula 9 3 2).encode)))) := by rfl

/-- The supplied witness premises yield the exact new invariant once the
backward/no-spurious coverage clause is supplied separately. -/
def combine_successor_invariant : KDerivation
    (imp suppliedPremises.encode (imp backwardCoverage.encode newPartial.encode)) := by
  let Q := both (member 0 2) (member 1 3)
  let T := both (member 10 2) (graphFormula 6 2 3).encode
  let G := (graphFormula 9 3 2).encode
  have hc := all2_guard_conjoin 2 3 Q (imp G T) (imp T G)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [backwardCoverage.encode,suppliedPremises.encode]
  have hb : Context Γ backwardCoverage.encode := Context.head _ _
  have hp : Context Γ suppliedPremises.encode := .hypothesis (by simp [Γ])
  have hf : Context Γ coverageFormula.encode := .mp hp (.closed coverage_all)
  have hnew : Context Γ (allCode 2 (allCode 3 (imp Q (both (imp G T) (imp T G))))) :=
    .mp hf (.mp hb (.closed hc))
  exact hnew

theorem combine_successor_invariant_certificate :
    theoremCode (certificate combine_successor_invariant) =
      imp suppliedPremises.encode (imp backwardCoverage.encode newPartial.encode) :=
  certificate_correct combine_successor_invariant

end PASoundness.PAtoCompactPartialInverseCombine

#print axioms PASoundness.PAtoCompactPartialInverseCombine.combine_successor_invariant
#print axioms PASoundness.PAtoCompactPartialInverseCombine.combine_successor_invariant_certificate
