import PASoundness.PAtoCompactGuardedModusPonens
import PASoundness.PAtoCompactGuardBaseTransport

/-! Finite K assembly of candidate-guard conjunctions across binder blocks. -/
namespace PASoundness.PAtoCompactGuardAssembly

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedEqualityReflexivity
open PASoundness.PAtoCompactGuardBaseTransport

/-- Given two lists of candidate guards, assemble a target list whose names
are covered by their union. The explicit bounds ensure the private blocks do
not bind the corresponding input name. Lists may repeat names or be reordered. -/
def guardList_combine (b c d : Nat) (xs ys zs : List Nat)
    (hx : ∀ x ∈ xs, x < b + 32) (hy : ∀ x ∈ ys, x < c + 32)
    (hz : ∀ x ∈ zs, x < d + 32)
    (cover : ∀ x ∈ zs, x ∈ xs ∨ x ∈ ys) :
    KDerivation (imp (guardList b xs).encode
      (imp (guardList c ys).encode (guardList d zs).encode)) := by
  induction zs with
  | nil =>
      apply Context.closeEmpty
      apply Context.deduction
      apply Context.deduction
      exact .closed (by simpa [guardList, Formula.encode] using KDerivation.truth)
  | cons z zs ih =>
      apply Context.closeEmpty
      apply Context.deduction
      apply Context.deduction
      let Γ := [(guardList c ys).encode, (guardList b xs).encode]
      have hgx : Context Γ (guardList b xs).encode := .hypothesis (by simp [Γ])
      have hgy : Context Γ (guardList c ys).encode := .hypothesis (by simp [Γ])
      have hzd : z < d + 32 := hz z (by simp)
      have hzz : Context Γ (domainAt d z).encode := by
        by_cases hzx : z ∈ xs
        · have hs : Context Γ (domainAt b z).encode :=
            .mp hgx (.closed (guardList_projection b z xs hzx))
          exact .mp hs (.closed (domainAt_transport b d z (hx z hzx) hzd))
        · have hzy : z ∈ ys := (cover z (by simp)).resolve_left hzx
          have hs : Context Γ (domainAt c z).encode :=
            .mp hgy (.closed (guardList_projection c z ys hzy))
          exact .mp hs (.closed (domainAt_transport c d z (hy z hzy) hzd))
      have ht : Context Γ (guardList d zs).encode := by
        apply Context.mp hgy
        apply Context.mp hgx
        exact .closed (ih (by intro x hm; exact hz x (by simp [hm]))
          (by intro x hm; exact cover x (by simp [hm])))
      have hboth := Context.conjunctionIntro hzz ht
      simpa [guardList, andF, Formula.encode, Formula.not, both, neg] using hboth

end PASoundness.PAtoCompactGuardAssembly

#print axioms PASoundness.PAtoCompactGuardAssembly.guardList_combine
