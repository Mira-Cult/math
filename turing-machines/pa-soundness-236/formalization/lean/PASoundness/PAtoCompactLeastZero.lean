import PASoundness.PAtoCompactLeastCounterexample

/-! Local zero case for an exposed least counterexample. The resulting code 1
is literally `member 0 0`; no global induction or PA-domain claim is made. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLeastZero
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactCounterexampleSet
open PASoundness.PAtoCompactLeastCounterexample

/-- Literal K zero case: the exact filter graph says the least member fails f,
whereas the supplied local base code says f holds at m when m satisfies
the displayed zero graph. The graph's test name z is fresh for m, and the
named predicate instance is capture-safe. No least-order argument is needed
beyond the least-member code's assertion that m belongs to the filter. -/
def least_zero_contradiction (x t m r z : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (htm : t ≠ m) (_hzm : z ≠ m)
    (htf : t ∉ f.binders) (hmf : m ∉ f.binders) :
    let c := filterPredicate x t (neg f.encode)
    let fm := (CompactNamed.replace t m f).encode
    KDerivation (imp (filterGraph x c t (neg f.encode)) (imp (leastMemberCode c m r)
      (imp (zeroCode m z) (imp (imp (zeroCode m z) fm) 1)))) := by
  dsimp only
  let c := filterPredicate x t (neg f.encode)
  let fm := (CompactNamed.replace t m f).encode
  let G := filterGraph x c t (neg f.encode)
  let L := leastMemberCode c m r
  let Z := zeroCode m z
  let B := imp Z fm
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [B,Z,L,G]
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hl : Context Γ L := .hypothesis (by simp [Γ])
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hm : Context Γ (member c m) := Context.conjunctionLeft hl
  have hgraph := Context.mp hg (.closed (counterexample_graph_at x t m f hxt htm htf hmf))
  have hnot : Context Γ (neg fm) := Context.conjunctionRight (.mp hm (Context.conjunctionLeft hgraph))
  exact .mp (.mp hz hb) hnot

theorem least_zero_certificate (x t m r z : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (htm : t ≠ m) (hzm : z ≠ m)
    (htf : t ∉ f.binders) (hmf : m ∉ f.binders) :
    let c := filterPredicate x t (neg f.encode)
    let fm := (CompactNamed.replace t m f).encode
    theoremCode (certificate (least_zero_contradiction x t m r z f hxt htm hzm htf hmf)) =
      imp (filterGraph x c t (neg f.encode)) (imp (leastMemberCode c m r)
        (imp (zeroCode m z) (imp (imp (zeroCode m z) fm) 1))) :=
  certificate_correct (least_zero_contradiction x t m r z f hxt htm hzm htf hmf)

/-- The base implication's standard-HF reading uses the same capture-safe
variable substitution as the K code. This semantic fact is independent of the
proof construction above. -/
theorem local_zero_base_standard (t m z : Nat) (f : CompactNamed.Formula)
    (htf : t ∉ f.binders) (hmf : m ∉ f.binders) (ρ : CompactMatrix.Environment) :
    (CompactMatrix.decode (imp (zeroCode m z) (CompactNamed.replace t m f).encode)).Realize ρ ↔
      ((CompactMatrix.decode (zeroCode m z)).Realize ρ →
        f.Realize (CompactMatrix.update ρ t (ρ m))) := by
  rw [CompactSemantics.realize_imp, CompactNamed.Formula.encode_realize,
    CompactNamed.replace_realize t m f htf hmf ρ]

end PASoundness.PAtoCompactLeastZero
