import Sude.APGrowingPhase
import Sude.BTGrowingPhase

/-! Compose successive phases without reusing deleted physical endpoints. -/
namespace Sude
noncomputable section

/-- Successive traces concatenate at their exact remaining stock and radius. -/
theorem BTGrowingTrace.append {g Q : ℕ} {initial middle final : Finset ℕ}
    {radius middleRadius last : ℕ} {first second : List BTSelectedStage}
    (hfirst : BTGrowingTrace g Q initial radius middle middleRadius first)
    (hsecond : BTGrowingTrace g Q middle middleRadius final last second) :
    BTGrowingTrace g Q initial radius final last (first ++ second) := by
  induction hfirst with
  | nil => simpa using hsecond
  | cons unused radius stage mid midRadius tail hgap hdiv hbound hminimum hcard hmatch hsub hrest ih =>
    simpa using BTGrowingTrace.cons unused radius stage final last (tail ++ second)
      hgap hdiv hbound hminimum hcard hmatch hsub (ih hsecond)

/-- Concatenation proves physical separation across phase boundaries and
charges the exact total number of retained pair endpoints. -/
theorem BTGrowingTrace.append_accounting {g Q : ℕ} {initial middle final : Finset ℕ}
    {radius middleRadius last : ℕ} {first second : List BTSelectedStage}
    (hfirst : BTGrowingTrace g Q initial radius middle middleRadius first)
    (hsecond : BTGrowingTrace g Q middle middleRadius final last second) :
    final ⊆ initial ∧ final.card + 2 * Q * (first.length + second.length) = initial.card ∧
      (first ++ second).Pairwise (fun x y => Disjoint x.footprint y.footprint) := by
  have h := hfirst.append hsecond
  have hc := h.final_accounting
  refine ⟨hc.1, ?_, h.pairwise_disjoint⟩
  simpa using hc.2.1

end
end Sude
