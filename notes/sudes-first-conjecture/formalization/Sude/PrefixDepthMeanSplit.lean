import Sude.PrefixDepthMeanIdentity
import Sude.PrefixSimultaneousSplit

/-! One global rounding depth, linked to its parent/child conditional means.
Recursive allocation and the construction of child means remain separate. -/
namespace Sude
noncomputable section

/-- Select left slots simultaneously, preserving each group's requested size
and bounding every line's total parent-to-child mean change by `10*C`.
The supplied child mean gap and per-slot weights satisfy the global DP2
budget; the result uses one selected set for every line. -/
theorem prefix_simultaneous_depth_mean_split {S G L : Type*}
    [DecidableEq S] [DecidableEq G] [DecidableEq L]
    (U : Finset S) (group : S → G) (m : G → ℕ) (lines : Finset L)
    (w : L → S → ℝ) (low high mean : G → ℝ) (C : ℝ)
    (hC : 0 ≤ C)
    (hm : ∀ g, m g ≤ (U.filter (fun s => group s = g)).card)
    (hw : ∀ l ∈ lines, ∀ s ∈ U, 0 ≤ w l s)
    (hweight : ∀ s ∈ U, (∑ l ∈ lines, w l s) ≤ 5)
    (hgap : ∀ s ∈ U, 0 ≤ high (group s) - low (group s) ∧
      high (group s) - low (group s) ≤ C)
    (hmean : ∀ s ∈ U, mean (group s) =
      prefixGroupInitial U group m s * low (group s) +
        (1 - prefixGroupInitial U group m s) * high (group s)) :
    ∃ T : Finset S, T ⊆ U ∧
      (∀ g ∈ U.image group, (T.filter (fun s => group s = g)).card = m g) ∧
      (∀ l ∈ lines,
        |(∑ s ∈ U, w l s * (if s ∈ T then low (group s) else high (group s))) -
          ∑ s ∈ U, w l s * mean (group s)| ≤ 10 * C) := by
  classical
  let ratio : G → ℝ := fun g => (m g : ℝ) /
    ((U.filter (fun s => group s = g)).card : ℝ)
  obtain ⟨T, hTU, hcard, hround⟩ := prefix_simultaneous_split U group m lines w
    (fun g => high g - low g) C hC hm hw hweight hgap
  refine ⟨T, hTU, hcard, ?_⟩
  intro l hl
  have hratio : ∀ s, ratio (group s) = prefixGroupInitial U group m s := by
    intro s
    rfl
  have hmean' : ∀ s ∈ U, mean (group s) = ratio (group s) * low (group s) +
      (1 - ratio (group s)) * high (group s) := by
    intro s hs
    simpa [hratio] using hmean s hs
  have hbound : |∑ s ∈ U, w l s * (high (group s) - low (group s)) *
      ((if (decide (s ∈ T) : Bool) then (1 : ℝ) else 0) - ratio (group s))| ≤ 10 * C := by
    simpa only [decide_eq_true_eq, hratio] using hround l hl
  simpa only [decide_eq_true_eq] using
    prefix_depth_mean_bound U group (fun s => decide (s ∈ T)) (w l) low high ratio mean
      (10 * C) hmean' hbound

end
end Sude
