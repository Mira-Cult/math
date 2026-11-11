import Sude.FWWidePhysicalGrid
import Sude.FlowRealization
import Sude.FWPoolBound

/-! Translate the exported bridge and wide coverage bounds into the natural
capacity used by the physical integral-flow interface. -/
namespace Sude
noncomputable section

/-- Bridge coverage through X and the wide-stage sum provide a radius of at
least X + 2KX. The resulting complete grid can center all even transfers of
magnitude at most 2*floor(KX/2). This is a numeric interface only: it does not
construct any network, flow, target demand, or line correction. -/
theorem fw_bridge_wide_uniform_integer_capacity {n R : ℕ}
    (wide : Fin (3 * (n / 450)) → ℕ)
    (hbridge : (poolMaximum n : ℝ) ≤ R)
    (hwide : (2 : ℝ) * (n / 450 : ℕ) * (poolMaximum n : ℝ) ≤ ∑ j, (wide j : ℝ)) :
    let X := poolMaximum n
    let K := n / 450
    let N := K * X
    let radius := R + ∑ j, wide j
    X + 2 * N ≤ radius ∧
    2 * N ≤ radius ∧
    2 * (N / 2) ≤ evenGridCenter radius := by
  dsimp only
  have hreal : ((poolMaximum n + 2 * ((n / 450) * poolMaximum n) : ℕ) : ℝ) ≤
      ((R + ∑ j, wide j : ℕ) : ℝ) := by
    push_cast
    linarith
  have hnat : poolMaximum n + 2 * ((n / 450) * poolMaximum n) ≤ R + ∑ j, wide j := by
    exact_mod_cast hreal
  have hcapacity : 2 * ((n / 450) * poolMaximum n) ≤ R + ∑ j, wide j := by omega
  exact ⟨hnat, hcapacity, evenGridCenter_pays_capacity _ _ hcapacity⟩

/-- In the first FW band, the same natural capacity is well above the
rounding threshold used by the FC2K integer-capacity lemma. This does not
assert that any target demand satisfies its separate box bound. -/
theorem fw_first_band_integer_capacity_large (lower : RSIndexLower) {n : ℕ}
    (hn : 19485 ≤ n) : 2000 ≤ (n / 450) * poolMaximum n := by
  have hk : 1 ≤ n / 450 := by omega
  have hx : 2000 ≤ poolMaximum n := by
    have h := fw_poolMaximum_gt_four_seed lower hn
    norm_num at h
    omega
  nlinarith

end
end Sude
